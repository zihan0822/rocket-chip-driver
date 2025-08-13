mod macros;

use patronus::expr::*;
use patronus::sim::*;
use patronus::system::*;
use std::cell::{OnceCell, RefCell};
use std::ffi::{c_char, c_uchar, c_uint};

pub const TRACED_STATES: &[&str] = &[];
thread_local! {
    static ROCKET_CHIP_SIMULATOR: OnceCell<RefCell<Driver>> = const { OnceCell::new() };
}
type SimBackend<'ctx> = Interpreter<'ctx>;

/// HACK: self-referential struct
/// Currently `patronus::Interpreter` borrows `Context` and `TransitionSystem`  
#[ouroboros::self_referencing]
struct Driver {
    ctx: Context,
    sys: TransitionSystem,
    #[borrows(ctx, sys)]
    #[covariant]
    sim: SimBackend<'this>,
    /// cached high and low baa value
    signal: (baa::BitVecValue, baa::BitVecValue),
    test_harness_module: MockTestHarnessModule,
    debug_module: DebugModule,
}

declare_module! {
    struct MockTestHarnessModule {
        #[in<1> = "clock", c_type=c_uchar]
        clk,
        #[in<1> = "reset", c_type = c_uchar]
        reset,
        #[in<32> = "io_exit", c_type = c_uint]
        exit,
        #[out = "io_success", c_type = c_uchar]
        io_success,
    }
}

declare_module! {
    #[in(bundle = debug_module_input_payload_t)]
    #[out(bundle = debug_module_output_payload_t)]
    struct DebugModule {
        #[in<7> = "io_debug_req_bits_addr", bundle_field = req_addr]
        in_req_addr,
        #[in<32> = "io_debug_req_bits_data", bundle_field = req_data]
        in_req_data,
        #[in<2> = "io_debug_req_bits_op", bundle_field = req_op]
        in_req_op,
        #[in<1> = "io_debug_resp_ready", bundle_field = resp_ready]
        in_resp_ready,
        #[in<1> = "io_debug_req_valid", bundle_field = req_valid]
        in_req_valid,
        #[out = "io_debug_resp_bits_resp", bundle_field = resp_resp]
        out_resp_resp,
        #[out = "io_debug_resp_bits_data", bundle_field = resp_data]
        out_resp_data,
        #[out = "io_debug_req_ready", bundle_field = req_ready]
        out_req_ready,
        #[out = "io_debug_resp_valid", bundle_field = resp_valid]
        out_resp_valid,
    }
}

#[repr(C)]
pub struct debug_module_input_payload_t {
    pub req_addr: c_uint,
    pub req_op: c_uint,
    pub req_data: c_uint,
    pub resp_ready: c_uint,
    pub req_valid: c_uchar,
}

#[repr(C)]
pub struct debug_module_output_payload_t {
    pub resp_resp: c_uint,
    pub resp_data: c_uint,
    pub req_ready: c_uchar,
    pub resp_valid: c_uchar,
}

fn with_driver_ref<F, R>(user: F) -> R
where
    for<'a> F: FnOnce(&'a Driver) -> R,
{
    ROCKET_CHIP_SIMULATOR.with(|stub| {
        user(
            &stub
                .get()
                .expect("`boostrap_driver` has never been called")
                .borrow(),
        )
    })
}

fn with_driver_mut<F, R>(user: F) -> R
where
    for<'a> F: FnOnce(&'a mut Driver) -> R,
{
    ROCKET_CHIP_SIMULATOR.with(|stub| {
        user(
            &mut stub
                .get()
                .expect("`boostrap_driver` has never been called")
                .borrow_mut(),
        )
    })
}

/// Returns whether bootstrap is successful.
/// This function should only be called once from cpp side.
///
/// # Safety
/// Caller should guarantee that `btor_path` is valid c_char pointer.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn bootstrap_driver(btor_path: *const c_char) -> bool {
    let (ctx, sys) = patronus::btor2::parse_file(unsafe {
        std::ffi::CStr::from_ptr(btor_path)
            .to_str()
            .expect("invalid input c string literal")
    })
    .expect("fail to load btor2 file");
    ROCKET_CHIP_SIMULATOR.with(|stub| stub.set(RefCell::new(Driver::init(ctx, sys))).is_ok())
}

/// Panics if `bootstrap_simulator` has never been called.
#[unsafe(no_mangle)]
pub extern "C" fn step_driver() {
    with_driver_mut(|driver| driver.step());
}

#[unsafe(no_mangle)]
pub extern "C" fn set_driver_debug_module_input(request: debug_module_input_payload_t) {
    with_driver_mut(|driver| {
        driver.with_mut(|fields| fields.debug_module.set_input(fields.sim, request))
    })
}

#[unsafe(no_mangle)]
pub extern "C" fn get_driver_debug_module_output() -> debug_module_output_payload_t {
    with_driver_ref(|driver| driver.with(|fields| fields.debug_module.get_output(fields.sim)))
}

#[unsafe(no_mangle)]
pub extern "C" fn set_driver_reset(signal: c_uchar) {
    with_driver_mut(|driver| {
        driver.with_mut(|fields| fields.test_harness_module.set_reset(fields.sim, signal))
    })
}

#[unsafe(no_mangle)]
pub extern "C" fn set_driver_exit(signal: c_uint) {
    with_driver_mut(|driver| {
        driver.with_mut(|fields| fields.test_harness_module.set_exit(fields.sim, signal))
    })
}

#[unsafe(no_mangle)]
pub extern "C" fn get_driver_io_success() -> c_uchar {
    with_driver_ref(|driver| {
        driver.with(|fields| fields.test_harness_module.get_io_success(fields.sim))
    })
}

impl Driver {
    fn init(ctx: Context, sys: TransitionSystem) -> Self {
        let test_harness_module = MockTestHarnessModule::from_context_and_system(&ctx, &sys);
        let debug_module = DebugModule::from_context_and_system(&ctx, &sys);
        DriverBuilder {
            sys,
            ctx,
            sim_builder: |ctx, sys| {
                let mut sim = SimBackend::new(ctx, sys);
                sim.init(InitKind::Zero);
                sim.register_traced_states(TRACED_STATES);
                sim
            },
            signal: (
                baa::BitVecValue::from_u64(1, 1),
                baa::BitVecValue::from_u64(0, 1),
            ),
            test_harness_module,
            debug_module,
        }
        .build()
    }

    fn step(&mut self) {
        self.with_mut(|driver| {
            let clk: ExprRef = driver.test_harness_module.clk;
            driver.sim.set(clk, (&driver.signal.0).into());
            driver.sim.step();
            driver.sim.set(clk, (&driver.signal.1).into());
        })
    }
}

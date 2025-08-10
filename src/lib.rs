#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]

mod macros;

use patronus::expr::*;
use patronus::sim::*;
use patronus::system::*;
use std::os::raw::c_char;
use std::sync::{Mutex, OnceLock};

const TRACED_STATES: &[&str] =
    &["ldut.tile_prci_domain.element_reset_domain_rockettile.core.mem_reg_wdata"];
static ROCKET_CHIP_SIMULATOR: OnceLock<Mutex<Driver>> = OnceLock::new();

type SimBackend<'ctx> = Interpreter<'ctx>;

#[allow(dead_code)]
mod ffi {
    include!(concat!(env!("OUT_DIR"), "/bindings.rs"));
}

/// HACK: self-referential struct
/// Currently `patronus::Interpreter` borrows `Context` and `TransitionSystem`  
#[ouroboros::self_referencing]
struct Driver {
    ctx: Context,
    sys: TransitionSystem,
    #[borrows(ctx, sys)]
    #[covariant]
    sim: SimBackend<'this>,
    clk: ExprRef,
    reset: ExprRef,
    /// cached high and low baa value
    signal: (baa::BitVecValue, baa::BitVecValue),
    debug_module: DebugModule,
}

debug_module! {
    struct DebugModule {
        #[in<7> = io_debug_req_bits_addr, c_struct_field = addr]
        in_req_bits_addr,
        #[in<32> = io_debug_req_bits_data, c_struct_field = data]
        in_req_bits_data,
        #[in<2> = io_debug_req_bits_op, c_struct_field = op]
        in_req_bits_op,
        #[out = io_debug_resp_bits_data, c_struct_field = data]
        out_resp_data,
        #[out = io_debug_resp_bits_resp, c_struct_field = resp]
        out_resp_bits,
    }
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
    ROCKET_CHIP_SIMULATOR
        .set(Mutex::new(Driver::init(ctx, sys)))
        .is_ok()
}

/// Panics if `bootstrap_simulator` has never been called.
#[unsafe(no_mangle)]
pub extern "C" fn step_driver() {
    rocket_chip_simulator!().step();
}

#[unsafe(no_mangle)]
pub extern "C" fn set_driver_debug_module_input(request: ffi::req) {
    rocket_chip_simulator!().with_mut(|driver| driver.debug_module.set_input(driver.sim, request))
}

#[unsafe(no_mangle)]
pub extern "C" fn get_driver_debug_module_output() -> ffi::resp {
    rocket_chip_simulator!().with(|driver| driver.debug_module.get_output(driver.sim))
}

impl Driver {
    fn init(ctx: Context, sys: TransitionSystem) -> Self {
        let clk = sys
            .lookup_input(&ctx, "clock")
            .expect("no clock input port found");
        let reset = sys
            .lookup_input(&ctx, "reset")
            .expect("no reset input port found");
        let debug_module = DebugModule::from_context_and_system(&ctx, &sys);
        DriverBuilder {
            clk,
            reset,
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
            debug_module,
        }
        .build()
    }

    fn step(&mut self) {
        self.with_mut(|driver| {
            let clk: ExprRef = *driver.clk;
            driver.sim.set(clk, (&driver.signal.0).into());
            driver.sim.step();
            driver.sim.set(clk, (&driver.signal.1).into());
        })
    }
}

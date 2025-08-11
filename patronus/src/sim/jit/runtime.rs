// Copyright 2025 Cornell University
// released under BSD 3-Clause License
// author: Zihan Li <zl2225@cornell.edu>
use crate::expr::*;
use cranelift::codegen::ir::{AbiParam, FuncRef, Function, types};
use cranelift::jit::{JITBuilder, JITModule};
use cranelift::module::{Linkage, Module};
use cranelift::prelude::*;
use rustc_hash::FxHashMap;
use trampoline::*;

pub(super) struct RuntimeLib {
    pub(super) clone_array: FuncRef,
    pub(super) clone_array_of_wide_bv: FuncRef,
    pub(super) dealloc_array: FuncRef,
    pub(super) dealloc_array_of_wide_bv: FuncRef,
    pub(super) alloc_array: FuncRef,
    pub(super) alloc_array_of_wide_bv: FuncRef,
    pub(super) copy_from_array: FuncRef,
    pub(super) copy_from_array_of_wide_bv: FuncRef,
    pub(super) clone_bv: FuncRef,
    pub(super) dealloc_bv: FuncRef,
    pub(super) copy_from_bv: FuncRef,
    pub(super) bv_ops: FxHashMap<&'static str, FuncRef>,
}
inventory::collect!(trampoline::BVOpRegistry);

const CLONE_ARRAY_SYM: &str = "__clone_array";
const CLONE_ARRAY_OF_WIDE_BV_SYM: &str = "__clone_array_of_wide_bv";
const DEALLOC_ARRAY_SYM: &str = "__dealloc_array";
const DEALLOC_ARRAY_OF_WIDE_BV_SYM: &str = "__dealloc_array_of_wide_bv";
const ALLOC_ARRAY_SYM: &str = "__alloc_array";
const ALLOC_ARRAY_OF_WIDE_BV_SYM: &str = "__alloc_array_of_wide_bv";
const COPY_FROM_ARRAY_SYM: &str = "__copy_from_array";
const COPY_FROM_ARRAY_OF_WIDE_BV_SYM: &str = "__copy_from_array_of_wide_bv";
const CLONE_BV_SYM: &str = "__clone_bv";
const DEALLOC_BV_SYM: &str = "__dealloc_bv";
const COPY_FROM_BV_SYM: &str = "__copy_from_bv";

pub(super) fn load_runtime_lib(builder: &mut JITBuilder) {
    builder.symbol(CLONE_ARRAY_SYM, __clone_array as *const u8);
    builder.symbol(
        CLONE_ARRAY_OF_WIDE_BV_SYM,
        __clone_array_of_wide_bv as *const u8,
    );
    builder.symbol(DEALLOC_ARRAY_SYM, __dealloc_array as *const u8);
    builder.symbol(
        DEALLOC_ARRAY_OF_WIDE_BV_SYM,
        __dealloc_array_of_wide_bv as *const u8,
    );
    builder.symbol(ALLOC_ARRAY_SYM, __alloc_array as *const u8);
    builder.symbol(
        ALLOC_ARRAY_OF_WIDE_BV_SYM,
        __alloc_array_of_wide_bv as *const u8,
    );
    builder.symbol(COPY_FROM_ARRAY_SYM, __copy_from_array as *const u8);
    builder.symbol(
        COPY_FROM_ARRAY_OF_WIDE_BV_SYM,
        __copy_from_array_of_wide_bv as *const u8,
    );
    builder.symbol(CLONE_BV_SYM, __clone_bv as *const u8);
    builder.symbol(DEALLOC_BV_SYM, __dealloc_bv as *const u8);
    builder.symbol(COPY_FROM_BV_SYM, __copy_from_bv as *const u8);
    for registered in inventory::iter::<trampoline::BVOpRegistry>() {
        builder.symbol(
            bv_operation_name_mangle(registered.sym),
            registered.raw_address(),
        );
    }
}

pub(super) fn import_runtime_lib_to_func_scope(
    module: &mut JITModule,
    func: &mut Function,
) -> RuntimeLib {
    let clone_array = import_extern_function(
        module,
        func,
        CLONE_ARRAY_SYM,
        [types::I64, types::I64],
        [types::I64],
    );
    let clone_array_of_wide_bv = import_extern_function(
        module,
        func,
        CLONE_ARRAY_OF_WIDE_BV_SYM,
        [types::I64, types::I64],
        [types::I64],
    );
    let dealloc_array = import_extern_function(
        module,
        func,
        DEALLOC_ARRAY_SYM,
        [types::I64, types::I64],
        [],
    );
    let dealloc_array_of_wide_bv = import_extern_function(
        module,
        func,
        DEALLOC_ARRAY_OF_WIDE_BV_SYM,
        [types::I64, types::I64],
        [],
    );
    let alloc_array = import_extern_function(
        module,
        func,
        ALLOC_ARRAY_SYM,
        [types::I64, types::I64],
        [types::I64],
    );
    let alloc_array_of_wide_bv = import_extern_function(
        module,
        func,
        ALLOC_ARRAY_OF_WIDE_BV_SYM,
        [types::I64, types::I64],
        [types::I64],
    );
    let copy_from_array = import_extern_function(
        module,
        func,
        COPY_FROM_ARRAY_SYM,
        [types::I64, types::I64, types::I64],
        [],
    );
    let copy_from_array_of_wide_bv = import_extern_function(
        module,
        func,
        COPY_FROM_ARRAY_OF_WIDE_BV_SYM,
        [types::I64, types::I64, types::I64],
        [],
    );
    let clone_bv = import_extern_function(module, func, CLONE_BV_SYM, [types::I64], [types::I64]);
    let dealloc_bv = import_extern_function(module, func, DEALLOC_BV_SYM, [types::I64], []);
    let copy_from_bv =
        import_extern_function(module, func, COPY_FROM_BV_SYM, [types::I64, types::I64], []);

    RuntimeLib {
        clone_array,
        clone_array_of_wide_bv,
        dealloc_array,
        dealloc_array_of_wide_bv,
        alloc_array,
        alloc_array_of_wide_bv,
        copy_from_array,
        copy_from_array_of_wide_bv,
        clone_bv,
        dealloc_bv,
        copy_from_bv,
        bv_ops: import_bv_runtime_to_func_scope(module, func),
    }
}

fn import_bv_runtime_to_func_scope(
    module: &mut JITModule,
    func: &mut Function,
) -> FxHashMap<&'static str, FuncRef> {
    let mut bv_runtime_lib = FxHashMap::default();
    for registered in inventory::iter::<BVOpRegistry>() {
        let num_params = match registered.kind {
            BVOpKind::Unary(_) | BVOpKind::Cmp(_) => 2,
            BVOpKind::Binary(_) | BVOpKind::Slice(_) => 3,
            BVOpKind::SliceWithOutputBuffer(_) | BVOpKind::Extend(_) | BVOpKind::Shift(_) => 4,
            BVOpKind::Concat(_) => 5,
        };
        let num_returns = match registered.kind {
            BVOpKind::Cmp(_) | BVOpKind::Slice(_) => 1,
            _ => 0,
        };
        let func_ref = import_extern_function(
            module,
            func,
            &bv_operation_name_mangle(registered.sym),
            std::iter::repeat_n(types::I64, num_params),
            std::iter::repeat_n(types::I64, num_returns),
        );
        bv_runtime_lib.insert(registered.sym, func_ref);
    }
    bv_runtime_lib
}

fn import_extern_function(
    module: &mut JITModule,
    func: &mut Function,
    name: &str,
    params: impl IntoIterator<Item = types::Type>,
    returns: impl IntoIterator<Item = types::Type>,
) -> FuncRef {
    let mut sig = module.make_signature();
    sig.params = Vec::from_iter(params.into_iter().map(AbiParam::new));
    sig.returns = Vec::from_iter(returns.into_iter().map(AbiParam::new));
    sig.call_conv = isa::CallConv::SystemV;

    let id = module
        .declare_function(name, Linkage::Import, &sig)
        .unwrap_or_else(|reason| panic!("fail to load {name}, due to {reason:#?}"));
    module.declare_func_in_func(id, func)
}

#[inline]
fn bv_operation_name_mangle(sym: &str) -> String {
    format!("__bv_{sym}")
}

pub(super) unsafe extern "C" fn __clone_array(src: *const i64, index_width: WidthInt) -> *mut i64 {
    unsafe {
        let len = 1 << index_width;
        let mut array = vec![0_i64; len];
        let src = std::slice::from_raw_parts(src, len);
        array.copy_from_slice(src);
        array.leak() as *mut [i64] as *mut i64
    }
}

pub(super) unsafe extern "C" fn __clone_array_of_wide_bv(
    src: *const *const baa::BitVecValue,
    index_width: WidthInt,
) -> *const *mut baa::BitVecValue {
    unsafe {
        let len = 1 << index_width;
        let mut array = Vec::with_capacity(len);
        let src = std::slice::from_raw_parts(src, len);
        array.extend(src.iter().map(|&bv| __clone_bv(bv)));
        array.leak() as *const [*mut baa::BitVecValue] as *const *mut baa::BitVecValue
    }
}

pub(super) unsafe extern "C" fn __copy_from_array(
    dst: *mut i64,
    src: *const i64,
    index_width: WidthInt,
) {
    unsafe {
        let len = 1 << index_width;
        let dst = std::slice::from_raw_parts_mut(dst, len);
        let src = std::slice::from_raw_parts(src, len);
        dst.copy_from_slice(src);
    }
}

pub(super) unsafe extern "C" fn __copy_from_array_of_wide_bv(
    dst: *const *mut baa::BitVecValue,
    src: *const *const baa::BitVecValue,
    index_width: WidthInt,
) {
    unsafe {
        let len = 1 << index_width;
        let dst = std::slice::from_raw_parts(dst, len);
        let src = std::slice::from_raw_parts(src, len);
        dst.iter()
            .zip(src.iter())
            .for_each(|(&dst_bv, &src_bv)| __copy_from_bv(dst_bv, src_bv));
    }
}

pub(super) extern "C" fn __alloc_array(index_width: WidthInt, default_data: i64) -> *mut i64 {
    let len = 1 << index_width;
    vec![default_data; len].leak() as *mut [i64] as *mut i64
}

pub(super) unsafe extern "C" fn __alloc_array_of_wide_bv(
    index_width: WidthInt,
    default_data: *const baa::BitVecValue,
) -> *const *mut baa::BitVecValue {
    let len = 1 << index_width;
    unsafe {
        Vec::from_iter(std::iter::repeat_with(|| __clone_bv(default_data)).take(len)).leak()
            as *const [*mut baa::BitVecValue] as *const *mut baa::BitVecValue
    }
}

pub(super) unsafe extern "C" fn __dealloc_array(src: *mut i64, index_width: WidthInt) {
    unsafe {
        let len = 1 << index_width;
        let ptr = std::ptr::slice_from_raw_parts_mut(src, len);
        let _ = Box::from_raw(ptr);
    }
}

pub(super) unsafe extern "C" fn __dealloc_array_of_wide_bv(
    src: *mut *mut baa::BitVecValue,
    index_width: WidthInt,
) {
    unsafe {
        let len = 1 << index_width;
        let array = std::slice::from_raw_parts_mut(src, len);
        for &bv in array.iter() {
            __dealloc_bv(bv);
        }
        let _ = Box::from_raw(array);
    }
}

pub(super) extern "C" fn __alloc_bv(width: WidthInt) -> *mut baa::BitVecValue {
    Box::leak(Box::new(baa::BitVecValue::zero(width)))
}

pub(super) unsafe extern "C" fn __clone_bv(src: *const baa::BitVecValue) -> *mut baa::BitVecValue {
    unsafe { Box::leak(Box::new((*src).clone())) }
}

pub(super) unsafe extern "C" fn __dealloc_bv(src: *mut baa::BitVecValue) {
    unsafe {
        let _ = Box::from_raw(src);
    }
}

pub(super) unsafe extern "C" fn __copy_from_bv(
    dst: *mut baa::BitVecValue,
    src: *const baa::BitVecValue,
) {
    unsafe {
        *dst = (*src).clone();
    }
}

mod trampoline {
    use crate::expr::*;
    use baa::{BitVecMutOps, BitVecOps, BitVecValue};

    pub(super) struct BVOpRegistry {
        pub(super) sym: &'static str,
        pub(super) kind: BVOpKind,
    }

    impl BVOpRegistry {
        pub(super) fn raw_address(&self) -> *const u8 {
            match self.kind {
                BVOpKind::Binary(address) => address as *const u8,
                BVOpKind::Unary(address) => address as *const u8,
                BVOpKind::Cmp(address) => address as *const u8,
                BVOpKind::Slice(address) => address as *const u8,
                BVOpKind::SliceWithOutputBuffer(address) => address as *const u8,
                BVOpKind::Concat(address) => address as *const u8,
                BVOpKind::Extend(address) => address as *const u8,
                BVOpKind::Shift(address) => address as *const u8,
            }
        }
    }
    type MaybeIndirect = i64;
    type ThinBV = i64;
    pub(super) enum BVOpKind {
        Binary(unsafe extern "C" fn(*mut BitVecValue, *const BitVecValue, *const BitVecValue)),
        Unary(unsafe extern "C" fn(*mut BitVecValue, *const BitVecValue)),
        Cmp(unsafe extern "C" fn(*const BitVecValue, *const BitVecValue) -> ThinBV),
        Slice(unsafe extern "C" fn(*const BitVecValue, WidthInt, WidthInt) -> ThinBV),
        SliceWithOutputBuffer(
            unsafe extern "C" fn(*mut BitVecValue, *const BitVecValue, WidthInt, WidthInt),
        ),
        Concat(
            unsafe extern "C" fn(
                *mut BitVecValue,
                MaybeIndirect,
                MaybeIndirect,
                WidthInt,
                WidthInt,
            ),
        ),
        Extend(unsafe extern "C" fn(*mut BitVecValue, MaybeIndirect, WidthInt, WidthInt)),
        Shift(unsafe extern "C" fn(*mut BitVecValue, *const BitVecValue, MaybeIndirect, WidthInt)),
    }

    macro_rules! baa_binary_op_shim {
        ($($op: ident),*) => {
            $(
                paste::paste! {
                    baa_binary_op_shim!(@internal [<__bv_ $op>], [<$op _in_place>], $op);
                }
            )*
        };
        (@internal $func: ident, $baa_delegation: ident, $sym: ident) => {
            inventory::submit!(BVOpRegistry {
                kind: BVOpKind::Binary($func),
                sym: stringify!($sym)
            });
            pub(super) unsafe extern "C" fn $func(
                dst: *mut BitVecValue,
                lhs: *const BitVecValue,
                rhs: *const BitVecValue,
            ) { unsafe {
                (*dst).$baa_delegation(&*lhs, &*rhs);
            }}
        }
    }

    macro_rules! baa_cmp_op_shim {
        ($($op: ident $([rename: $rename: ident])?),*) => {
            $(
                baa_cmp_op_shim!(@maybe_rename $op $(,$rename)?);
            )*
        };

        (@maybe_rename $op: ident, $rename: ident) => {
            paste::paste! {
                baa_cmp_op_shim!(@internal [<__bv_ $op>], $op, $rename);
            }
        };

        (@maybe_rename $op: ident) => {
            paste::paste! {
                baa_cmp_op_shim!(@internal [<__bv_ $op>], $op, $op);
            }
        };

        (@internal $func: ident, $baa_delegation: ident, $sym: ident) => {
            inventory::submit!(BVOpRegistry {
                kind: BVOpKind::Cmp($func),
                sym: stringify!($sym)
            });
            pub(super) unsafe extern "C" fn $func(
                lhs: *const BitVecValue,
                rhs: *const BitVecValue,
            ) -> ThinBV { unsafe {
                (&*lhs).$baa_delegation(&*rhs) as ThinBV
            }}
        };
    }

    macro_rules! baa_unary_op_shim {
        ($($op: ident),*) => {
            $(
                paste::paste! {
                    baa_unary_op_shim!(@internal [<__bv_ $op>], $op, $op);
                }
            )*
        };
        (@internal $func: ident, $baa_delegation: ident, $sym: ident) => {
            inventory::submit!(BVOpRegistry {
                kind: BVOpKind::Unary($func),
                sym: stringify!($sym)
            });
            pub(super) unsafe extern "C" fn $func(
                dst: *mut BitVecValue,
                value: *const BitVecValue,
            ) { unsafe {
                *dst = (&*value).$baa_delegation();
            }}
        };
    }

    macro_rules! baa_extend_op_shim {
        ($($op: ident),*) => {
            $(
                paste::paste! {
                    baa_extend_op_shim!(@internal [<__bv_ $op>], [<$op _in_place>], $op);
                }
            )*
        };
        (@internal $func: ident, $baa_delegation: ident, $sym: ident) => {
            inventory::submit!(BVOpRegistry {
                kind: BVOpKind::Extend($func),
                sym: stringify!($sym)
            });
            pub(super) unsafe extern "C" fn $func(
                dst: *mut BitVecValue,
                value: MaybeIndirect,
                original_width: WidthInt,
                by: WidthInt,
            ) { unsafe {
                let value = if original_width <= 64 {
                    &BitVecValue::from_i64(value, original_width)
                } else {
                    &*(value as *const BitVecValue)
                };
                (*dst).$baa_delegation(value, by);
            }}
        };
    }
    macro_rules! baa_shift_op_shim {
        ($($op: ident),*) => {
            $(
                paste::paste! {
                    baa_shift_op_shim!(@internal [<__bv_ $op>], [<$op _in_place>], $op);
                }
            )*
        };

        (@internal $func: ident, $baa_delegation: ident, $sym: ident) => {
            inventory::submit!(BVOpRegistry {
                kind: BVOpKind::Shift($func),
                sym: stringify!($sym)
            });
            pub(super) unsafe extern "C" fn $func(
                dst: *mut BitVecValue,
                value: *const BitVecValue,
                shift: MaybeIndirect,
                shift_data_width: WidthInt,
            ) { unsafe {
                let shift = if shift_data_width <= 64 {
                    &BitVecValue::from_i64(shift, shift_data_width)
                } else {
                    &*(shift as *const BitVecValue)
                };
                (*dst).$baa_delegation(&*value, shift);
            }}
        };
    }
    baa_binary_op_shim!(add, sub, mul, and, or, xor);
    baa_shift_op_shim!(shift_right, arithmetic_shift_right, shift_left);
    baa_extend_op_shim!(sign_extend, zero_extend);
    baa_unary_op_shim!(not, negate);
    baa_cmp_op_shim!(
        is_greater [rename: gt],
        is_greater_or_equal [rename: ge],
        is_greater_signed [rename: gt_signed],
        is_greater_or_equal_signed [rename: ge_signed],
        is_equal [rename: equal]
    );

    inventory::submit!(BVOpRegistry {
        kind: BVOpKind::Slice(__bv_slice),
        sym: "slice"
    });
    pub(super) unsafe extern "C" fn __bv_slice(
        value: *const BitVecValue,
        hi: WidthInt,
        lo: WidthInt,
    ) -> ThinBV {
        unsafe {
            let ret = (*value).slice(hi, lo);
            debug_assert!(ret.width() <= 64);
            ret.to_u64().unwrap() as ThinBV
        }
    }

    inventory::submit!(BVOpRegistry {
        kind: BVOpKind::SliceWithOutputBuffer(__bv_slice_with_output_buffer),
        sym: "slice_with_output_buffer"
    });
    pub(super) unsafe extern "C" fn __bv_slice_with_output_buffer(
        dst: *mut BitVecValue,
        value: *const BitVecValue,
        hi: WidthInt,
        lo: WidthInt,
    ) {
        unsafe {
            debug_assert!((hi - lo + 1) > 64);
            (*dst).slice_in_place(&*value, hi, lo);
        }
    }

    inventory::submit!(BVOpRegistry {
        kind: BVOpKind::Concat(__bv_concat),
        sym: "concat"
    });
    pub(super) unsafe extern "C" fn __bv_concat(
        dst: *mut BitVecValue,
        hi: MaybeIndirect,
        lo: MaybeIndirect,
        hi_width: WidthInt,
        lo_width: WidthInt,
    ) {
        unsafe {
            let hi = if hi_width <= 64 {
                &BitVecValue::from_u64(hi as u64, hi_width)
            } else {
                &*(hi as *const BitVecValue)
            };
            let lo = if lo_width <= 64 {
                &BitVecValue::from_u64(lo as u64, lo_width)
            } else {
                &*(lo as *const BitVecValue)
            };
            (*dst).concat_in_place(hi, lo);
        }
    }
}

// Copyright 2025 Cornell University
// released under BSD 3-Clause License
// author: Zihan Li <zl2225@cornell.edu>
use crate::expr::*;
use baa::Word;
use cranelift::codegen::ir::{types, AbiParam, FuncRef, Function};
use cranelift::jit::{JITBuilder, JITModule};
use cranelift::module::{Linkage, Module};
use cranelift::prelude::*;
use rustc_hash::FxHashMap;
use trampoline::*;

#[allow(dead_code)]
pub(super) struct RuntimeLib {
    pub(super) clone_array: FuncRef,
    pub(super) dealloc_array: FuncRef,
    pub(super) alloc_const_array: FuncRef,
    pub(super) copy_from_array: FuncRef,
    pub(super) clone_bv: FuncRef,
    pub(super) dealloc_bv: FuncRef,
    pub(super) copy_from_bv: FuncRef,
    pub(super) bv_ops: FxHashMap<&'static str, FuncRef>,
}
inventory::collect!(trampoline::BVOpRegistry);

const CLONE_ARRAY_SYM: &str = "__clone_array";
const DEALLOC_ARRAY_SYM: &str = "__dealloc_array";
const ALLOC_CONST_ARRAY_SYM: &str = "__alloc_const_array";
const COPY_FROM_ARRAY_SYM: &str = "__copy_from_array";
const CLONE_BV_SYM: &str = "__clone_bv";
const DEALLOC_BV_SYM: &str = "__dealloc_bv";
const COPY_FROM_BV_SYM: &str = "__copy_from_bv";

pub(super) fn load_runtime_lib(builder: &mut JITBuilder) {
    builder.symbol(CLONE_ARRAY_SYM, __clone_array as *const u8);
    builder.symbol(DEALLOC_ARRAY_SYM, __dealloc_array as *const u8);
    builder.symbol(ALLOC_CONST_ARRAY_SYM, __alloc_const_array as *const u8);
    builder.symbol(COPY_FROM_ARRAY_SYM, __copy_from_array as *const u8);
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
    let dealloc_array = import_extern_function(
        module,
        func,
        DEALLOC_ARRAY_SYM,
        [types::I64, types::I64],
        [],
    );
    let alloc_const_array = import_extern_function(
        module,
        func,
        ALLOC_CONST_ARRAY_SYM,
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
    let clone_bv = import_extern_function(module, func, CLONE_BV_SYM, [types::I64], [types::I64]);
    let dealloc_bv = import_extern_function(module, func, DEALLOC_BV_SYM, [types::I64], []);
    let copy_from_bv =
        import_extern_function(module, func, COPY_FROM_BV_SYM, [types::I64, types::I64], []);

    RuntimeLib {
        clone_array,
        dealloc_array,
        alloc_const_array,
        copy_from_array,
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
            std::iter::repeat(types::I64).take(num_params),
            std::iter::repeat(types::I64).take(num_returns),
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
        .unwrap_or_else(|reason| panic!("fail to load {}, due to {:#?}", name, reason));
    module.declare_func_in_func(id, func)
}

#[inline]
fn bv_operation_name_mangle(sym: &str) -> String {
    format!("__bv_{sym}")
}

pub(super) unsafe extern "C" fn __clone_array(src: *const i64, index_width: WidthInt) -> *mut i64 {
    let len = 1 << index_width;
    let mut array = vec![0_i64; len];
    let src = std::slice::from_raw_parts(src, len);
    array.copy_from_slice(src);
    array.leak() as *mut [i64] as *mut i64
}

pub(super) unsafe extern "C" fn __copy_from_array(
    dst: *mut i64,
    src: *const i64,
    index_width: WidthInt,
) {
    let len = 1 << index_width;
    let dst = std::slice::from_raw_parts_mut(dst, len);
    let src = std::slice::from_raw_parts(src, len);
    dst.copy_from_slice(src);
}

pub(super) extern "C" fn __alloc_const_array(index_width: WidthInt, default_data: i64) -> *mut i64 {
    let len = 1 << index_width;
    vec![default_data; len].leak() as *mut [i64] as *mut i64
}

pub(super) unsafe extern "C" fn __dealloc_array(src: *mut i64, index_width: WidthInt) {
    let len = 1 << index_width;
    let ptr = std::ptr::slice_from_raw_parts_mut(src, len);
    let _ = Box::from_raw(ptr);
}

pub(super) extern "C" fn __alloc_bv(width: WidthInt) -> *mut baa::BitVecValue {
    Box::leak(Box::new(baa::BitVecValue::zero(width)))
}

pub(super) unsafe extern "C" fn __clone_bv(src: *const baa::BitVecValue) -> *mut baa::BitVecValue {
    Box::leak(Box::new((*src).clone()))
}

pub(super) unsafe extern "C" fn __dealloc_bv(src: *mut baa::BitVecValue) {
    let _ = Box::from_raw(src);
}

pub(super) unsafe extern "C" fn __copy_from_bv(
    dst: *mut baa::BitVecValue,
    src: *const baa::BitVecValue,
) {
    *dst = (*src).clone();
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
    pub(super) enum BVOpKind {
        Binary(unsafe extern "C" fn(*mut BitVecValue, *const BitVecValue, *const BitVecValue)),
        Unary(unsafe extern "C" fn(*mut BitVecValue, *const BitVecValue)),
        Cmp(unsafe extern "C" fn(*const BitVecValue, *const BitVecValue) -> MaybeIndirect),
        Slice(unsafe extern "C" fn(*const BitVecValue, WidthInt, WidthInt) -> MaybeIndirect),
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
        ($func: ident, $baa_op_name: ident) => {
            inventory::submit!(BVOpRegistry {
                kind: BVOpKind::Binary($func),
                sym: stringify!($baa_op_name)
            });
            pub(super) unsafe extern "C" fn $func(
                dst: *mut BitVecValue,
                lhs: *const BitVecValue,
                rhs: *const BitVecValue,
            ) {
                *dst = (&*lhs).$baa_op_name(&*rhs);
            }
        };
    }

    macro_rules! baa_cmp_op_shim {
        ($func: ident, $baa_op_name: ident, rename: $rename: ident) => {
            inventory::submit!(BVOpRegistry {
                kind: BVOpKind::Cmp($func),
                sym: stringify!($rename)
            });
            pub(super) unsafe extern "C" fn $func(
                lhs: *const BitVecValue,
                rhs: *const BitVecValue,
            ) -> MaybeIndirect {
                (&*lhs).$baa_op_name(&*rhs) as MaybeIndirect
            }
        };
        ($func: ident, $baa_op_name: ident) => {
            baa_binary_op_shim!($func, $baa_op_name, rename: $baa_op_name);
        }
    }

    macro_rules! baa_unary_op_shim {
        ($func: ident, $baa_op_name: ident) => {
            inventory::submit!(BVOpRegistry {
                kind: BVOpKind::Unary($func),
                sym: stringify!($baa_op_name)
            });
            pub(super) unsafe extern "C" fn $func(
                dst: *mut BitVecValue,
                value: *const BitVecValue,
            ) {
                *dst = (&*value).$baa_op_name();
            }
        };
    }

    macro_rules! baa_extend_op_shim {
        ($func: ident, $baa_op_name: ident) => {
            inventory::submit!(BVOpRegistry {
                kind: BVOpKind::Extend($func),
                sym: stringify!($baa_op_name)
            });
            pub(super) unsafe extern "C" fn $func(
                dst: *mut BitVecValue,
                value: MaybeIndirect,
                original_width: WidthInt,
                by: WidthInt,
            ) {
                let value = if original_width <= 64 {
                    &BitVecValue::from_i64(value, original_width)
                } else {
                    &*(value as *const BitVecValue)
                };
                *dst = value.$baa_op_name(by);
            }
        };
    }
    macro_rules! baa_shift_op_shim {
        ($func: ident, $baa_op_name: ident) => {
            inventory::submit!(BVOpRegistry {
                kind: BVOpKind::Shift($func),
                sym: stringify!($baa_op_name)
            });
            pub(super) unsafe extern "C" fn $func(
                dst: *mut BitVecValue,
                value: *const BitVecValue,
                shift: MaybeIndirect,
                shift_data_width: WidthInt,
            ) {
                let shift = if shift_data_width <= 64 {
                    &BitVecValue::from_i64(shift, shift_data_width)
                } else {
                    &*(shift as *const BitVecValue)
                };
                *dst = (&*value).$baa_op_name(shift);
            }
        };
    }

    baa_binary_op_shim!(__bv_add, add);
    baa_binary_op_shim!(__bv_sub, sub);
    baa_binary_op_shim!(__bv_mul, mul);
    baa_binary_op_shim!(__bv_and, and);
    baa_binary_op_shim!(__bv_or, or);
    baa_binary_op_shim!(__bv_xor, xor);

    baa_shift_op_shim!(__bv_shift_right, shift_right);
    baa_shift_op_shim!(__bv_arithmetic_shift_right, arithmetic_shift_right);
    baa_shift_op_shim!(__bv_shift_left, shift_left);

    baa_unary_op_shim!(__bv_not, not);
    baa_unary_op_shim!(__bv_negate, negate);

    baa_cmp_op_shim!(__bv_gt, is_greater, rename: gt);
    baa_cmp_op_shim!(__bv_ge, is_greater_or_equal, rename: ge);
    baa_cmp_op_shim!(__bv_gt_signed, is_greater_signed, rename: gt_signed);
    baa_cmp_op_shim!(__bv_ge_signed, is_greater_or_equal_signed, rename: ge_signed);
    baa_cmp_op_shim!(__bv_equal, is_equal, rename: equal);

    baa_extend_op_shim!(__bv_sign_extend, sign_extend);
    baa_extend_op_shim!(__bv_zero_extend, zero_extend);

    inventory::submit!(BVOpRegistry {
        kind: BVOpKind::Slice(__bv_slice),
        sym: "slice"
    });
    pub(super) unsafe extern "C" fn __bv_slice(
        value: *const BitVecValue,
        hi: WidthInt,
        lo: WidthInt,
    ) -> MaybeIndirect {
        let ret = (*value).slice(hi, lo);
        debug_assert!(ret.width() <= 64);
        ret.to_u64().unwrap() as MaybeIndirect
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
        debug_assert!((hi - lo + 1) > 64);
        super::slice((*dst).words_mut(), (*value).words(), hi, lo);
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
        super::concat((*dst).words_mut(), hi.words(), lo.words(), lo_width);
    }
}

fn concat(dst: &mut [baa::Word], msb: &[baa::Word], lsb: &[baa::Word], lsb_width: WidthInt) {
    // copy lsb to dst
    assign(dst, lsb);

    let lsb_offset = lsb_width % baa::Word::BITS;
    if lsb_offset == 0 {
        // copy msb to dst
        for (d, m) in dst.iter_mut().skip(lsb.len()).zip(msb.iter()) {
            *d = *m;
        }
    } else {
        // copy a shifted version of the msb to dst
        let shift_right = baa::Word::BITS - lsb_offset;
        let m = mask(shift_right);
        let mut prev = dst[lsb.len() - 1]; // the msb of the lsb
        for (d, s) in dst
            .iter_mut()
            .skip(lsb.len() - 1)
            .zip(msb.iter().chain([0].iter()))
        {
            *d = prev | ((*s) & m) << lsb_offset;
            prev = (*s) >> shift_right;
        }
    }
}

#[inline]
pub fn mask(bits: WidthInt) -> baa::Word {
    if bits == baa::Word::BITS || bits == 0 {
        baa::Word::MAX
    } else {
        assert!(bits < baa::Word::BITS);
        ((1 as baa::Word) << bits) - 1
    }
}

#[inline]
fn assign(dst: &mut [baa::Word], source: &[baa::Word]) {
    for (d, s) in dst.iter_mut().zip(source.iter()) {
        *d = *s;
    }
}

fn slice(dst: &mut [Word], source: &[Word], hi: WidthInt, lo: WidthInt) {
    let lo_offset = lo % Word::BITS;
    let hi_word = (hi / Word::BITS) as usize;
    let lo_word = (lo / Word::BITS) as usize;
    let src = &source[lo_word..(hi_word + 1)];

    let shift_right = lo_offset;
    if shift_right == 0 {
        assign(dst, src);
    } else {
        // assign with a shift
        let shift_left = Word::BITS - shift_right;
        let m = mask(shift_right);
        let mut prev = src[0] >> shift_right;
        // We append a zero to the src iter in case src.len() == dst.len().
        // If src.len() == dst.len() + 1, then the 0 will just be ignored by `zip`.
        for (d, s) in dst.iter_mut().zip(src.iter().skip(1).chain([0].iter())) {
            *d = prev | ((*s) & m) << shift_left;
            prev = (*s) >> shift_right;
        }
    }
    // mask the result msb
    mask_msb(dst, hi - lo + 1);
}

#[inline]
fn mask_msb(dst: &mut [Word], width: WidthInt) {
    let m = mask(width % Word::BITS);
    *dst.last_mut().unwrap() &= m;
}

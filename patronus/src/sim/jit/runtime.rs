use crate::expr::*;
use cranelift::codegen::ir::{AbiParam, FuncRef, Function};
use cranelift::jit::{JITBuilder, JITModule};
use cranelift::module::{Linkage, Module};
use cranelift::prelude::*;

#[allow(dead_code)]
pub(super) struct RuntimeLib {
    pub(super) clone_array: FuncRef,
    pub(super) dealloc_array: FuncRef,
}

const CLONE_ARRAY_SYM: &str = "__clone_array";
const DEALLOC_ARRAY_SYM: &str = "__dealloc_array";

pub(super) fn load_runtime_lib(builder: &mut JITBuilder) {
    builder.symbol(CLONE_ARRAY_SYM, __clone_array as *const u8);
    builder.symbol(DEALLOC_ARRAY_SYM, __dealloc_array as *const u8);
}

pub(super) fn import_runtime_lib_to_func_scope(
    module: &mut JITModule,
    func: &mut Function,
) -> RuntimeLib {
    let mut sig = module.make_signature();
    sig.params = vec![AbiParam::new(types::I64), AbiParam::new(types::I64)];
    sig.returns = vec![AbiParam::new(types::I64)];
    sig.call_conv = isa::CallConv::SystemV;
    let clone_array_id = module
        .declare_function(CLONE_ARRAY_SYM, Linkage::Import, &sig)
        .unwrap_or_else(|_| panic!("fail to load {CLONE_ARRAY_SYM}"));
    let clone_array = module.declare_func_in_func(clone_array_id, func);

    let mut sig = module.make_signature();
    sig.params = vec![AbiParam::new(types::I64), AbiParam::new(types::I64)];
    sig.returns = vec![];
    sig.call_conv = isa::CallConv::SystemV;

    let dealloc_array_id = module
        .declare_function(DEALLOC_ARRAY_SYM, Linkage::Import, &sig)
        .unwrap_or_else(|_| panic!("fail to load {DEALLOC_ARRAY_SYM}"));
    let dealloc_array = module.declare_func_in_func(dealloc_array_id, func);

    RuntimeLib {
        clone_array,
        dealloc_array,
    }
}

pub(super) unsafe extern "C" fn __clone_array(src: *const i64, index_width: WidthInt) -> *mut i64 {
    let len = 1 << index_width;
    let mut array = vec![0_i64; len].into_boxed_slice();
    let src = std::slice::from_raw_parts(src, len);
    array.copy_from_slice(src);
    Box::leak(array) as *mut [i64] as *mut i64
}

pub(super) unsafe extern "C" fn __dealloc_array(src: *mut i64, index_width: WidthInt) {
    let len = 1 << index_width;
    let ptr = std::ptr::slice_from_raw_parts_mut(src, len);
    let _ = Box::from_raw(ptr);
}

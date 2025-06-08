use crate::expr::*;
use cranelift::codegen::ir::{AbiParam, FuncRef, Function};
use cranelift::jit::{JITBuilder, JITModule};
use cranelift::module::{Linkage, Module};
use cranelift::prelude::*;

#[allow(dead_code)]
pub(super) struct RuntimeLib {
    pub(super) clone_array: FuncRef,
    pub(super) dealloc_array: FuncRef,
    pub(super) alloc_const_array: FuncRef,
}

const CLONE_ARRAY_SYM: &str = "__clone_array";
const DEALLOC_ARRAY_SYM: &str = "__dealloc_array";
const ALLOC_CONST_ARRAY_SYM: &str = "__alloc_const_array";

macro_rules! import_lib {
    ($module: ident, $func: ident, $name: ident, [$($param_ty: expr),*], [$($ret_ty: expr),*]) => {
        {
            let mut sig = $module.make_signature();
            sig.params = vec![$(AbiParam::new($param_ty)),*];
            sig.returns = vec![$(AbiParam::new($ret_ty)),*];
            sig.call_conv = isa::CallConv::SystemV;

            let id = $module
                .declare_function($name, Linkage::Import, &sig)
                .unwrap_or_else(|_| panic!("fail to load {}", $name));
            $module.declare_func_in_func(id, $func)
        }
    }
}

pub(super) fn load_runtime_lib(builder: &mut JITBuilder) {
    builder.symbol(CLONE_ARRAY_SYM, __clone_array as *const u8);
    builder.symbol(DEALLOC_ARRAY_SYM, __dealloc_array as *const u8);
    builder.symbol(ALLOC_CONST_ARRAY_SYM, __alloc_const_array as *const u8);
}

pub(super) fn import_runtime_lib_to_func_scope(
    module: &mut JITModule,
    func: &mut Function,
) -> RuntimeLib {
    let clone_array = import_lib!(
        module,
        func,
        CLONE_ARRAY_SYM,
        [types::I64, types::I64],
        [types::I64]
    );
    let dealloc_array = import_lib!(
        module,
        func,
        DEALLOC_ARRAY_SYM,
        [types::I64, types::I64],
        []
    );
    let alloc_const_array = import_lib!(
        module,
        func,
        ALLOC_CONST_ARRAY_SYM,
        [types::I64, types::I64],
        [types::I64]
    );

    RuntimeLib {
        clone_array,
        dealloc_array,
        alloc_const_array,
    }
}

pub(super) unsafe extern "C" fn __clone_array(src: *const i64, index_width: WidthInt) -> *mut i64 {
    let len = 1 << index_width;
    let mut array = vec![0_i64; len].into_boxed_slice();
    let src = std::slice::from_raw_parts(src, len);
    array.copy_from_slice(src);
    Box::leak(array) as *mut [i64] as *mut i64
}

pub(super) unsafe extern "C" fn __alloc_const_array(
    index_width: WidthInt,
    default_data: i64,
) -> *const i64 {
    let len = 1 << index_width;
    let array = vec![default_data; len].into_boxed_slice();
    Box::leak(array) as *const [i64] as *const i64
}

pub(super) unsafe extern "C" fn __dealloc_array(src: *mut i64, index_width: WidthInt) {
    let len = 1 << index_width;
    let ptr = std::ptr::slice_from_raw_parts_mut(src, len);
    let _ = Box::from_raw(ptr);
}

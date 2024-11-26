// Copyright 2023 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@berkeley.edu>
mod context;
mod eval;
mod foreach;
mod meta;
mod nodes;
mod parse;
mod serialize;
mod simplify;
mod transform;
pub mod traversal;
mod types;

pub use context::{Builder, Context, ExprRef, StringRef};
pub use eval::{eval_array_expr, eval_bv_expr, eval_expr, SymbolValueStore};
pub use foreach::ForEachChild;
pub use meta::{
    get_fixed_point, DenseExprMetaData, DenseExprSet, ExprMap, ExprSet, SparseExprMap,
    SparseExprSet,
};
pub use nodes::{ArrayType, BVLitValue, Expr, Type, WidthInt};
pub use parse::parse_expr;
pub use serialize::SerializableIrNode;
pub(crate) use serialize::{serialize_expr, serialize_expr_ref};
pub(crate) use simplify::simplify;
pub use simplify::simplify_single_expression;
pub(crate) use transform::{do_transform_expr, ExprTransformMode};
pub use types::{TypeCheck, TypeCheckError};

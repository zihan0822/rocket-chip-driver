// Copyright 2023 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@berkeley.edu>
mod context;
mod eval;
mod expr;
mod foreach;
mod serialize;
mod transform;
pub mod traversal;
mod types;

pub use context::{Context, ExprRef, StringRef};
pub use eval::{eval_array_expr, eval_bv_expr, eval_expr, SymbolValueStore};
pub use expr::{ArrayType, Expr, Type};
pub use foreach::ForEachChild;
pub use serialize::SerializableIrNode;
pub(crate) use serialize::{serialize_expr, serialize_expr_ref};
pub(crate) use transform::{do_transform_expr, simplify};
pub use transform::{simplify_single_expression, ExprMetaData};
pub use types::{TypeCheck, TypeCheckError};

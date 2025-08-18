use crate::expr::traversal::{self, TraversalCmd};
use crate::expr::*;
use dot_writer::{Attributes, DotWriter, Node, NodeId};
use rustc_hash::FxHashMap;
use std::fmt::Write;

pub struct ComputeGraphDrawerBuilder<'ctx> {
    ctx: &'ctx Context,
    /// Whether to display data type
    node_data_type: bool,
    /// Whether to display symbol name if there is one
    symbol_name: bool,
    /// Maxinum depth the root expression node will expanded
    /// Graph will be early-terminated if `max_depth` is reached
    max_depth: Option<usize>,
}

impl<'ctx> ComputeGraphDrawerBuilder<'ctx> {
    pub fn new(ctx: &'ctx Context) -> Self {
        Self {
            ctx,
            node_data_type: true,
            symbol_name: false,
            max_depth: None,
        }
    }

    pub fn with_data_type(mut self) -> Self {
        self.node_data_type = true;
        self
    }

    pub fn with_symbol_name(mut self) -> Self {
        self.symbol_name = true;
        self
    }

    pub fn max_depth(mut self, depth: usize) -> Self {
        self.max_depth = Some(depth);
        self
    }

    pub fn finish(self) -> ComputeGraphDrawer<'ctx> {
        ComputeGraphDrawer {
            ctx: self.ctx,
            node_data_type: self.node_data_type,
            symbol_name: self.symbol_name,
            max_depth: self.max_depth,
        }
    }
}

pub struct ComputeGraphDrawer<'ctx> {
    ctx: &'ctx Context,
    node_data_type: bool,
    symbol_name: bool,
    max_depth: Option<usize>,
}

impl ComputeGraphDrawer<'_> {
    pub fn dot_graph(&mut self, expr: ExprRef) -> String {
        DotWriter::write_string(|writer| {
            writer.set_pretty_print(false);
            let mut graph = writer.digraph();

            let root_id = self.decorate_expr_node(graph.node_auto(), expr);
            let mut frontier = FxHashMap::from_iter([(expr, (1, root_id))]);

            traversal::top_down(self.ctx, expr, |ctx, current_expr| {
                let (current_depth, current_id) = frontier[&current_expr].clone();
                let early_return = self
                    .max_depth
                    .is_some_and(|max_depth| current_depth >= max_depth);
                let mut child_node_ids = vec![];

                ctx[current_expr].for_each_child(|&child_expr| {
                    let id = if early_return {
                        self.decorate_dummy_node(graph.node_auto())
                    } else {
                        self.decorate_expr_node(graph.node_auto(), child_expr)
                    };
                    frontier.insert(child_expr, (current_depth + 1, id.clone()));
                    child_node_ids.push(id);
                });

                for child_id in &child_node_ids {
                    graph.edge(&current_id, child_id);
                }
                if early_return {
                    TraversalCmd::Stop
                } else {
                    TraversalCmd::Continue
                }
            });
        })
    }

    fn decorate_dummy_node(&self, mut node: Node) -> NodeId {
        node.set_label("...");
        node.id()
    }

    fn decorate_expr_node(&self, mut node: Node, expr: ExprRef) -> NodeId {
        let mut display = String::new();

        if self.symbol_name {
            if let Some(name) = self.ctx.get_symbol_name(expr) {
                writeln!(&mut display, "`{name}`").unwrap();
            }
        }

        writeln!(&mut display, "{}", self.ctx[expr].expr_kind_literal()).unwrap();
        if self.node_data_type {
            write!(
                &mut display,
                "`{}`",
                expr.get_type(self.ctx).type_kind_literal()
            )
            .unwrap();
        }
        node.set_label(&display);
        node.id()
    }
}

impl Type {
    pub fn type_kind_literal(&self) -> String {
        match self {
            Type::BV(width) => format!("bitvec [{width}]"),
            Type::Array(ArrayType {
                index_width,
                data_width,
            }) => format!("array [{index_width}][{data_width}]"),
        }
    }
}

impl Expr {
    pub fn expr_kind_literal(&self) -> &'static str {
        match self {
            Expr::BVSymbol { .. } => "sym",
            Expr::BVLiteral { .. } => "const",
            Expr::BVZeroExt { .. } => "zero ext",
            Expr::BVSignExt { .. } => "sign ext",
            Expr::BVSlice { .. } => "slice",
            Expr::BVNot(..) => "not",
            Expr::BVNegate(..) => "negate",
            Expr::BVEqual(..) => "equal",
            Expr::BVImplies(..) => "implies",
            Expr::BVGreater(..) => "gt",
            Expr::BVGreaterSigned(..) => "signed gt",
            Expr::BVGreaterEqual(..) => "ge",
            Expr::BVGreaterEqualSigned(..) => "signed ge",
            Expr::BVConcat(..) => "concat",
            Expr::BVAnd(..) => "and",
            Expr::BVOr(..) => "or",
            Expr::BVXor(..) => "xor",
            Expr::BVShiftLeft(..) => "sl",
            Expr::BVArithmeticShiftRight(..) => "arith sr",
            Expr::BVShiftRight(..) => "sr",
            Expr::BVAdd(..) => "add",
            Expr::BVSub(..) => "sub",
            Expr::BVMul(..) => "mul",
            Expr::BVUnsignedDiv(..) => "div",
            Expr::BVSignedDiv(..) => "signed div",
            Expr::BVSignedMod(..) => "signed mod",
            Expr::BVUnsignedRem(..) => "rem",
            Expr::BVSignedRem(..) => "signed rem",
            Expr::BVIte { .. } => "ite",
            Expr::BVArrayRead { .. } => "read",
            Expr::ArrayStore { .. } => "store",
            Expr::ArraySymbol { .. } => "array sym",
            Expr::ArrayConstant { .. } => "array const",
            Expr::ArrayEqual { .. } => "array equal",
            Expr::ArrayIte { .. } => "array ite",
        }
    }
}

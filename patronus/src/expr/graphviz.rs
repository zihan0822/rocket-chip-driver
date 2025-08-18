use crate::expr::*;
use dot_writer::{Attributes, DotWriter, Node, NodeId};
use std::fmt::Write;

pub struct ComputeGraphDrawerBuilder<'ctx> {
    ctx: &'ctx Context,
    /// Whether to display data type
    node_data_type: bool,
    /// Whether to display symbol name if there is one
    symbol_name: bool,
}

impl<'ctx> ComputeGraphDrawerBuilder<'ctx> {
    pub fn new(ctx: &'ctx Context) -> Self {
        Self {
            ctx,
            node_data_type: true,
            symbol_name: false,
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

    pub fn finish(self) -> ComputeGraphDrawer<'ctx> {
        ComputeGraphDrawer {
            ctx: self.ctx,
            node_data_type: self.node_data_type,
            symbol_name: self.symbol_name,
        }
    }
}

pub struct ComputeGraphDrawer<'ctx> {
    ctx: &'ctx Context,
    node_data_type: bool,
    symbol_name: bool,
}

impl ComputeGraphDrawer<'_> {
    pub fn dot_graph(&mut self, expr: ExprRef) -> String {
        DotWriter::write_string(|writer| {
            writer.set_pretty_print(false);
            let mut graph = writer.digraph();

            crate::expr::traversal::bottom_up(self.ctx, expr, |_, current, children| {
                let current_id = self.decorate_expr_node(graph.node_auto(), current);
                for child_id in children.iter() {
                    graph.edge(child_id, &current_id);
                }
                current_id
            });
        })
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

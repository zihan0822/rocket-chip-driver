// Copyright 2024 Cornell University
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@cornell.edu>

use patronus::expr::*;

/// test a simplification
fn ts(inp: &str, expect: &str) {
    let mut ctx = Context::default();
    let input = parse_expr(&mut ctx, inp);
    let expected = parse_expr(&mut ctx, expect);
    let simplified = simplify_single_expression(&mut ctx, input);
    assert_eq!(
        simplified,
        expected,
        "simplify({}) = {}\nExpected: {}",
        input.serialize_to_str(&ctx),
        simplified.serialize_to_str(&ctx),
        expected.serialize_to_str(&ctx)
    );
}

#[test]
fn test_simplify_and() {
    ts("true", "true");
    ts("false", "false");
    ts("and(true, false)", "false");
    ts("and(true, true)", "true");
    ts("and(a : bv<1>, true)", "a : bv<1>");
    ts("and(a : bv<3>, 3'b111)", "a : bv<3>");
    ts("and(a : bv<1>, false)", "false");
    ts("and(a : bv<3>, 3'b000)", "3'b000");
    ts("and(a : bv<1>, not(a))", "false");
    ts("and(not(a : bv<1>), a)", "false");
}

#[test]
fn test_simplify_or() {
    ts("or(false, true)", "true");
    ts("or(false, false)", "false");
    ts("or(a : bv<1>, true)", "true");
    ts("or(a : bv<3>, 3'b111)", "3'b111");
    ts("or(a : bv<1>, false)", "a : bv<1>");
    ts("or(a : bv<3>, 3'b000)", "a : bv<3>");
    ts("or(a : bv<1>, not(a))", "true");
    ts("or(not(a : bv<1>), a)", "true");
}

#[test]
fn test_simplify_xor() {
    ts("xor(false, true)", "true");
    ts("xor(false, false)", "false");
    ts("xor(true, true)", "false");
    ts("xor(a : bv<1>, a)", "false");
    ts("xor(a : bv<1>, not(a))", "true");
    ts("xor(not(a : bv<1>), a)", "true");
}

#[test]
fn test_simplify_not() {
    ts("not(false)", "true");
    ts("not(true)", "false");
    ts("not(a: bv<1>)", "not(a: bv<1>)");
    ts("not(not(a: bv<1>))", "a: bv<1>");
    ts("not(not(not(a: bv<1>)))", "not(a: bv<1>)");
    ts("not(not(not(not(a: bv<1>))))", "a: bv<1>");
}

#[test]
fn test_simplify_zext() {
    ts("zext(false, 1)", "2'b00");
    ts("zext(true, 1)", "2'b01");
    ts("zext(true, 0)", "true");
}

#[test]
fn test_simplify_sext() {
    ts("sext(false, 1)", "2'b00");
    ts("sext(true, 1)", "2'b11");
    ts("sext(true, 0)", "true");
}

#[test]
fn test_simplify_ite() {
    // outcome is always the same
    ts("ite(c : bv<1>, a: bv<10>, a)", "a : bv<10>");

    // constant condition
    ts("ite(true, a: bv<10>, b: bv<10>)", "a : bv<10>");
    ts("ite(false, a: bv<10>, b: bv<10>)", "b : bv<10>");

    // both true and false value are boolean constants
    ts("ite(c : bv<1>, true, false)", "c : bv<1>");
    ts("ite(c : bv<1>, true, true)", "true");
    ts("ite(c : bv<1>, false, true)", "not(c : bv<1>)");
    ts("ite(c : bv<1>, false, false)", "false");
}

#[test]
fn test_simplify_slice() {
    // slice a constant
    ts("3'b110[2]", "true");
    ts("3'b110[1]", "true");
    ts("3'b110[0]", "false");
    ts("4'b1100[3:2]", "2'b11");
    ts("4'b1100[2:1]", "2'b10");
    ts("4'b1100[1:0]", "2'b00");

    // nested slices
    ts("a : bv<10>[6:3][1]", "a : bv<10>[4]");
}

#[test]
fn test_simplify_shift_left() {
    // shift a constant by a constant
    ts("shift_left(3'b011, 3'd0)", "3'b011");
    ts("shift_left(3'b011, 3'd1)", "3'b110");
    ts("shift_left(3'b011, 3'd2)", "3'b100");
    ts("shift_left(3'b011, 3'd3)", "3'b000");

    // shift by a constant
    ts("shift_left(a : bv<3>, 3'd0)", "a : bv<3>");
    ts(
        "shift_left(a : bv<3>, 3'd1)",
        "concat(a : bv<3>[1:0], 1'b0)",
    );
    ts("shift_left(a : bv<3>, 3'd2)", "concat(a : bv<3>[0], 2'b00)");
    ts("shift_left(a : bv<3>, 3'd3)", "3'b000");
}

#[test]
fn test_simplify_shift_right() {
    // shift a constant by a constant
    ts("shift_right(3'b101, 3'd0)", "3'b101");
    ts("shift_right(3'b101, 3'd1)", "3'b010");
    ts("shift_right(3'b101, 3'd2)", "3'b001");
    ts("shift_right(3'b101, 3'd3)", "3'b000");

    // shift by a constant
    ts("shift_right(a : bv<3>, 3'd0)", "a : bv<3>");
    ts("shift_right(a : bv<3>, 3'd1)", "zext(a : bv<3>[2:1], 1)");
    ts("shift_right(a : bv<3>, 3'd2)", "zext(a : bv<3>[2], 2)");
    ts("shift_right(a : bv<3>, 3'd3)", "3'b000");
}

#[test]
fn test_simplify_arithmetic_shift_right() {
    // shift a constant by a constant
    ts("arithmetic_shift_right(3'b101, 3'd0)", "3'b101");
    ts("arithmetic_shift_right(3'b101, 3'd1)", "3'b110");
    ts("arithmetic_shift_right(3'b101, 3'd2)", "3'b111");
    ts("arithmetic_shift_right(3'b101, 3'd3)", "3'b111");

    // shift by a constant
    ts("arithmetic_shift_right(a : bv<3>, 3'd0)", "a : bv<3>");
    ts(
        "arithmetic_shift_right(a : bv<3>, 3'd1)",
        "sext(a : bv<3>[2:1], 1)",
    );
    ts(
        "arithmetic_shift_right(a : bv<3>, 3'd2)",
        "sext(a : bv<3>[2], 2)",
    );
    ts(
        "arithmetic_shift_right(a : bv<3>, 3'd3)",
        "sext(a : bv<3>[2], 2)",
    );
}

#[test]
fn test_simplify_add() {
    // add constants
    ts("add(true, true)", "false");
    ts("add(true, false)", "true");
    ts("add(false, false)", "false");
    ts("add(15'd123, 15'd321)", "15'd444");

    // add zero
    ts("add(a : bv<4>, 4'd0)", "a : bv<4>");
    ts("add(4'd0, a : bv<4>)", "a : bv<4>");
}

#[test]
fn test_simplify_mul() {
    // multiply constants
    ts("mul(true, true)", "true");
    ts("mul(true, false)", "false");
    ts("mul(false, false)", "false");
    ts("mul(17'd123, 17'd321)", "17'd39483");

    // multiply with zero
    ts("mul(a : bv<4>, 4'd0)", "4'd0");
    ts("mul(4'd0, a : bv<4>)", "4'd0");

    // multiply with one
    ts("mul(a : bv<4>, 4'd1)", "a : bv<4>");
    ts("mul(4'd1, a : bv<4>)", "a : bv<4>");

    // multiply with power of two (this includes a simplification of the left shift)
    ts("mul(a : bv<4>, 4'd2)", "concat(a : bv<4>[2:0],  1'b0)");
    ts("mul(a : bv<4>, 4'd4)", "concat(a : bv<4>[1:0], 2'b00)");
    ts("mul(a : bv<4>, 4'd8)", "concat(a : bv<4>[0],  3'b000)");
}

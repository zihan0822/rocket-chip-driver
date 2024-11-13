module miter(A, B, M, N);
    input [15:0] A, B;
    input [3:0] M, N;
    wire [62:0] O_spec, O_impl;

    spec s(.A(A), .B(B), .M(M), .N(N), .O(O_spec));
    impl i(.A(A), .B(B), .M(M), .N(N), .O(O_spec));
    assert property (O_spec == O_impl);
endmodule
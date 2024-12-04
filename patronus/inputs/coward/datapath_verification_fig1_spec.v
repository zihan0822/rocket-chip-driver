module spec(A, B, M, N, O) ;
    input [15:0] A, B;
    input [3:0] M, N;
    output [62:0] O;
    wire [30:0] D;
    wire [30:0] E;
    assign D = A << M;
    assign E = B << N ;
    assign O = D * E;
endmodule


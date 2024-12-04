module impl(A, B, M, N, O);
    input [15:0] A, B;
    input [3:0] M, N;
    output [62:0] O;
    wire [31:0] C;
    wire [4:0] P;

    assign C = A * B;
    assign P = M + N;
    assign O = C << P;
endmodule

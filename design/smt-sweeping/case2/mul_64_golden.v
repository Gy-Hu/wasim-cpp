module alu_golden(input [63:0] a64, input [63:0] b64, output [127:0] out128);

assign out128 = a64 * b64;

endmodule

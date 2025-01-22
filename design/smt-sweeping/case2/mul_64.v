module alu(input [63:0] a, input [63:0] b, input [3:0] control, output [127:0] out);

wire [63:0] internal_a;
wire [63:0] internal_b;

assign internal_a = control[1:0] == 2'b00 ? a : 
                    control[1:0] == 2'b01 ? {1'b0, a[62:0]} :
                    control[1:0] == 2'b10 ? {a[63:1], 1'b0} : a & b;

assign internal_b = b;

assign out = control[3:2] == 2'b00 ? internal_a + internal_b :
             control[3:2] == 2'b01 ? internal_a - internal_b :
             control[3:2] == 2'b10 ? internal_a * internal_b : internal_a / internal_b;

// when control is 4'b1000, alu is same as alu_golden

endmodule
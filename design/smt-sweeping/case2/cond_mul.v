// module alu(input [4:0] a, input [4:0] b, input [3:0] control, output [9:0] out);

// wire [4:0] internal_a;
// wire [4:0] internal_b;

// assign internal_a = control[1:0] == 2'b00 ? a : 
// 		    control[1:0] == 2'b01 ? {1'b0, a[3:0]} :
// 		    control[1:0] == 2'b10 ? {a[4:1], 1'b0} : a & b;

// assign internal_b = b;

// assign out = control[3:2] == 2'b00 ? internal_a + internal_b :
// 	     control[3:2] == 2'b01 ? internal_a - internal_b :
// 	     control[3:2] == 2'b10 ? internal_a * internal_b : internal_a / internal_b;

// // when control is 4'b1000, alu is same as alu_golden

// endmodule


// module alu_golden(input [4:0] a, input [4:0] b, output [9:0] out);

// assign out = a * b;

// endmodule

// module alu_miter(input [4:0] a, input [4:0] b, input [3:0] control, output result, output condition);

// wire [9:0] alu_out;
// wire [9:0] alu_golden_out;
// wire [9:0] miter_out;

// alu alu(.a(a), .b(b), .control(control), .out(alu_out));
// alu_golden alu_golden(.a(a), .b(b), .out(alu_golden_out));

// assign miter_out = alu_out ^ alu_golden_out;
// assign result = |miter_out;
// assign condition = (control == 4'b1000) ? 1'b1 : 1'b0;

// endmodule



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


module alu_golden(input [63:0] a, input [63:0] b, output [127:0] out);

assign out = a * b;

endmodule

module alu_miter(input [63:0] a, input [63:0] b, input [3:0] control, output result, output condition);

wire [127:0] alu_out;
wire [127:0] alu_golden_out;
wire [127:0] miter_out;

alu alu(.a(a), .b(b), .control(control), .out(alu_out));
alu_golden alu_golden(.a(a), .b(b), .out(alu_golden_out));

assign miter_out = alu_out ^ alu_golden_out;
assign result = |miter_out;
assign condition = (control == 4'b1000) ? 1'b1 : 1'b0;

endmodule


// module alu(input [127:0] a, input [127:0] b, input [3:0] control, output [255:0] out);

// wire [127:0] internal_a;
// wire [127:0] internal_b;

// assign internal_a = control[1:0] == 2'b00 ? a : 
//                     control[1:0] == 2'b01 ? {1'b0, a[126:0]} :
//                     control[1:0] == 2'b10 ? {a[127:1], 1'b0} : a & b;

// assign internal_b = b;

// assign out = control[3:2] == 2'b00 ? internal_a + internal_b :
//              control[3:2] == 2'b01 ? internal_a - internal_b :
//              control[3:2] == 2'b10 ? internal_a * internal_b : internal_a / internal_b;

// // when control is 4'b1000, alu is same as alu_golden

// endmodule


// module alu_golden(input [127:0] a, input [127:0] b, output [255:0] out);

// assign out = a * b;

// endmodule

// module alu_miter(input [127:0] a, input [127:0] b, input [3:0] control, output result, output condition);

// wire [255:0] alu_out;
// wire [255:0] alu_golden_out;
// wire [255:0] miter_out;

// alu alu(.a(a), .b(b), .control(control), .out(alu_out));
// alu_golden alu_golden(.a(a), .b(b), .out(alu_golden_out));

// assign miter_out = alu_out ^ alu_golden_out;
// assign result = |miter_out;
// assign condition = (control == 4'b1000) ? 1'b1 : 1'b0;

// endmodule
module AES_Encrypt_tb;
reg [127:0] in1;
wire [127:0] out1;
reg [127:0] key1;
AES_Encrypt a(in1,key1,out1);

initial begin
$monitor("in128= %h, key128= %h ,out128= %h",in1,key1,out1);
in1=128'h3243f6a8885a308d313198a2e0370734;
key1=128'h2b7e151628aed2a6abf7158809cf4f3c;
#10;
end

endmodule


module AES_Encrypt#(parameter N=128,parameter Nr=1,parameter Nk=4)(in,key,out);
input [127:0] in;
input [127:0] key;
output [127:0] out;

wire [(128*(Nr+1))-1 :0] fullkeys;
wire [127:0] states [Nr+1:0];
wire [127:0] afterSubBytes;
wire [127:0] afterShiftRows;

keyExpansion #(Nk,Nr) ke (key,fullkeys);

addRoundKey addrk1 (in,states[0],fullkeys[((128*(Nr+1))-1)-:128]);

subBytes sb(states[0],afterSubBytes);
shiftRows sr(afterSubBytes,afterShiftRows);
addRoundKey addrk2(afterShiftRows,states[1],fullkeys[127:0]);
assign out=states[1];

endmodule
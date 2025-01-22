module encryptRound(in,key,out);
input [127:0] in;
output [127:0] out;
input [127:0] key;
wire [127:0] afterSubBytes;
wire [127:0] afterShiftRows;


subBytes s(in,afterSubBytes);
shiftRows r(afterSubBytes,afterShiftRows);
addRoundKey b(afterShiftRows,out,key);
		
endmodule
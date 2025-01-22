`timescale 1ns / 1ps
`include "rounndlast.v"
`include "KeyGeneration.v"
`include "subbytes.v"
`include "shiftrow.v"
`include "sbox.v"

`include "rounds.v"
`include "mixcolumn.v"

module aescipher(clk,datain,key,dataout);

    input clk;
    input [127:0] datain;
    input [127:0] key;
    output[127:0] dataout;
    
    wire [127:0] r0_out;
    
   
	 
	assign r0_out = datain^key;
	 
    rounds r1(.clk(clk),.rc(4'b0000),.data(r0_out),.keyin(key),.keyout(keyout1),.rndout(r1_out));
    rounds r2(.clk(clk),.rc(4'b0001),.data(r1_out),.keyin(keyout1),.keyout(keyout2),.rndout(r2_out));
    rounds r3(.clk(clk),.rc(4'b0010),.data(r2_out),.keyin(keyout2),.keyout(keyout3),.rndout(r3_out));
    rounds r4(.clk(clk),.rc(4'b0011),.data(r3_out),.keyin(keyout3),.keyout(keyout4),.rndout(r4_out));
    rounds r5(.clk(clk),.rc(4'b0100),.data(r4_out),.keyin(keyout4),.keyout(keyout5),.rndout(r5_out));
    rounds r6(.clk(clk),.rc(4'b0101),.data(r5_out),.keyin(keyout5),.keyout(keyout6),.rndout(r6_out));
    rounds r7(.clk(clk),.rc(4'b0110),.data(r6_out),.keyin(keyout6),.keyout(keyout7),.rndout(r7_out));
    rounds r8(.clk(clk),.rc(4'b0111),.data(r7_out),.keyin(keyout7),.keyout(keyout8),.rndout(r8_out));
    rounds r9(.clk(clk),.rc(4'b1000),.data(r8_out),.keyin(keyout8),.keyout(keyout9),.rndout(r9_out));
    // rounndlast r10(.clk(clk),.rc(4'b0000),.rin(r0_out),.keylastin(key),.fout(dataout));
    rounndlast r10(.clk(clk), .rc(4'b1001),.rin(r9_out),.keylastin(keyout9),.fout(dataout));
    
endmodule

`include "AES-128-Bit-Verilog/AES_TOP.v"
`include "AES-Verilog/AES_Encrypt.v"

module aes_miter(
    input [127:0] datain,
    input [127:0] key,
    output miter_out
);

    wire [127:0] out1;
    wire [127:0] out2;

    AES_Encrypt #(
        .N(128),
        .Nr(10),
        .Nk(4)
    ) dut1 (
        .in(datain),
        .key(key),
        .out(out1)
    );

    AES_TOP dut2 (
        .finalout(out2),
        .datain(datain),
        .key(key)
    );

    assign miter_out = out1 != out2; 

endmodule
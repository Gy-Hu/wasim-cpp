`timescale 1ns / 1ps

module aescipher_tb;

    // Inputs
    reg clk;
    reg [127:0] datain;
    reg [127:0] key;

    // Outputs
    wire [127:0] dataout;

    // Instantiate the Unit Under Test (UUT)
    aescipher uut (
        .clk(clk),
        .datain(datain),
        .key(key),
        .dataout(dataout)
    );

    // Clock generation
    always begin
        #5 clk = ~clk; // 10ns clock period (100 MHz)
    end

    // Test procedure
    initial begin
        // Initialize Inputs
        clk = 0;
        datain = 128'h00000000000000000000000000000000;
        key = 128'h00000000000000000000000000000000;

        // Wait for a few clock cycles
        #10;

        // Test case 1: First key and input text
        datain = 128'h6bc1bee22e409f96e93d7e117393172a; // Example plaintext
        key = 128'h2b7e151628aed2a6abf7158809cf4f3c;   // Example key

        // Wait for the encryption to complete
        #100;
        $display("Key: %h | Input: %h | Output: %h",key, datain, dataout);

        // End simulation
        $stop;
    end

endmodule

`timescale 1ns / 1ps

module KeyGeneration_tb;

    // Inputs
    reg [3:0] rc;
    reg [127:0] key;

    // Outputs
    wire [127:0] keyout;

    // Instantiate the Unit Under Test (UUT)
    KeyGeneration uut (
        .rc(rc),
        .key(key),
        .keyout(keyout)
    );

    // Test procedure
    initial begin
        // Initialize Inputs
        rc = 4'b0000;
        key = 128'h000102030405060708090a0b0c0d0e0f;  // Example key

        // Wait for the first round key to be generated
        #10;
        $display("Time: %0t | Round: %h | Input Key: %h | Output Key: %h", $time, rc, key, keyout);

        // End simulation
        $stop;
    end

endmodule

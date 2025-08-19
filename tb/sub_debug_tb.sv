// Debug testbench for SUB operation
`timescale 1ns / 1ps

import alu_pkg::*;

module sub_debug_tb;
    logic CLK, RST_n, EN;
    logic [15:0] A, B, Result;
    logic [3:0] OpCode;
    logic Cin;
    logic Zero, Carry, Overflow, Negative;
    
    ALU_16bit dut (.*);
    
    initial begin
        CLK = 0;
        forever #5 CLK = ~CLK;
    end
    
    initial begin
        $dumpfile("sub_debug.vcd");
        $dumpvars(0, sub_debug_tb);
        
        // Reset
        RST_n = 0;
        EN = 0;
        A = 0;
        B = 0;
        OpCode = 0;
        Cin = 0;
        #20 RST_n = 1;
        
        // Test 1: 0x5678 - 0x1234 (cin=1, means no borrow)
        // Expected: 0x4444
        #10;
        A = 16'h5678;
        B = 16'h1234;
        OpCode = OP_SUB;
        Cin = 1;
        EN = 1;
        #20;
        $display("Test 1: %h - %h (cin=%b) = %h (expected 4444)", A, B, Cin, Result);
        $display("  Carry=%b (expected 1)", Carry);
        
        // Test 2: 0x0000 - 0x0001 (cin=1, means no borrow)
        // Expected: 0xFFFF with borrow
        #10;
        A = 16'h0000;
        B = 16'h0001;
        OpCode = OP_SUB;
        Cin = 1;
        EN = 1;
        #20;
        $display("Test 2: %h - %h (cin=%b) = %h (expected FFFF)", A, B, Cin, Result);
        $display("  Carry=%b (expected 0)", Carry);
        
        // Let's trace internal signals
        #10;
        A = 16'h5678;
        B = 16'h1234;
        OpCode = OP_SUB;
        Cin = 1;
        EN = 1;
        #20;
        $display("\nDetailed trace for 5678 - 1234:");
        $display("  A        = %h", dut.u_arithmetic_unit.a);
        $display("  B        = %h", dut.u_arithmetic_unit.b);
        $display("  B_mux    = %h", dut.u_arithmetic_unit.b_mux);
        $display("  Cin_mux  = %b", dut.u_arithmetic_unit.cin_mux);
        $display("  Sum      = %h", dut.u_arithmetic_unit.sum);
        $display("  Cout     = %b", dut.u_arithmetic_unit.cout);
        
        #100 $finish;
    end
endmodule
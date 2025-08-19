// =============================================================================
// File: alu_16bit_tb.sv
// Description: Comprehensive testbench for 16-bit ALU verification
// Author: RTL Generator
// Date: 2025-01-19
// Version: 1.0
// =============================================================================

`timescale 1ns / 1ps

import alu_pkg::*;

module alu_16bit_tb;

    // =========================================================================
    // Signal Declarations
    // =========================================================================
    
    // Clock and Reset
    logic        clk;
    logic        rst_n;
    logic        en;
    
    // DUT Inputs
    logic [15:0] a;
    logic [15:0] b;
    logic [3:0]  opcode;
    logic        cin;
    
    // DUT Outputs
    logic [15:0] result;
    logic        zero;
    logic        carry;
    logic        overflow;
    logic        negative;
    
    // Test control
    integer      test_count;
    integer      error_count;
    integer      i, j;
    
    // Expected results
    logic [15:0] expected_result;
    logic        expected_zero;
    logic        expected_carry;
    logic        expected_overflow;
    logic        expected_negative;
    
    // =========================================================================
    // DUT Instantiation
    // =========================================================================
    
    ALU_16bit dut (
        .CLK      (clk),
        .RST_n    (rst_n),
        .EN       (en),
        .A        (a),
        .B        (b),
        .OpCode   (opcode),
        .Cin      (cin),
        .Result   (result),
        .Zero     (zero),
        .Carry    (carry),
        .Overflow (overflow),
        .Negative (negative)
    );
    
    // =========================================================================
    // Clock Generation
    // =========================================================================
    
    initial begin
        clk = 0;
        forever #5 clk = ~clk;  // 100MHz clock (10ns period)
    end
    
    // =========================================================================
    // Test Tasks
    // =========================================================================
    
    task reset_dut();
        begin
            rst_n = 0;
            en = 0;
            a = 16'h0000;
            b = 16'h0000;
            opcode = 4'h0;
            cin = 0;
            repeat(3) @(posedge clk);
            rst_n = 1;
            @(posedge clk);
        end
    endtask
    
    task apply_test(
        input [15:0] test_a,
        input [15:0] test_b,
        input [3:0]  test_op,
        input        test_cin
    );
        begin
            a = test_a;
            b = test_b;
            opcode = test_op;
            cin = test_cin;
            en = 1;
            @(posedge clk);
            @(posedge clk);  // Wait for result
            test_count++;
        end
    endtask
    
    task check_result();
        begin
            if (result !== expected_result) begin
                $display("[ERROR] Result mismatch: Expected %h, Got %h", 
                         expected_result, result);
                error_count++;
            end
            if (zero !== expected_zero) begin
                $display("[ERROR] Zero flag mismatch: Expected %b, Got %b", 
                         expected_zero, zero);
                error_count++;
            end
            if (carry !== expected_carry) begin
                $display("[ERROR] Carry flag mismatch: Expected %b, Got %b", 
                         expected_carry, carry);
                error_count++;
            end
            if (overflow !== expected_overflow) begin
                $display("[ERROR] Overflow flag mismatch: Expected %b, Got %b", 
                         expected_overflow, overflow);
                error_count++;
            end
            if (negative !== expected_negative) begin
                $display("[ERROR] Negative flag mismatch: Expected %b, Got %b", 
                         expected_negative, negative);
                error_count++;
            end
        end
    endtask
    
    // =========================================================================
    // Test Scenarios
    // =========================================================================
    
    task test_add_operation();
        begin
            $display("\n=== Testing ADD Operation ===");
            
            // Test 1: Simple addition
            apply_test(16'h1234, 16'h5678, OP_ADD, 0);
            expected_result = 16'h68AC;
            expected_zero = 0;
            expected_carry = 0;
            expected_overflow = 0;
            expected_negative = 0;
            check_result();
            
            // Test 2: Addition with carry out
            apply_test(16'hFFFF, 16'h0001, OP_ADD, 0);
            expected_result = 16'h0000;
            expected_zero = 1;
            expected_carry = 1;
            expected_overflow = 0;
            expected_negative = 0;
            check_result();
            
            // Test 3: Signed overflow (positive + positive = negative)
            apply_test(16'h7FFF, 16'h0001, OP_ADD, 0);
            expected_result = 16'h8000;
            expected_zero = 0;
            expected_carry = 0;
            expected_overflow = 1;
            expected_negative = 1;
            check_result();
        end
    endtask
    
    task test_sub_operation();
        begin
            $display("\n=== Testing SUB Operation ===");
            
            // Test 1: Simple subtraction
            apply_test(16'h5678, 16'h1234, OP_SUB, 1);
            expected_result = 16'h4444;
            expected_zero = 0;
            expected_carry = 1;
            expected_overflow = 0;
            expected_negative = 0;
            check_result();
            
            // Test 2: Subtraction with borrow
            apply_test(16'h0000, 16'h0001, OP_SUB, 1);
            expected_result = 16'hFFFF;
            expected_zero = 0;
            expected_carry = 0;
            expected_overflow = 0;
            expected_negative = 1;
            check_result();
        end
    endtask
    
    task test_logic_operations();
        begin
            $display("\n=== Testing Logic Operations ===");
            
            // AND operation
            apply_test(16'hF0F0, 16'h00FF, OP_AND, 0);
            expected_result = 16'h00F0;
            expected_zero = 0;
            expected_carry = 0;
            expected_overflow = 0;
            expected_negative = 0;
            check_result();
            
            // OR operation
            apply_test(16'hF0F0, 16'h00FF, OP_OR, 0);
            expected_result = 16'hF0FF;
            expected_zero = 0;
            expected_carry = 0;
            expected_overflow = 0;
            expected_negative = 1;
            check_result();
            
            // XOR operation
            apply_test(16'hF0F0, 16'h00FF, OP_XOR, 0);
            expected_result = 16'hF00F;
            expected_zero = 0;
            expected_carry = 0;
            expected_overflow = 0;
            expected_negative = 1;
            check_result();
            
            // NOT operation
            apply_test(16'h5555, 16'h0000, OP_NOT, 0);
            expected_result = 16'hAAAA;
            expected_zero = 0;
            expected_carry = 0;
            expected_overflow = 0;
            expected_negative = 1;
            check_result();
        end
    endtask
    
    task test_shift_operations();
        begin
            $display("\n=== Testing Shift Operations ===");
            
            // LSL operation
            apply_test(16'h5555, 16'h0000, OP_LSL, 0);
            expected_result = 16'hAAAA;
            expected_zero = 0;
            expected_carry = 0;
            expected_overflow = 0;
            expected_negative = 1;
            check_result();
            
            // LSR operation
            apply_test(16'hAAAA, 16'h0000, OP_LSR, 0);
            expected_result = 16'h5555;
            expected_zero = 0;
            expected_carry = 0;
            expected_overflow = 0;
            expected_negative = 0;
            check_result();
            
            // ASR operation (sign extend)
            apply_test(16'h8000, 16'h0000, OP_ASR, 0);
            expected_result = 16'hC000;
            expected_zero = 0;
            expected_carry = 0;
            expected_overflow = 0;
            expected_negative = 1;
            check_result();
            
            // ROL operation
            apply_test(16'h8001, 16'h0000, OP_ROL, 0);
            expected_result = 16'h0003;
            expected_zero = 0;
            expected_carry = 1;
            expected_overflow = 0;
            expected_negative = 0;
            check_result();
            
            // ROR operation
            apply_test(16'h0001, 16'h0000, OP_ROR, 0);
            expected_result = 16'h8000;
            expected_zero = 0;
            expected_carry = 1;
            expected_overflow = 0;
            expected_negative = 1;
            check_result();
        end
    endtask
    
    task test_special_operations();
        begin
            $display("\n=== Testing Special Operations ===");
            
            // INC operation
            apply_test(16'hFFFF, 16'h0000, OP_INC, 0);
            expected_result = 16'h0000;
            expected_zero = 1;
            expected_carry = 1;
            expected_overflow = 0;
            expected_negative = 0;
            check_result();
            
            // DEC operation
            apply_test(16'h0000, 16'h0000, OP_DEC, 0);
            expected_result = 16'hFFFF;
            expected_zero = 0;
            expected_carry = 0;
            expected_overflow = 0;
            expected_negative = 1;
            check_result();
            
            // PASS operation
            apply_test(16'hABCD, 16'h1234, OP_PASS, 0);
            expected_result = 16'hABCD;
            expected_zero = 0;
            expected_carry = 0;
            expected_overflow = 0;
            expected_negative = 1;
            check_result();
        end
    endtask
    
    task run_random_tests();
        begin
            $display("\n=== Running Random Tests ===");
            
            for (i = 0; i < 1000; i++) begin
                logic [15:0] rand_a, rand_b;
                logic [3:0]  rand_op;
                logic        rand_cin;
                
                rand_a = $random();
                rand_b = $random();
                rand_op = $random() & 4'hF;
                rand_cin = $random() & 1'b1;
                
                apply_test(rand_a, rand_b, rand_op, rand_cin);
                
                // Basic check - just ensure no X or Z
                if (^result === 1'bx || ^result === 1'bz) begin
                    $display("[ERROR] Unknown value in result for op %h", rand_op);
                    error_count++;
                end
            end
            
            $display("Completed %0d random tests", 1000);
        end
    endtask
    
    // =========================================================================
    // Main Test Sequence
    // =========================================================================
    
    initial begin
        // Initialize
        test_count = 0;
        error_count = 0;
        
        $display("\n====================================");
        $display("    16-bit ALU Testbench Started    ");
        $display("====================================\n");
        
        // Reset DUT
        reset_dut();
        
        // Run test suites
        test_add_operation();
        test_sub_operation();
        test_logic_operations();
        test_shift_operations();
        test_special_operations();
        run_random_tests();
        
        // Report results
        $display("\n====================================");
        $display("         Test Summary Report         ");
        $display("====================================");
        $display("Total Tests:  %0d", test_count);
        $display("Errors:       %0d", error_count);
        if (error_count == 0) begin
            $display("Status:       PASSED");
        end else begin
            $display("Status:       FAILED");
        end
        $display("====================================\n");
        
        // End simulation
        #100;
        $finish;
    end
    
    // =========================================================================
    // Waveform Dumping
    // =========================================================================
    
    initial begin
        $dumpfile("alu_16bit.vcd");
        $dumpvars(0, alu_16bit_tb);
    end
    
endmodule : alu_16bit_tb
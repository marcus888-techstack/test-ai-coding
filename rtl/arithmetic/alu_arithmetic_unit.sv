// =============================================================================
// File: alu_arithmetic_unit.sv
// Description: Arithmetic unit with optimized Carry Skip Adder
// Author: RTL Generator
// Date: 2025-01-19
// Version: 1.0
// Architecture: Mixed Carry Skip + Carry Select for critical path optimization
// =============================================================================

`timescale 1ns / 1ps

import alu_pkg::*;

module alu_arithmetic_unit (
    input  logic [15:0] a,             // Operand A
    input  logic [15:0] b,             // Operand B
    input  logic        cin,           // Carry input
    input  logic [2:0]  ctrl,          // Control signals
    output logic [15:0] result,        // Arithmetic result
    output logic        cout,          // Carry output
    output logic        overflow       // Overflow flag
);

    // Internal signals
    logic [15:0] b_mux;                // B operand after mux
    logic        cin_mux;              // Carry input after mux
    logic [15:0] sum;                  // Adder sum output
    logic        carry_out;            // Final carry out
    
    // Carry chain signals for optimized adder
    logic [3:0]  group_carry;          // Carry out from each 4-bit group
    logic [3:0]  group_propagate;      // Group propagate signals
    logic [3:0]  group_generate;       // Group generate signals
    
    // =========================================================================
    // Input Operand Selection
    // =========================================================================
    always_comb begin
        // Default values
        b_mux = b;
        cin_mux = cin;
        
        case (ctrl)
            ARITH_ADD: begin
                b_mux = b;
                cin_mux = cin;
            end
            ARITH_SUB, ARITH_CMP: begin
                b_mux = ~b;           // One's complement for subtraction
                cin_mux = cin;        // For subtraction: A - B = A + ~B + 1 (cin=1 means no borrow)
            end
            ARITH_INC: begin
                b_mux = 16'h0000;
                cin_mux = 1'b1;       // Add 1
            end
            ARITH_DEC: begin
                b_mux = 16'hFFFF;     // Add -1 (two's complement)
                cin_mux = 1'b0;
            end
            default: begin
                b_mux = b;
                cin_mux = cin;
            end
        endcase
    end
    
    // =========================================================================
    // Optimized Carry Skip Adder (Mixed Architecture)
    // Lower 8 bits: Carry Skip (2-3-3 configuration)
    // Upper 8 bits: Carry Select for speed
    // =========================================================================
    
    // Group 0: Bits [1:0] - 2-bit Ripple Carry Adder
    logic [1:0] sum_g0;
    logic       c0, c1, c2;
    
    assign c0 = cin_mux;
    full_adder fa0 (.a(a[0]), .b(b_mux[0]), .cin(c0), .sum(sum_g0[0]), .cout(c1));
    full_adder fa1 (.a(a[1]), .b(b_mux[1]), .cin(c1), .sum(sum_g0[1]), .cout(c2));
    
    assign group_carry[0] = c2;
    assign group_propagate[0] = (a[0] ^ b_mux[0]) & (a[1] ^ b_mux[1]);
    assign group_generate[0] = (a[1] & b_mux[1]) | ((a[1] ^ b_mux[1]) & a[0] & b_mux[0]);
    
    // Group 1: Bits [4:2] - 3-bit Ripple Carry with Skip
    logic [2:0] sum_g1;
    logic       c3, c4, c5;
    logic       skip_carry_g1;
    
    assign c3 = group_carry[0];
    full_adder fa2 (.a(a[2]), .b(b_mux[2]), .cin(c3), .sum(sum_g1[0]), .cout(c4));
    full_adder fa3 (.a(a[3]), .b(b_mux[3]), .cin(c4), .sum(sum_g1[1]), .cout(c5));
    full_adder fa4 (.a(a[4]), .b(b_mux[4]), .cin(c5), .sum(sum_g1[2]), .cout(skip_carry_g1));
    
    assign group_propagate[1] = (a[2] ^ b_mux[2]) & (a[3] ^ b_mux[3]) & (a[4] ^ b_mux[4]);
    assign group_carry[1] = group_propagate[1] ? group_carry[0] : skip_carry_g1;
    
    // Group 2: Bits [7:5] - 3-bit Ripple Carry with Skip
    logic [2:0] sum_g2;
    logic       c6, c7, c8;
    logic       skip_carry_g2;
    
    assign c6 = group_carry[1];
    full_adder fa5 (.a(a[5]), .b(b_mux[5]), .cin(c6), .sum(sum_g2[0]), .cout(c7));
    full_adder fa6 (.a(a[6]), .b(b_mux[6]), .cin(c7), .sum(sum_g2[1]), .cout(c8));
    full_adder fa7 (.a(a[7]), .b(b_mux[7]), .cin(c8), .sum(sum_g2[2]), .cout(skip_carry_g2));
    
    assign group_propagate[2] = (a[5] ^ b_mux[5]) & (a[6] ^ b_mux[6]) & (a[7] ^ b_mux[7]);
    assign group_carry[2] = group_propagate[2] ? group_carry[1] : skip_carry_g2;
    
    // Group 3: Bits [15:8] - 8-bit Carry Select Adder for speed
    logic [7:0] sum_g3_c0, sum_g3_c1;
    logic       cout_g3_c0, cout_g3_c1;
    
    // Calculate both possibilities in parallel
    ripple_carry_adder_8bit rca_c0 (
        .a(a[15:8]),
        .b(b_mux[15:8]),
        .cin(1'b0),
        .sum(sum_g3_c0),
        .cout(cout_g3_c0)
    );
    
    ripple_carry_adder_8bit rca_c1 (
        .a(a[15:8]),
        .b(b_mux[15:8]),
        .cin(1'b1),
        .sum(sum_g3_c1),
        .cout(cout_g3_c1)
    );
    
    // Select based on actual carry from group 2
    logic [7:0] sum_g3;
    assign sum_g3 = group_carry[2] ? sum_g3_c1 : sum_g3_c0;
    assign group_carry[3] = group_carry[2] ? cout_g3_c1 : cout_g3_c0;
    
    // =========================================================================
    // Result Assembly
    // =========================================================================
    assign sum = {sum_g3, sum_g2, sum_g1, sum_g0};
    assign carry_out = group_carry[3];
    
    // Output assignment based on operation
    always_comb begin
        if (ctrl == ARITH_CMP) begin
            // CMP operation: don't update result, only flags
            result = 16'h0000;
        end else begin
            result = sum;
        end
        
        cout = carry_out;
        
        // Overflow detection for signed arithmetic
        // Overflow occurs when: pos + pos = neg, or neg + neg = pos
        if (ctrl == ARITH_ADD || ctrl == ARITH_INC) begin
            overflow = (a[15] == b_mux[15]) && (sum[15] != a[15]);
        end else if (ctrl == ARITH_SUB || ctrl == ARITH_CMP) begin
            // For subtraction: A - B, check if (pos - neg = neg) or (neg - pos = pos)
            overflow = (a[15] != b[15]) && (sum[15] != a[15]);
        end else if (ctrl == ARITH_DEC) begin
            // Decrement: check if neg - 1 = pos (underflow)
            overflow = (a[15] == 1'b1) && (sum[15] == 1'b0) && (a == 16'h8000);
        end else begin
            overflow = 1'b0;
        end
    end
    
endmodule : alu_arithmetic_unit

// =============================================================================
// Helper module: Full Adder
// =============================================================================
module full_adder (
    input  logic a,
    input  logic b,
    input  logic cin,
    output logic sum,
    output logic cout
);
    assign sum = a ^ b ^ cin;
    assign cout = (a & b) | (cin & (a ^ b));
endmodule : full_adder

// =============================================================================
// Helper module: 8-bit Ripple Carry Adder
// =============================================================================
module ripple_carry_adder_8bit (
    input  logic [7:0] a,
    input  logic [7:0] b,
    input  logic       cin,
    output logic [7:0] sum,
    output logic       cout
);
    logic [7:0] carry;
    
    full_adder fa[7:0] (
        .a(a),
        .b(b),
        .cin({carry[6:0], cin}),
        .sum(sum),
        .cout(carry)
    );
    
    assign cout = carry[7];
endmodule : ripple_carry_adder_8bit
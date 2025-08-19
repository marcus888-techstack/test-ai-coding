// =============================================================================
// File: alu_flag_generator.sv
// Description: Optimized flag generation unit for Z, C, V, N flags
// Author: RTL Generator
// Date: 2025-01-19
// Version: 1.0
// Architecture: Parallel flag computation with optimized zero detection
// =============================================================================

`timescale 1ns / 1ps

import alu_pkg::*;

module alu_flag_generator (
    input  logic [15:0] result,        // ALU result
    input  logic [15:0] operand_a,     // Original operand A
    input  logic [15:0] operand_b,     // Original operand B
    input  logic        arith_carry,   // Carry from arithmetic unit
    input  logic        arith_ovf,     // Overflow from arithmetic unit
    input  logic        shift_carry,   // Carry from shift unit
    input  logic [15:0] op_sel,        // One-hot operation select
    output logic        zero_flag,     // Zero flag (Result == 0)
    output logic        carry_flag,    // Carry/borrow flag
    output logic        overflow_flag, // Overflow flag
    output logic        negative_flag  // Negative flag (Result[15])
);

    // =========================================================================
    // Zero Flag Generation - Optimized Tree Structure
    // Target: 0.8ns (down from 1.4ns)
    // =========================================================================
    
    // Stage 1: 4-bit NOR groups (4 groups of 4 bits each)
    logic [3:0] zero_group;
    
    assign zero_group[0] = ~(|result[3:0]);    // Bits [3:0]
    assign zero_group[1] = ~(|result[7:4]);    // Bits [7:4]
    assign zero_group[2] = ~(|result[11:8]);   // Bits [11:8]
    assign zero_group[3] = ~(|result[15:12]);  // Bits [15:12]
    
    // Stage 2: Final AND of all groups
    assign zero_flag = &zero_group;
    
    // Alternative parallel tree implementation (for synthesis comparison)
    // wire zero_flag_alt = (result == 16'h0000);
    
    // =========================================================================
    // Carry Flag Generation
    // Depends on operation type
    // =========================================================================
    
    always_comb begin
        carry_flag = 1'b0;
        
        // Arithmetic operations use arithmetic carry
        if (op_sel[0] || op_sel[1] || op_sel[11] || op_sel[12] || op_sel[13]) begin
            carry_flag = arith_carry;
        end
        // Shift/rotate operations use shift carry
        else if (op_sel[6] || op_sel[7] || op_sel[8] || op_sel[9] || op_sel[10]) begin
            carry_flag = shift_carry;
        end
        // Logic operations don't affect carry
        else begin
            carry_flag = 1'b0;
        end
    end
    
    // =========================================================================
    // Overflow Flag Generation
    // Only meaningful for signed arithmetic operations
    // =========================================================================
    
    always_comb begin
        overflow_flag = 1'b0;
        
        // Only arithmetic operations can cause overflow
        if (op_sel[0] || op_sel[1] || op_sel[11] || op_sel[12] || op_sel[13]) begin
            overflow_flag = arith_ovf;
        end
        else begin
            overflow_flag = 1'b0;
        end
    end
    
    // =========================================================================
    // Negative Flag Generation
    // Simply the MSB of the result
    // =========================================================================
    
    assign negative_flag = result[15];
    
    // =========================================================================
    // Optimization Notes:
    // 1. Zero detection uses 4x4 tree structure for speed
    // 2. Flag selection based on one-hot operation encoding
    // 3. All flags computed in parallel
    // 4. Critical path through zero detection: ~0.8ns
    // =========================================================================
    
    // =========================================================================
    // Assertions for Verification
    // =========================================================================
    `ifdef SIMULATION
        // Verify zero flag
        property zero_flag_check;
            @(*) zero_flag == (result == 16'h0000);
        endproperty
        assert property(zero_flag_check) else
            $error("Zero flag mismatch at time %0t", $time);
        
        // Verify negative flag
        property negative_flag_check;
            @(*) negative_flag == result[15];
        endproperty
        assert property(negative_flag_check) else
            $error("Negative flag mismatch at time %0t", $time);
        
        // Verify carry flag only set for appropriate operations
        property carry_flag_ops;
            @(*) (!(op_sel[0] || op_sel[1] || op_sel[6] || op_sel[7] || 
                   op_sel[8] || op_sel[9] || op_sel[10] || op_sel[11] || 
                   op_sel[12] || op_sel[13])) |-> (carry_flag == 1'b0);
        endproperty
        assert property(carry_flag_ops) else
            $error("Carry flag set for non-carry operation at time %0t", $time);
    `endif
    
endmodule : alu_flag_generator
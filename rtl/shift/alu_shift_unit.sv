// =============================================================================
// File: alu_shift_unit.sv
// Description: Optimized single-bit shift unit (not barrel shifter)
// Author: RTL Generator
// Date: 2025-01-19
// Version: 1.0
// Architecture: Single-bit shift/rotate operations for simplicity
// =============================================================================

`timescale 1ns / 1ps

import alu_pkg::*;

module alu_shift_unit (
    input  logic [15:0] a,             // Operand A
    input  logic [2:0]  ctrl,          // Control signals
    input  logic        carry_in,      // Carry input (for rotate operations)
    output logic [15:0] result,        // Shift result
    output logic        carry_out      // Carry output
);

    // =========================================================================
    // Single-bit Shift/Rotate Operations
    // All operations shift/rotate by exactly 1 bit position
    // Optimized for single-cycle execution
    // =========================================================================
    
    always_comb begin
        // Default values
        result = a;
        carry_out = 1'b0;
        
        case (ctrl)
            SHIFT_LSL: begin  // Logical Shift Left
                result = {a[14:0], 1'b0};
                carry_out = a[15];
            end
            
            SHIFT_LSR: begin  // Logical Shift Right
                result = {1'b0, a[15:1]};
                carry_out = a[0];
            end
            
            SHIFT_ASR: begin  // Arithmetic Shift Right (sign extend)
                result = {a[15], a[15:1]};
                carry_out = a[0];
            end
            
            SHIFT_ROL: begin  // Rotate Left
                result = {a[14:0], a[15]};
                carry_out = a[15];
            end
            
            SHIFT_ROR: begin  // Rotate Right
                result = {a[0], a[15:1]};
                carry_out = a[0];
            end
            
            default: begin
                result = a;
                carry_out = 1'b0;
            end
        endcase
    end
    
    // =========================================================================
    // Implementation Notes:
    // 1. Single-bit shifts are simpler and faster than barrel shifter
    // 2. All operations complete in single cycle
    // 3. Carry_in is not used in current implementation (reserved for future)
    // 4. Could be extended to rotate through carry if needed
    // =========================================================================
    
    // =========================================================================
    // Assertions for Verification
    // =========================================================================
    `ifdef SIMULATION
        // Verify LSL operation
        property lsl_check;
            @(*) (ctrl == SHIFT_LSL) |-> 
                (result == {a[14:0], 1'b0}) && (carry_out == a[15]);
        endproperty
        assert property(lsl_check) else
            $error("LSL operation failed at time %0t", $time);
        
        // Verify LSR operation
        property lsr_check;
            @(*) (ctrl == SHIFT_LSR) |-> 
                (result == {1'b0, a[15:1]}) && (carry_out == a[0]);
        endproperty
        assert property(lsr_check) else
            $error("LSR operation failed at time %0t", $time);
        
        // Verify ASR operation
        property asr_check;
            @(*) (ctrl == SHIFT_ASR) |-> 
                (result == {a[15], a[15:1]}) && (carry_out == a[0]);
        endproperty
        assert property(asr_check) else
            $error("ASR operation failed at time %0t", $time);
        
        // Verify ROL operation
        property rol_check;
            @(*) (ctrl == SHIFT_ROL) |-> 
                (result == {a[14:0], a[15]}) && (carry_out == a[15]);
        endproperty
        assert property(rol_check) else
            $error("ROL operation failed at time %0t", $time);
        
        // Verify ROR operation
        property ror_check;
            @(*) (ctrl == SHIFT_ROR) |-> 
                (result == {a[0], a[15:1]}) && (carry_out == a[0]);
        endproperty
        assert property(ror_check) else
            $error("ROR operation failed at time %0t", $time);
    `endif
    
endmodule : alu_shift_unit
// =============================================================================
// File: alu_logic_unit.sv
// Description: Logic unit with parallel bit-slice architecture
// Author: RTL Generator
// Date: 2025-01-19
// Version: 1.0
// Architecture: 16 parallel bit-slice units for minimum delay
// =============================================================================

`timescale 1ns / 1ps

import alu_pkg::*;

module alu_logic_unit (
    input  logic [15:0] a,             // Operand A
    input  logic [15:0] b,             // Operand B
    input  logic [2:0]  ctrl,          // Control signals
    output logic [15:0] result         // Logic result
);

    // =========================================================================
    // Parallel Bit-Slice Logic Operations
    // Each bit is computed independently for maximum parallelism
    // Target delay: 0.6ns (single logic level with compound gates)
    // =========================================================================
    
    genvar i;
    generate
        for (i = 0; i < 16; i++) begin : bit_slice
            // Single bit-slice logic unit
            always_comb begin
                case (ctrl)
                    LOGIC_AND:  result[i] = a[i] & b[i];      // AND operation
                    LOGIC_OR:   result[i] = a[i] | b[i];      // OR operation
                    LOGIC_XOR:  result[i] = a[i] ^ b[i];      // XOR operation
                    LOGIC_NOT:  result[i] = ~a[i];            // NOT operation (A only)
                    LOGIC_TEST: result[i] = a[i] & b[i];      // TEST (same as AND, flags only)
                    default:    result[i] = 1'b0;             // Default to zero
                endcase
            end
        end
    endgenerate
    
    // =========================================================================
    // Optimization Notes:
    // 1. Parallel bit-slice architecture ensures single gate delay
    // 2. Synthesis tools can optimize to compound gates (AOI, OAI)
    // 3. No sequential dependencies between bits
    // 4. TEST operation reuses AND logic (differentiated by flag handling)
    // =========================================================================
    
    // =========================================================================
    // Assertions for Verification
    // =========================================================================
    `ifdef SIMULATION
        // Verify AND operation
        property and_check;
            @(*) (ctrl == LOGIC_AND) |-> (result == (a & b));
        endproperty
        assert property(and_check) else
            $error("AND operation failed at time %0t", $time);
        
        // Verify OR operation
        property or_check;
            @(*) (ctrl == LOGIC_OR) |-> (result == (a | b));
        endproperty
        assert property(or_check) else
            $error("OR operation failed at time %0t", $time);
        
        // Verify XOR operation
        property xor_check;
            @(*) (ctrl == LOGIC_XOR) |-> (result == (a ^ b));
        endproperty
        assert property(xor_check) else
            $error("XOR operation failed at time %0t", $time);
        
        // Verify NOT operation
        property not_check;
            @(*) (ctrl == LOGIC_NOT) |-> (result == ~a);
        endproperty
        assert property(not_check) else
            $error("NOT operation failed at time %0t", $time);
        
        // Verify TEST operation (same as AND but different flag handling)
        property test_check;
            @(*) (ctrl == LOGIC_TEST) |-> (result == (a & b));
        endproperty
        assert property(test_check) else
            $error("TEST operation failed at time %0t", $time);
    `endif
    
endmodule : alu_logic_unit
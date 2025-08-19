// =============================================================================
// File: alu_result_mux.sv
// Description: Optimized hierarchical result multiplexer
// Author: RTL Generator
// Date: 2025-01-19
// Version: 1.0
// Architecture: 4:1 MUX with pre-decoded selection for minimum delay
// =============================================================================

`timescale 1ns / 1ps

import alu_pkg::*;

module alu_result_mux (
    input  logic [15:0] arith_result,  // Arithmetic unit result
    input  logic [15:0] logic_result,  // Logic unit result
    input  logic [15:0] shift_result,  // Shift unit result
    input  logic [15:0] pass_result,   // Pass-through result (operand A)
    input  logic [1:0]  sel,           // Selection control (pre-decoded)
    output logic [15:0] final_result   // Final ALU result
);

    // =========================================================================
    // Optimized 4:1 Multiplexer
    // Uses parallel selection with pre-decoded control signals
    // Target delay: 0.7ns (down from 0.9ns)
    // =========================================================================
    
    always_comb begin
        case (sel)
            SEL_ARITH: final_result = arith_result;
            SEL_LOGIC: final_result = logic_result;
            SEL_SHIFT: final_result = shift_result;
            SEL_PASS:  final_result = pass_result;
            default:   final_result = 16'h0000;
        endcase
    end
    
    // Alternative implementation using conditional assignment
    // (Synthesis tool can choose the better implementation)
    /*
    assign final_result = (sel == SEL_ARITH) ? arith_result :
                         (sel == SEL_LOGIC) ? logic_result :
                         (sel == SEL_SHIFT) ? shift_result :
                         (sel == SEL_PASS)  ? pass_result :
                         16'h0000;
    */
    
    // =========================================================================
    // Optimization Notes:
    // 1. Simple 4:1 MUX is more efficient than hierarchical 16:1
    // 2. Pre-decoded selection signals from control decoder
    // 3. All inputs arrive in parallel (no cascading)
    // 4. Synthesis tool can optimize to transmission gates
    // =========================================================================
    
    // =========================================================================
    // Assertions for Verification
    // =========================================================================
    `ifdef SIMULATION
        // Verify arithmetic result selection
        property arith_sel_check;
            @(*) (sel == SEL_ARITH) |-> (final_result == arith_result);
        endproperty
        assert property(arith_sel_check) else
            $error("Arithmetic result selection failed at time %0t", $time);
        
        // Verify logic result selection
        property logic_sel_check;
            @(*) (sel == SEL_LOGIC) |-> (final_result == logic_result);
        endproperty
        assert property(logic_sel_check) else
            $error("Logic result selection failed at time %0t", $time);
        
        // Verify shift result selection
        property shift_sel_check;
            @(*) (sel == SEL_SHIFT) |-> (final_result == shift_result);
        endproperty
        assert property(shift_sel_check) else
            $error("Shift result selection failed at time %0t", $time);
        
        // Verify pass result selection
        property pass_sel_check;
            @(*) (sel == SEL_PASS) |-> (final_result == pass_result);
        endproperty
        assert property(pass_sel_check) else
            $error("Pass result selection failed at time %0t", $time);
    `endif
    
endmodule : alu_result_mux
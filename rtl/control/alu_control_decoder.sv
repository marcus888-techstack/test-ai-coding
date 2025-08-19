// =============================================================================
// File: alu_control_decoder.sv
// Description: Control decoder for ALU operations (4:16 decoder)
// Author: RTL Generator
// Date: 2025-01-19
// Version: 1.0
// =============================================================================

`timescale 1ns / 1ps

import alu_pkg::*;

module alu_control_decoder (
    input  logic [3:0]  opcode,        // 4-bit operation code
    output logic [15:0] op_sel,        // One-hot operation select
    output logic [2:0]  arith_ctrl,    // Arithmetic unit control
    output logic [2:0]  logic_ctrl,    // Logic unit control  
    output logic [2:0]  shift_ctrl,    // Shift unit control
    output logic [1:0]  result_sel     // Result source selection
);

    // =========================================================================
    // One-hot Decoder (4:16) - Two-stage hierarchical implementation
    // Stage 1: Two 2:4 pre-decoders
    // Stage 2: 4x4 AND array for final one-hot output
    // =========================================================================
    
    logic [3:0] decode_high, decode_low;
    
    // Stage 1: Pre-decoders (NAND-based for speed)
    always_comb begin
        // Upper 2 bits decoder
        decode_high = 4'b0000;
        case (opcode[3:2])
            2'b00: decode_high = 4'b0001;
            2'b01: decode_high = 4'b0010;
            2'b10: decode_high = 4'b0100;
            2'b11: decode_high = 4'b1000;
        endcase
        
        // Lower 2 bits decoder
        decode_low = 4'b0000;
        case (opcode[1:0])
            2'b00: decode_low = 4'b0001;
            2'b01: decode_low = 4'b0010;
            2'b10: decode_low = 4'b0100;
            2'b11: decode_low = 4'b1000;
        endcase
    end
    
    // Stage 2: Final one-hot generation
    always_comb begin
        op_sel = 16'h0000;
        
        // Generate 16 one-hot outputs
        op_sel[0]  = decode_high[0] & decode_low[0];  // 0000: ADD
        op_sel[1]  = decode_high[0] & decode_low[1];  // 0001: SUB
        op_sel[2]  = decode_high[0] & decode_low[2];  // 0010: AND
        op_sel[3]  = decode_high[0] & decode_low[3];  // 0011: OR
        op_sel[4]  = decode_high[1] & decode_low[0];  // 0100: XOR
        op_sel[5]  = decode_high[1] & decode_low[1];  // 0101: NOT
        op_sel[6]  = decode_high[1] & decode_low[2];  // 0110: LSL
        op_sel[7]  = decode_high[1] & decode_low[3];  // 0111: LSR
        op_sel[8]  = decode_high[2] & decode_low[0];  // 1000: ASR
        op_sel[9]  = decode_high[2] & decode_low[1];  // 1001: ROL
        op_sel[10] = decode_high[2] & decode_low[2];  // 1010: ROR
        op_sel[11] = decode_high[2] & decode_low[3];  // 1011: INC
        op_sel[12] = decode_high[3] & decode_low[0];  // 1100: DEC
        op_sel[13] = decode_high[3] & decode_low[1];  // 1101: CMP
        op_sel[14] = decode_high[3] & decode_low[2];  // 1110: TEST
        op_sel[15] = decode_high[3] & decode_low[3];  // 1111: PASS
    end
    
    // =========================================================================
    // Control Signal Generation
    // =========================================================================
    
    // Arithmetic unit control signals
    always_comb begin
        arith_ctrl = ARITH_ADD;
        
        case (1'b1)
            op_sel[0]:  arith_ctrl = ARITH_ADD;  // ADD
            op_sel[1]:  arith_ctrl = ARITH_SUB;  // SUB
            op_sel[11]: arith_ctrl = ARITH_INC;  // INC
            op_sel[12]: arith_ctrl = ARITH_DEC;  // DEC
            op_sel[13]: arith_ctrl = ARITH_CMP;  // CMP
            default:    arith_ctrl = ARITH_ADD;
        endcase
    end
    
    // Logic unit control signals
    always_comb begin
        logic_ctrl = LOGIC_AND;
        
        case (1'b1)
            op_sel[2]:  logic_ctrl = LOGIC_AND;  // AND
            op_sel[3]:  logic_ctrl = LOGIC_OR;   // OR
            op_sel[4]:  logic_ctrl = LOGIC_XOR;  // XOR
            op_sel[5]:  logic_ctrl = LOGIC_NOT;  // NOT
            op_sel[14]: logic_ctrl = LOGIC_TEST; // TEST
            default:    logic_ctrl = LOGIC_AND;
        endcase
    end
    
    // Shift unit control signals
    always_comb begin
        shift_ctrl = SHIFT_LSL;
        
        case (1'b1)
            op_sel[6]:  shift_ctrl = SHIFT_LSL;  // LSL
            op_sel[7]:  shift_ctrl = SHIFT_LSR;  // LSR
            op_sel[8]:  shift_ctrl = SHIFT_ASR;  // ASR
            op_sel[9]:  shift_ctrl = SHIFT_ROL;  // ROL
            op_sel[10]: shift_ctrl = SHIFT_ROR;  // ROR
            default:    shift_ctrl = SHIFT_LSL;
        endcase
    end
    
    // Result source selection
    always_comb begin
        result_sel = SEL_PASS;
        
        // Arithmetic operations
        if (op_sel[0] || op_sel[1] || op_sel[11] || op_sel[12] || op_sel[13])
            result_sel = SEL_ARITH;
        // Logic operations
        else if (op_sel[2] || op_sel[3] || op_sel[4] || op_sel[5] || op_sel[14])
            result_sel = SEL_LOGIC;
        // Shift operations
        else if (op_sel[6] || op_sel[7] || op_sel[8] || op_sel[9] || op_sel[10])
            result_sel = SEL_SHIFT;
        // Pass-through
        else if (op_sel[15])
            result_sel = SEL_PASS;
    end
    
    // =========================================================================
    // Assertions for Verification
    // =========================================================================
    `ifdef SIMULATION
        // Ensure only one operation is selected at a time
        property one_hot_check;
            @(*) $onehot(op_sel);
        endproperty
        assert property(one_hot_check) else
            $error("One-hot violation in op_sel at time %0t", $time);
        
        // Ensure valid result selection
        property valid_result_sel;
            @(*) (result_sel <= 2'b11);
        endproperty
        assert property(valid_result_sel) else
            $error("Invalid result_sel value at time %0t", $time);
    `endif
    
endmodule : alu_control_decoder
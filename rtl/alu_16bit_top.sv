// =============================================================================
// File: alu_16bit_top.sv
// Description: Top-level 16-bit ALU module
// Author: RTL Generator
// Date: 2025-01-19
// Version: 1.0
// Target: 65nm CMOS, 100-200MHz operation
// =============================================================================

`timescale 1ns / 1ps

import alu_pkg::*;

module ALU_16bit (
    // Clock and Reset
    input  logic        CLK,           // System clock
    input  logic        RST_n,         // Active-low asynchronous reset
    input  logic        EN,            // Enable signal
    
    // Data Inputs
    input  logic [15:0] A,             // Operand A
    input  logic [15:0] B,             // Operand B
    input  logic [3:0]  OpCode,        // Operation code
    input  logic        Cin,           // Carry input
    
    // Data Outputs
    output logic [15:0] Result,        // Computation result
    
    // Flag Outputs
    output logic        Zero,          // Zero flag (Result == 0)
    output logic        Carry,         // Carry/borrow flag
    output logic        Overflow,      // Overflow flag
    output logic        Negative       // Negative flag (Result[15])
);

    // Internal signals
    logic [15:0] op_sel;               // One-hot operation select
    logic [15:0] arith_result;         // Arithmetic unit result
    logic [15:0] logic_result;         // Logic unit result
    logic [15:0] shift_result;         // Shift unit result
    logic [15:0] result_comb;          // Combinational result
    
    logic        arith_cout;           // Arithmetic carry out
    logic        arith_overflow;       // Arithmetic overflow
    logic        shift_cout;           // Shift carry out
    
    logic [2:0]  arith_ctrl;           // Arithmetic unit control
    logic [2:0]  logic_ctrl;           // Logic unit control
    logic [2:0]  shift_ctrl;           // Shift unit control
    logic [1:0]  result_sel;           // Result source selection
    
    logic        zero_comb;            // Combinational zero flag
    logic        carry_comb;           // Combinational carry flag
    logic        overflow_comb;        // Combinational overflow flag
    logic        negative_comb;        // Combinational negative flag
    
    // Input registers (for timing closure)
    logic [15:0] a_reg, b_reg;
    logic [3:0]  opcode_reg;
    logic        cin_reg;
    logic        en_reg;
    
    // =========================================================================
    // Input Registration
    // =========================================================================
    always_ff @(posedge CLK or negedge RST_n) begin
        if (!RST_n) begin
            a_reg      <= 16'h0000;
            b_reg      <= 16'h0000;
            opcode_reg <= 4'h0;
            cin_reg    <= 1'b0;
            en_reg     <= 1'b0;
        end else if (EN) begin
            a_reg      <= A;
            b_reg      <= B;
            opcode_reg <= OpCode;
            cin_reg    <= Cin;
            en_reg     <= EN;
        end
    end
    
    // =========================================================================
    // Control Decoder Instance
    // =========================================================================
    alu_control_decoder u_control_decoder (
        .opcode      (opcode_reg),
        .op_sel      (op_sel),
        .arith_ctrl  (arith_ctrl),
        .logic_ctrl  (logic_ctrl),
        .shift_ctrl  (shift_ctrl),
        .result_sel  (result_sel)
    );
    
    // =========================================================================
    // Arithmetic Unit Instance
    // =========================================================================
    alu_arithmetic_unit u_arithmetic_unit (
        .a           (a_reg),
        .b           (b_reg),
        .cin         (cin_reg),
        .ctrl        (arith_ctrl),
        .result      (arith_result),
        .cout        (arith_cout),
        .overflow    (arith_overflow)
    );
    
    // =========================================================================
    // Logic Unit Instance
    // =========================================================================
    alu_logic_unit u_logic_unit (
        .a           (a_reg),
        .b           (b_reg),
        .ctrl        (logic_ctrl),
        .result      (logic_result)
    );
    
    // =========================================================================
    // Shift Unit Instance
    // =========================================================================
    alu_shift_unit u_shift_unit (
        .a           (a_reg),
        .ctrl        (shift_ctrl),
        .carry_in    (cin_reg),
        .result      (shift_result),
        .carry_out   (shift_cout)
    );
    
    // =========================================================================
    // Result Multiplexer Instance
    // =========================================================================
    alu_result_mux u_result_mux (
        .arith_result (arith_result),
        .logic_result (logic_result),
        .shift_result (shift_result),
        .pass_result  (a_reg),
        .sel          (result_sel),
        .final_result (result_comb)
    );
    
    // =========================================================================
    // Flag Generator Instance
    // =========================================================================
    alu_flag_generator u_flag_generator (
        .result       (result_comb),
        .operand_a    (a_reg),
        .operand_b    (b_reg),
        .arith_carry  (arith_cout),
        .arith_ovf    (arith_overflow),
        .shift_carry  (shift_cout),
        .op_sel       (op_sel),
        .zero_flag    (zero_comb),
        .carry_flag   (carry_comb),
        .overflow_flag(overflow_comb),
        .negative_flag(negative_comb)
    );
    
    // =========================================================================
    // Output Registration
    // =========================================================================
    always_ff @(posedge CLK or negedge RST_n) begin
        if (!RST_n) begin
            Result   <= 16'h0000;
            Zero     <= 1'b0;
            Carry    <= 1'b0;
            Overflow <= 1'b0;
            Negative <= 1'b0;
        end else if (en_reg) begin
            Result   <= result_comb;
            Zero     <= zero_comb;
            Carry    <= carry_comb;
            Overflow <= overflow_comb;
            Negative <= negative_comb;
        end
    end
    
    // =========================================================================
    // Assertions for Verification
    // =========================================================================
    `ifdef SIMULATION
        // Check for unknown inputs
        property no_unknown_inputs;
            @(posedge CLK) disable iff (!RST_n)
            EN |-> (!$isunknown(A) && !$isunknown(B) && !$isunknown(OpCode));
        endproperty
        assert property(no_unknown_inputs) else
            $error("Unknown inputs detected at time %0t", $time);
        
        // Check valid opcode range
        property valid_opcode;
            @(posedge CLK) disable iff (!RST_n)
            EN |-> (OpCode <= 4'hF);
        endproperty
        assert property(valid_opcode) else
            $error("Invalid opcode %h at time %0t", OpCode, $time);
    `endif
    
endmodule : ALU_16bit
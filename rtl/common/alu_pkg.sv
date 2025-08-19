// =============================================================================
// File: alu_pkg.sv
// Description: Package containing ALU constants, types, and operation definitions
// Author: RTL Generator
// Date: 2025-01-19
// Version: 1.0
// =============================================================================

package alu_pkg;
    
    // ALU Operation Codes (4-bit)
    typedef enum logic [3:0] {
        OP_ADD  = 4'b0000,  // Addition: Result = A + B + Cin
        OP_SUB  = 4'b0001,  // Subtraction: Result = A - B - Cin
        OP_AND  = 4'b0010,  // Logical AND: Result = A & B
        OP_OR   = 4'b0011,  // Logical OR: Result = A | B
        OP_XOR  = 4'b0100,  // Logical XOR: Result = A ^ B
        OP_NOT  = 4'b0101,  // Logical NOT: Result = ~A
        OP_LSL  = 4'b0110,  // Logical Shift Left: Result = A << 1
        OP_LSR  = 4'b0111,  // Logical Shift Right: Result = A >> 1
        OP_ASR  = 4'b1000,  // Arithmetic Shift Right: Result = A >>> 1
        OP_ROL  = 4'b1001,  // Rotate Left: Result = {A[14:0], A[15]}
        OP_ROR  = 4'b1010,  // Rotate Right: Result = {A[0], A[15:1]}
        OP_INC  = 4'b1011,  // Increment: Result = A + 1
        OP_DEC  = 4'b1100,  // Decrement: Result = A - 1
        OP_CMP  = 4'b1101,  // Compare: A - B (flags only)
        OP_TEST = 4'b1110,  // Test: A & B (flags only)
        OP_PASS = 4'b1111   // Pass-through: Result = A
    } alu_opcode_t;
    
    // Control signals for arithmetic unit
    typedef enum logic [2:0] {
        ARITH_ADD = 3'b000,
        ARITH_SUB = 3'b001,
        ARITH_INC = 3'b010,
        ARITH_DEC = 3'b011,
        ARITH_CMP = 3'b100
    } arith_ctrl_t;
    
    // Control signals for logic unit
    typedef enum logic [2:0] {
        LOGIC_AND  = 3'b000,
        LOGIC_OR   = 3'b001,
        LOGIC_XOR  = 3'b010,
        LOGIC_NOT  = 3'b011,
        LOGIC_TEST = 3'b100
    } logic_ctrl_t;
    
    // Control signals for shift unit
    typedef enum logic [2:0] {
        SHIFT_LSL = 3'b000,
        SHIFT_LSR = 3'b001,
        SHIFT_ASR = 3'b010,
        SHIFT_ROL = 3'b011,
        SHIFT_ROR = 3'b100
    } shift_ctrl_t;
    
    // Result source selection
    typedef enum logic [1:0] {
        SEL_ARITH = 2'b00,
        SEL_LOGIC = 2'b01,
        SEL_SHIFT = 2'b10,
        SEL_PASS  = 2'b11
    } result_sel_t;
    
    // Timing parameters (in ns) for 65nm @ 100MHz
    parameter real T_CLK_PERIOD = 10.0;     // Clock period
    parameter real T_SETUP      = 1.5;      // Setup time
    parameter real T_HOLD       = 0.5;      // Hold time
    parameter real T_PD_MAX     = 5.0;      // Max propagation delay
    parameter real T_CO_MAX     = 3.0;      // Max clock-to-output delay
    
    // Data width parameters
    parameter DATA_WIDTH = 16;
    parameter OP_WIDTH   = 4;
    
    // Power and area budgets
    parameter real POWER_BUDGET_MW = 50.0;  // Total power budget in mW
    parameter real AREA_BUDGET_MM2 = 0.15;  // Total area budget in mm²
    
endpackage : alu_pkg
#!/bin/bash
# =============================================================================
# Script: run_sim.sh
# Description: Run ALU simulation with Icarus Verilog
# Author: RTL Generator
# Date: 2025-01-19
# =============================================================================

set -e  # Exit on error

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

echo -e "${GREEN}=====================================${NC}"
echo -e "${GREEN}    16-bit ALU Simulation Script    ${NC}"
echo -e "${GREEN}=====================================${NC}\n"

# Create simulation directory
echo -e "${YELLOW}[1/5] Creating simulation directory...${NC}"
mkdir -p sim

# Compile RTL and testbench
echo -e "${YELLOW}[2/5] Compiling RTL and testbench...${NC}"
iverilog -g2012 -Wall -o sim/alu_16bit.vvp \
    -I rtl/common \
    rtl/common/alu_pkg.sv \
    rtl/control/alu_control_decoder.sv \
    rtl/arithmetic/alu_arithmetic_unit.sv \
    rtl/logic/alu_logic_unit.sv \
    rtl/shift/alu_shift_unit.sv \
    rtl/mux/alu_result_mux.sv \
    rtl/flags/alu_flag_generator.sv \
    rtl/alu_16bit_top.sv \
    tb/alu_16bit_tb.sv

if [ $? -eq 0 ]; then
    echo -e "${GREEN}✓ Compilation successful${NC}"
else
    echo -e "${RED}✗ Compilation failed${NC}"
    exit 1
fi

# Run simulation
echo -e "${YELLOW}[3/5] Running simulation...${NC}"
cd sim
vvp alu_16bit.vvp > simulation.log 2>&1
cd ..

if [ $? -eq 0 ]; then
    echo -e "${GREEN}✓ Simulation completed${NC}"
else
    echo -e "${RED}✗ Simulation failed${NC}"
    exit 1
fi

# Parse results
echo -e "${YELLOW}[4/5] Parsing results...${NC}"
if grep -q "PASSED" sim/simulation.log; then
    echo -e "${GREEN}✓ All tests PASSED${NC}"
    grep "Total Tests:" sim/simulation.log
    grep "Errors:" sim/simulation.log
else
    echo -e "${RED}✗ Some tests FAILED${NC}"
    grep "Total Tests:" sim/simulation.log
    grep "Errors:" sim/simulation.log
    echo -e "${YELLOW}Check sim/simulation.log for details${NC}"
fi

# Generate summary
echo -e "${YELLOW}[5/5] Generating summary...${NC}"
echo -e "\n${GREEN}=====================================${NC}"
echo -e "${GREEN}         Simulation Summary          ${NC}"
echo -e "${GREEN}=====================================${NC}"
echo "Log file: sim/simulation.log"
echo "VCD file: sim/alu_16bit.vcd"
echo ""
echo "To view waveforms, run:"
echo "  gtkwave sim/alu_16bit.vcd"
echo ""
echo -e "${GREEN}=====================================${NC}\n"

# Check for errors in log
if grep -q "ERROR" sim/simulation.log; then
    echo -e "${RED}Errors found in simulation:${NC}"
    grep "ERROR" sim/simulation.log | head -10
    echo -e "${YELLOW}(Showing first 10 errors)${NC}"
fi

exit 0
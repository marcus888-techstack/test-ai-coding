# =============================================================================
# Makefile for 16-bit ALU RTL Simulation
# Author: RTL Generator
# Date: 2025-01-19
# =============================================================================

# Simulator selection (iverilog, xsim, vsim, vcs)
SIM ?= iverilog

# Directories
RTL_DIR = rtl
TB_DIR = tb
SIM_DIR = sim

# Source files
RTL_SOURCES = \
	$(RTL_DIR)/common/alu_pkg.sv \
	$(RTL_DIR)/control/alu_control_decoder.sv \
	$(RTL_DIR)/arithmetic/alu_arithmetic_unit.sv \
	$(RTL_DIR)/logic/alu_logic_unit.sv \
	$(RTL_DIR)/shift/alu_shift_unit.sv \
	$(RTL_DIR)/mux/alu_result_mux.sv \
	$(RTL_DIR)/flags/alu_flag_generator.sv \
	$(RTL_DIR)/alu_16bit_top.sv

TB_SOURCES = \
	$(TB_DIR)/alu_16bit_tb.sv

# Output files
VCD_FILE = $(SIM_DIR)/alu_16bit.vcd
LOG_FILE = $(SIM_DIR)/simulation.log

# Compilation flags
VLOG_FLAGS = -g2012 -Wall
VVP_FLAGS = 

# Default target
all: sim

# Create simulation directory
$(SIM_DIR):
	@mkdir -p $(SIM_DIR)

# Compile with Icarus Verilog
compile-iverilog: $(SIM_DIR)
	iverilog $(VLOG_FLAGS) -o $(SIM_DIR)/alu_16bit.vvp \
		$(RTL_SOURCES) $(TB_SOURCES)

# Run simulation with Icarus Verilog
sim-iverilog: compile-iverilog
	cd $(SIM_DIR) && vvp alu_16bit.vvp | tee simulation.log

# View waveforms
wave: $(VCD_FILE)
	gtkwave $(VCD_FILE) &

# Clean build artifacts
clean:
	rm -rf $(SIM_DIR)
	rm -f *.vcd *.log

# Synthesis with Yosys (optional)
synth:
	yosys -p "read_verilog -sv $(RTL_SOURCES); \
		hierarchy -top ALU_16bit; \
		proc; opt; \
		techmap; opt; \
		write_verilog $(SIM_DIR)/alu_16bit_synth.v; \
		stat"

# Lint with Verilator
lint:
	verilator --lint-only -Wall --top-module ALU_16bit \
		$(RTL_SOURCES)

# Help
help:
	@echo "Makefile for 16-bit ALU Simulation"
	@echo ""
	@echo "Targets:"
	@echo "  all       - Run simulation (default)"
	@echo "  compile   - Compile RTL and testbench"
	@echo "  sim       - Run simulation"
	@echo "  wave      - View waveforms"
	@echo "  synth     - Synthesize with Yosys"
	@echo "  lint      - Lint check with Verilator"
	@echo "  clean     - Remove build artifacts"
	@echo "  help      - Show this help message"
	@echo ""
	@echo "Variables:"
	@echo "  SIM       - Simulator to use (iverilog, xsim, vsim, vcs)"
	@echo ""
	@echo "Examples:"
	@echo "  make              # Run simulation with Icarus Verilog"
	@echo "  make wave         # View waveforms"
	@echo "  make clean        # Clean build artifacts"

# Shortcuts
compile: compile-$(SIM)
sim: sim-$(SIM)

.PHONY: all compile sim wave synth lint clean help
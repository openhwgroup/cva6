LIB             = work
VER             = 10.5c
VLOG_OPTS       = -work $(LIB) +incdir+../common/include

ASSERT_LOG      = assert.log
COMPILE_LOG     = compile.log
SIMULATE_LOG    = simulate.log

RUNSCRIPT_NOGUI	= ./scripts/run.tcl
RUNSCRIPT_GUI	= ./scripts/run_gui.tcl

# Path to the 'CfMath' package.  This default path is correct when this package is used in the
# 'big.pulp' repository.  Otherwise, adapt it so that 'CfMath.sv' can be found at this path.
CF_MATH_PKG_PATH ?= ../../../../../fe/ips/pkg/cfmath

PKGS = $(CF_MATH_PKG_PATH)/CfMath.sv
SRCS = $(wildcard ../common/modules/*.sv) $(wildcard ../../rtl/*.sv)

nogui: ${LIB} compile sim_nogui evaluate
gui: ${LIB} compile sim_gui

${LIB}:
	@vlib-${VER} ${LIB}

compile: $(PKGS) $(SRCS) Testbench.sv
	@rm -f $(COMPILE_LOG)
	@vlog-${VER} $(VLOG_OPTS) $^ >> $(COMPILE_LOG); \
		rc=$$?; \
		if [ $$rc != 0 ]; then \
			cat $(COMPILE_LOG); \
			exit $$rc; \
		fi

sim_nogui:
	@if [ -e '$(RUNSCRIPT_NOGUI)' ]; then \
		RUN_CMD="source $(RUNSCRIPT_NOGUI)"; \
	else \
		RUN_CMD="run"; \
	fi; \
	vsim-${VER} -c -do "$$RUN_CMD; quit" -assertfile $(ASSERT_LOG) $(LIB).Testbench > $(SIMULATE_LOG); \
		rc=$$?; \
		if [ $$rc != 0 ]; then \
			cat $(SIMULATE_LOG); \
			exit $$rc; \
		fi

sim_gui:
	@if [ -e '$(RUNSCRIPT_GUI)' ]; then \
		RUN_CMD="source $(RUNSCRIPT_GUI)"; \
	else \
		RUN_CMD="run"; \
	fi; \
	vsim-${VER} -voptargs=+acc -do "$$RUN_CMD" $(LIB).Testbench

evaluate:
	@if [ \"$$(wc -l $(ASSERT_LOG) | cut -d' ' -f1)\" != \"0\" ]; then \
		cat $(ASSERT_LOG); \
		exit 1; \
	else \
		echo "All assertions passed."; \
	fi

clean:
	@rm -rf work
	@rm -f *.log *.out *.wlf
	@rm -f modelsim.ini transcript

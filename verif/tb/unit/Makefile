VERILATOR ?= verilator
ROOT := ../../..
BUILD_ROOT ?= .build
TESTS := $(patsubst %.sv,%,$(notdir $(wildcard *_test.sv)))

.PHONY: all clean $(TESTS)

all: $(TESTS)

trigger_loadaddr_test:
	mkdir -p $(BUILD_ROOT)
	$(VERILATOR) --binary --assert --timing -Wno-fatal -Wno-WIDTHTRUNC -Wno-WIDTHEXPAND -Wno-MULTIDRIVEN --top-module $@ --Mdir $(BUILD_ROOT)/$@ $(ROOT)/core/include/config_pkg.sv $(ROOT)/core/include/cv64a6_imafdc_sv39_config_pkg.sv $(ROOT)/core/include/build_config_pkg.sv $(ROOT)/core/include/riscv_pkg.sv $(ROOT)/core/include/ariane_pkg.sv $(ROOT)/core/include/triggers_pkg.sv $(ROOT)/core/trigger_module.sv $@.sv
	$(BUILD_ROOT)/$@/V$@

clean:
	rm -rf $(BUILD_ROOT)

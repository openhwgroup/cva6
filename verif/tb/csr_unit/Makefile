ROOT := ../../..
BUILD := .build/mstatus_wpri_test

SOURCES := \
	$(ROOT)/core/include/config_pkg.sv \
	$(ROOT)/core/include/cv64a6_imafdc_sv39_config_pkg.sv \
	$(ROOT)/core/include/build_config_pkg.sv \
	$(ROOT)/core/include/riscv_pkg.sv \
	$(ROOT)/core/include/ariane_pkg.sv \
	$(ROOT)/core/include/triggers_pkg.sv \
	$(ROOT)/core/trigger_module.sv \
	$(ROOT)/core/csr_regfile.sv \
	mstatus_wpri_test.sv

.PHONY: mstatus_wpri_test
mstatus_wpri_test:
	mkdir -p .build
	verilator --binary --assert --timing -Wno-fatal -Wno-PINMISSING -Wno-WIDTHTRUNC -Wno-WIDTHEXPAND -Wno-MULTIDRIVEN -I$(ROOT)/core/include --top-module mstatus_wpri_test --Mdir $(BUILD) $(SOURCES)
	$(BUILD)/Vmstatus_wpri_test

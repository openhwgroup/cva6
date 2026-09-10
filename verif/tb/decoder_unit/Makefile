ROOT := ../../..
BUILD := .build/zicbom_permissions_test

SOURCES := \
	$(ROOT)/core/include/config_pkg.sv \
	$(ROOT)/core/include/cv64a6_imafdch_sv39_config_pkg.sv \
	$(ROOT)/core/include/build_config_pkg.sv \
	$(ROOT)/core/include/riscv_pkg.sv \
	$(ROOT)/core/include/ariane_pkg.sv \
	$(ROOT)/core/decoder.sv \
	zicbom_permissions_test.sv

.PHONY: zicbom_permissions_test
zicbom_permissions_test:
	mkdir -p .build
	verilator --binary --assert --timing \
		-Wno-fatal \
		-Wno-PINMISSING \
		-Wno-UNOPTFLAT \
		-Wno-WIDTHTRUNC \
		-Wno-WIDTHEXPAND \
		-I$(ROOT)/core/include \
		--top-module zicbom_permissions_test \
		--Mdir $(BUILD) \
		$(SOURCES)
	$(BUILD)/Vzicbom_permissions_test

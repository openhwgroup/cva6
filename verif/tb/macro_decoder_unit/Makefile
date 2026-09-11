ROOT := ../../..
BUILD := .build/macro_decoder_issue_ack_test

SOURCES := \
	$(ROOT)/core/include/config_pkg.sv \
	$(ROOT)/core/include/cv32a6_imac_sv32_config_pkg.sv \
	$(ROOT)/core/include/build_config_pkg.sv \
	$(ROOT)/core/include/riscv_pkg.sv \
	$(ROOT)/core/macro_decoder.sv \
	macro_decoder_issue_ack_test.sv

.PHONY: all macro_decoder_issue_ack_test clean

all: macro_decoder_issue_ack_test

macro_decoder_issue_ack_test:
	mkdir -p .build
	verilator \
		--binary \
		--assert \
		--timing \
		-Wno-fatal \
		-Wno-PINMISSING \
		-Wno-WIDTHTRUNC \
		-Wno-WIDTHEXPAND \
		-I$(ROOT)/core/include \
		--top-module macro_decoder_issue_ack_test \
		--Mdir $(BUILD) \
		$(SOURCES)
	$(BUILD)/Vmacro_decoder_issue_ack_test

clean:
	rm -rf .build

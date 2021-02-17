#
# Copyright 2020 OpenHW Group
# Copyright 2020 Symbiotic EDA
#
# Licensed under the Solderpad Hardware License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
# https://solderpad.org/licenses/
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
#
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
#

VERI_CFLAGS += -DMCY

include $(PROJ_ROOT_DIR)/cv32/sim/core/Makefile

DIV_ONLY_FIRMWARE = $(CORE_TEST_DIR)/div_only_firmware
DIV_ONLY_FIRMWARE_OBJS = $(addprefix $(DIV_ONLY_FIRMWARE)/, start.o print.o stats.o)
DIV_ONLY_TEST_OBJS =$(RISCV_TESTS)/rv32um/div.o $(RISCV_TESTS)/rv32um/divu.o $(RISCV_TESTS)/rv32um/rem.o $(RISCV_TESTS)/rv32um/remu.o

$(DIV_ONLY_FIRMWARE)/div_only_firmware.elf: $(DIV_ONLY_FIRMWARE_OBJS) $(RISCV_TESTS_OBJS) $(DIV_ONLY_FIRMWARE)/link.ld
	$(RISCV_EXE_PREFIX)gcc -g -Os -march=rv32imc -ffreestanding -nostdlib -o $@ \
	$(RISCV_TEST_INCLUDES) \
	-Wl,-Bstatic,-T,$(DIV_ONLY_FIRMWARE)/link.ld,-Map,$(DIV_ONLY_FIRMWARE)/div_only_firmware.map,--strip-debug \
	$(DIV_ONLY_FIRMWARE_OBJS) $(DIV_ONLY_TEST_OBJS) -lgcc

$(DIV_ONLY_FIRMWARE)/start.o: $(DIV_ONLY_FIRMWARE)/start.S
	$(RISCV_EXE_PREFIX)gcc -c -march=rv32imc -g -o $@ $<

$(DIV_ONLY_FIRMWARE)/%.o: $(DIV_ONLY_FIRMWARE)/%.c
	$(RISCV_EXE_PREFIX)gcc -c -march=rv32ic -g -Os --std=c99 -Wall \
		$(RISCV_TEST_INCLUDES) \
		-ffreestanding -nostdlib -o $@ $<

.PHONY: div-only-veri-run
div-only-veri-run: verilate $(DIV_ONLY_FIRMWARE)/div_only_firmware.hex
	mkdir -p $(VERI_LOG_DIR)
	./testbench_verilator $(VERI_FLAGS) \
		"+firmware=$(DIV_ONLY_FIRMWARE)/div_only_firmware.hex" \
		| tee $(VERI_LOG_DIR)/div-only-veri-run.log

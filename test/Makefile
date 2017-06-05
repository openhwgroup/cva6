CC 		= riscv64-unknown-elf-gcc
OBJDUMP = riscv64-unknown-elf-objdump
ODFLAGS =
OBJCOPY = riscv64-unknown-elf-objcopy
OCFLAGS =
ASFLAGS = -c
CFLAGS  =
LDFLAGS =

TESTS = rv64ui-p-add rv64ui-p-addi

$(TESTS).v: $(TESTS)
	$(OBJCOPY)  -O verilog -I elf64-little $< $<.v

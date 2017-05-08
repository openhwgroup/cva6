CC 		= riscv64-unknown-elf-gcc
OBJDUMP = riscv64-unknown-elf-objdump
ODFLAGS =
OBJCOPY = riscv64-unknown-elf-objcopy
OCFLAGS =
ASFLAGS = -c
CFLAGS  =
LDFLAGS =

TESTS = add_test

.S.o:
	$(CC) $(ASFLAGS) -o $@ $<


# .c.o:
# 	$(CC) $(CFLAGS) -o $@ -c $<
# .v: .S.o

$(TESTS): $(TESTS).o
	$(OBJCOPY)  -O verilog -I elf64-little $< $@.v

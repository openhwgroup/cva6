# See LICENSE.SiFive for license details

debug_rom = debug_rom.img

GCC=riscv64-unknown-elf-gcc
OBJCOPY=riscv64-unknown-elf-objcopy

all: $(debug_rom)

%.img: %.bin
	dd if=$< of=$@ bs=128 count=1

%.bin: %.elf
	$(OBJCOPY) -O binary $< $@

%.elf: %.S link.ld
	$(GCC) -I$(RISCV)/include -Tlink.ld $< -nostdlib -static -Wl,--no-gc-sections -o $@

clean:
	rm $(debug_rom)


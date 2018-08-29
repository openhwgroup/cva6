bootrom_img = bootrom.img

GCC=riscv64-unknown-elf-gcc
OBJCOPY=riscv64-unknown-elf-objcopy
DTB=ariane.dtb

all: $(bootrom_img)

%.img: %.bin
	dd if=$< of=$@ bs=128

%.bin: %.elf
	$(OBJCOPY) -O binary $< $@

%.elf: %.S linker.ld $(DTB)
	$(GCC) -Tlinker.ld $< -nostdlib -static -Wl,--no-gc-sections -o $@

%.dtb: %.dts
	dtc -I dts $< -O dtb -o $@

clean:
	rm $(bootrom_img) $(DTB)

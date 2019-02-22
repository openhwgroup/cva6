ENTRY(main)

SECTIONS
{
    ROM_BASE = 0x10000; /* ... but actually position independent */

    . = ROM_BASE;

    .text.init : { *(.text.init) }

    .text : ALIGN(0x100) {
    _TEXT_START_ = .;
        *(.text)
    _TEXT_END_ = .;
    }

    .data : ALIGN(0x100) {
    _DATA_START_ = .;
        *(.data)
    _DATA_END_ = .;
    }

    PROVIDE(_data = ADDR(.data));
    PROVIDE(_data_lma = LOADADDR(.data));
    PROVIDE(_edata = .);

    .bss : ALIGN(0x100) {
    _BSS_START_ = .;
        *(.bss)
    _BSS_END_ = .;
    }

    .rodata : ALIGN(0x100) {
    _RODATA_START_ = .;
        *(.rodata)
        *(.dtb*)
        *(.rodata*)
    _RODATA_END_ = .;
    }
}

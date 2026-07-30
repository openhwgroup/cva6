OUTPUT_ARCH( "riscv" )
ENTRY(_start)

MEMORY {
  /* Mapped directly to the ExecuteRegionAddrBase from the SV package */
  RAM (rwx) : ORIGIN = 0x80000000, LENGTH = 64M
}

SECTIONS {
  .text : {
    /* Force the start code from crt0.S to be the very first thing in memory */
    *(.text.start)
    *(.text .text.*)
  } > RAM

  /* Provide the trap vector address for mtvec */
  .vectors : ALIGN(64) {
    __vector_start = .;
    KEEP(*(.vectors))
  } > RAM

  .rodata : {
    *(.rodata .rodata.*)
  } > RAM

  .data : {
    *(.data .data.*)
    . = ALIGN(8);
    /* Provide the global pointer for crt0.S */
    PROVIDE( __global_pointer$ = . + 0x800 );
    *(.sdata .sdata.*)
  } > RAM

  .bss : {
    /* Provide BSS boundaries for crt0.S's memset loop */
    _edata = .;
    *(.bss .bss.*)
    *(.sbss .sbss.*)
    *(COMMON)
    _end = .;
    
    /* Provide the heap start boundary for Newlib's sbrk allocator */
    end = .;
    __end = .;
  } > RAM

  /* Provide the stack pointer to crt0.S */
  __stack_end = ORIGIN(RAM) + LENGTH(RAM);
}
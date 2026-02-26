OUTPUT_ARCH( "riscv" )
ENTRY(_start)

SECTIONS
{
  . = 0x80000000;
  _start_text = .;
  .text.init : { *(.text.init) }
  . = ALIGN(0x1000);
  .tohost : { *(.tohost) }
  . = ALIGN(0x1000);
  .uvmif : { *(.uvmif) }
  . = ALIGN(0x1000);
  .text : { *(.text) }
  . = ALIGN(0x1000);
  .text.startup : { *(.text.startup) }
  . = ALIGN(0x1000);
  _end_text = .;
  . = ALIGN(0x1000);
  .rodata : { *(.rodata*)}
  . = ALIGN(0x8);
  . = ALIGN(0x1000);
  .page_table : { *(.page_table) }
  .user_stack : { *(.user_stack) }
  .kernel_data : { *(.kernel_data) }
  .kernel_stack : { *(.kernel_stack) }
  .data : { *(.data) }
  .sdata : {
    __global_pointer$ = . + 0x800;
    *(.srodata.cst16) *(.srodata.cst8) *(.srodata.cst4) *(.srodata.cst2) *(.srodata*)
    *(.sdata .sdata.* .gnu.linkonce.s.*)
  }
  .bss : { *(.bss) }
  .tdata :
  {
    _tdata_begin = .;
    *(.tdata)
    _tdata_end = .;
  }
  .tbss :
  {
    *(.tbss)
    _tbss_end = .;
  }
  .trampoline ALIGN(4096) : {
    trampoline_start = .;
    *(.trampoline)
    trampoline_end = .;
  }
  _end = .;
}

ASSERT(trampoline_end - trampoline_start <= 4096, "Section .trampoline is larger than a page !");

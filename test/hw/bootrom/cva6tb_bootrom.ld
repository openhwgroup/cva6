/* Copyright 2026 ETH Zurich and University of Bologna. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

ENTRY(_start)

MEMORY {
  dram (rwx)   : ORIGIN = 0x80000000, LENGTH = 8M,
  spm  (rwx)   : ORIGIN = 0x20000000, LENGTH = 1M,
  bootrom (rx) : ORIGIN = 0x00010000, LENGTH = 1K
}

SECTIONS {
  __global_pointer$ = ADDR(.misc) + SIZEOF(.misc) / 2;
  __stack_pointer$  = ORIGIN(spm) + LENGTH(spm) - 8;

  .text : {
    *(.text._start)
    *(.text)
    *(.text.*)
  } > bootrom

  .misc : ALIGN(16) {
    *(.rodata)
    *(.rodata.*)
    *(.data)
    *(.data.*)
    *(.srodata)
    *(.srodata.*)
    *(.sdata)
    *(.sdata.*)
  } > bootrom

  . = ALIGN(32);
  __bss_start = .;
  .bss : {
    *(.bss)
    *(.bss.*)
    *(.sbss)
    *(.sbss.*)
  } > bootrom
  . = ALIGN(32);
  __bss_end = .;

  .bulk : ALIGN(16) {
    *(.bulk)
    *(.bulk.*)
  } > bootrom

  /* Relevant addresses */
  __base_regs    = 0x10000000;
  __base_console = 0x10001000;
  __base_clic    = 0x10040000;
  __base_clint   = 0x02040000;
  __base_plic    = 0x0c000000;
  __base_dram    = ORIGIN(dram);
  __base_spm     = ORIGIN(spm);
  __base_heap    = ADDR(.bulk) + SIZEOF(.bulk);

}

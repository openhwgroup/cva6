/*
This is free and unencumbered software released into the public domain.

Anyone is free to copy, modify, publish, use, compile, sell, or
distribute this software, either in source code form or as a compiled
binary, for any purpose, commercial or non-commercial, and by any
means.
*/

OUTPUT_FORMAT("elf32-littleriscv", "elf32-littleriscv",
	      "elf32-littleriscv")
OUTPUT_ARCH(riscv)
ENTRY(__mem_start)
MEMORY
{
	/* the memory in the testbench is 1024k in size;
	* set LENGTH=1008k and leave at least 16k for stack */
	 mem : ORIGIN = 0x00000000, LENGTH = 0x000fc000
}

SECTIONS
{
	.vectors (ORIGIN(mem)):
	{
		/* . = ALIGN(4); */
		__irq_base_vector = .;
		KEEP(*(.vectors));
	} > mem

	.start (ORIGIN(mem) + 0x80):
	{
		__boot_addr = .;
		KEEP(*(.start));
	} > mem

	/* temporary hack to redirect control flow when PULP_SECURE=0 */
	.legacy_irq (ORIGIN(mem) + 0x8000):
	{
		KEEP(*(.legacy_irq));
	} > mem


	.text.init :
	{
		*(.text.init);
	} > mem

	.text :
	{
		__mem_start = .;
		start*(.text);
		*(.text);
		__mem_end = .;
	} > mem
	_etext = .;

	.data :
	{
		__data_begin = .;
    		*(.data .data.* .gnu.linkonce.d.*)
	} > mem

	.data.string :
	{
		*(.data.string)
	} > mem

	.sdata :
	{
		__sdata_begin = .;
		*(.sdata .sdata.* .gnu.linkonce.s.*)
	} > mem
	_edata = .;

	. = ALIGN(4);
	__bss_start = .;
	.bss :
	{
		*(.bss)
	} > mem

	/* elf special section */
	.sbss :
	{
		*(.sbss)
	} > mem

	. = ALIGN(4);
	__bss_end = .;
	__global_pointer$ = MIN(__sdata_begin + 0x800,
			    MAX(__data_begin + 0x800, __bss_end - 0x800));
	_end = .;
}

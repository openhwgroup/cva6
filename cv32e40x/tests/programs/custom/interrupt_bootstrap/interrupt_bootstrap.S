/* Make sure the vector table gets linked into the binary.  */
.global vector_table

/* Entry point for bare metal programs */
.section .text.start
.global _start
.type _start, @function

_start:
/* initialize global pointer */
.option push
.option norelax
1:	auipc gp, %pcrel_hi(__global_pointer$)
	addi  gp, gp, %pcrel_lo(1b)
.option pop

/* initialize stack pointer */
	la sp, __stack_end

/* clear the bss segment */
	la a0, _edata
	la a2, _end
	sub a2, a2, a0
	li a1, 0
	call memset

/* new-style constructors and destructors */
	la a0, __libc_fini_array
	call atexit
	call __libc_init_array

/* call main */
//	lw a0, 0(sp)                    /* a0 = argc */
//	addi a1, sp, __SIZEOF_POINTER__ /* a1 = argv */
//	li a2, 0                        /* a2 = envp = NULL */
// Initialize these variables to 0. Cannot use argc or argv
// since the stack is not initialized
	li a0, 0
	li a1, 0
	li a2, 0

	call main
	tail exit

.size  _start, .-_start

.global _init
.type   _init, @function
.global _fini
.type   _fini, @function
_init:
_fini:
 /* These don't have to do anything since we use init_array/fini_array. Prevent
    missing symbol error */
	ret
.size  _init, .-_init
.size _fini, .-_fini


// Custom alternate vector table to load at interrupt boostrap address
.section .vectors.alt, "ax"

.global alt_vector_table
.option norvc
.align 8

alt_vector_table:

	j u_sw_irq_handler
	j __no_irq_handler
	j __no_irq_handler
	j m_software_irq_handler
	j __no_irq_handler
	j __no_irq_handler
	j __no_irq_handler
	j m_timer_irq_handler
	j __no_irq_handler
	j __no_irq_handler
	j __no_irq_handler
	j m_external_irq_handler
	j __no_irq_handler
	j __no_irq_handler
	j __no_irq_handler
	j __no_irq_handler
	j m_fast0_irq_handler
	j m_fast1_irq_handler
	j m_fast2_irq_handler
	j m_fast3_irq_handler
	j m_fast4_irq_handler
	j m_fast5_irq_handler
	j m_fast6_irq_handler
	j m_fast7_irq_handler
	j m_fast8_irq_handler
	j m_fast9_irq_handler
	j m_fast10_irq_handler
	j m_fast11_irq_handler
	j m_fast12_irq_handler
	j m_fast13_irq_handler
	j m_fast14_irq_handler
	j m_fast15_irq_handler


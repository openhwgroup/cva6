.globl _start
_start:
    la t0, trap_handler
    csrw mtvec, t0

    # Configure the Jump Vector Table.
    la t0, __jvt_base$

    # JVT CSR = 0x017.
    # Use the numeric CSR address because the bundled assembler does not
    # recognize the Zcmt CSR name.
    csrw 0x017, t0

    fence.i

    # cm.jalt 64
    #
    # The bundled GNU assembler does not recognize the Zcmt mnemonic, so emit
    # the architecturally defined 16-bit encoding directly.
    #
    # index = instruction[9:2] = 64
    # encoding = 0xa102
    .2byte 0xa102

    # cm.jalt must not fall through.
    j fail

target1:
    j pass

trap_handler:
    j fail

pass:
    # RISC-V test convention: tohost = 1 means success.
    li x1, 1
    j write_tohost

fail:
    # An odd value greater than one represents failure.
    li x1, 3

write_tohost:
    la t0, tohost
    sw x1, 0(t0)

1:
    j 1b

# Jump Vector Table.
#
# Entry 0 deliberately points to the failure path.
# Entry 64 deliberately points to target1.
#
# With the buggy six-bit index calculation:
#   index 64 aliases index 0 -> fail
#
# With the correct eight-bit calculation:
#   index 64 -> target1 -> pass
.section .riscv.jvt, "a", @progbits
.align 6
__jvt_base$:
    .word fail
    .space 252
    .word target1

.section .data
.align 6
.global tohost
tohost:
    .dword 0

.align 6
.global fromhost
fromhost:
    .dword 0

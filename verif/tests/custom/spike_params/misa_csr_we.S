.globl main
main:
    # Disable extension C in MISA Extensions field
    li x1, 0x00141100
    csrw 0x301, x1
    # If misa_we=true, following code should provoke illegal instruction exceptions
    # And test should timeout
    c.li x2, 0
    c.addi x2, 2
    c.addi x2, -2
    li x1, 0
    slli x1, x1, 1
    addi x1, x1, 1
    sw x1, tohost, t5

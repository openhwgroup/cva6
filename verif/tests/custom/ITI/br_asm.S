.section .text
.align 1 
.align 4 
.global toto
.type toto, @function


toto: 
    c.li x12,10
    loop:
        bne x13,x13, toto
        bne x13,x13, toto
        bne x13,x13, toto
        bne x13,x13, toto
        la x11, toto
        lw x10, 0(x11)
        bne x13,x13, toto
        bne x13,x13, toto
        bne x13,x13, toto
        bne x13,x13, toto
        bne x13,x13, toto
        bne x13,x13, toto
    c.addi x12, -1
    c.bnez x12, loop


    c.jr ra

# Copyright 2023 Thales DIS France SAS
#
# Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
# You may obtain a copy of the License at https://solderpad.org/licenses/
#

.globl main
main:
    call csr_cycle_overflow
    call csr_instert_overflow
    #End of csr test
    j csr_pass

csr_cycle_overflow:
    #Overflow CYCLE and MCYCLE, MCYCLEH and CYCLEH should increment by 1
    li x3, 0xfffffff0
    csrw mcycle, x3
    
    #Read backs registers
    csrr x14, mcycle
    csrr x14, mcycleh

    #Wait some cycles to overflow MCYCLE and CYCLE
    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop

    #Read backs registers. cycle and mcycle should be arround 0, cycleh and mcycleh should increment by 1
    csrr x14, mcycle
    csrr x14, mcycleh

    #Overflow MCYCLEH and CYCLEH.
    li x3, 0xffffffff
    csrw mcycleh, x3
    li x3, 0xfffffff0
    csrw mcycle, x3

    #Read backs registers
    csrr x14, mcycle
    csrr x14, mcycleh
    
    #Wait some cycles to overflow
    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop
        
    #Read backs registers, cycle and mcycle should be arround 0, cycleh and mcycleh should be 0
    csrr x14, mcycle
    csrr x14, mcycleh

    ret

csr_instert_overflow:
    #Overflow INSTRET and MINSTRET, MINSTRETH and INSTRETH should increment by 1
    li x3, 0xfffffff0
    csrw minstret, x3
    
    #Read backs registers
    csrr x14, minstret
    csrr x14, minstreth

    #Wait some instrets to overflow MINSTRET and INSTRET
    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop

    #Read backs registers. instret and minstret should be arround 0, instreth and minstreth should increment by 1
    csrr x14, minstret
    csrr x14, minstreth

    #Overflow MINSTRETH and INSTRETH.
    li x3, 0xffffffff
    csrw minstreth, x3
    li x3, 0xfffffff0
    csrw minstret, x3

    #Read backs registers
    csrr x14, minstret
    csrr x14, minstreth
    
    #Wait some instrets to overflow
    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop
    nop
        
    #Read backs registers, instret and minstret should be arround 0, instreth and minstreth should be 0
    csrr x14, minstret
    csrr x14, minstreth

    ret

csr_pass:
    li x1, 0
    slli x1, x1, 1
    addi x1, x1, 1
    sw x1, tohost, x30
    self_loop: j self_loop

csr_fail:
    li x1, 1
    slli x1, x1, 1
    addi x1, x1, 1
    sw x1, tohost, x30
    self_loop_2: j self_loop_2

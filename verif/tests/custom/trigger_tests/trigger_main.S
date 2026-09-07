# Copyright 2022 Thales DIS design services SAS
#
# Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
# You may obtain a copy of the License at https://solderpad.org/licenses/
#
# Original Author: Mounsaf YOUSFI (mounsaf.yousfi@thalesgroup.fr)

#*****************************************************************************
# mcontrol6 trigger test for all trigger types
#-----------------------------------------------------------------------------

.data
load_array: .word 0xBEEFBEEF, 0xBEEEBEEE, 0xBEEFDEAD
store_array: .word 0x00000000, 0x00000000, 0x00000000

  .globl main
main:
    #Load custom trap_handler in trap vector
    la t0, trap_handler
    csrw mtvec, t0
    
    ############### 
    # FIRST BATCH # 
    ###############  

    #Trigger 0 configuration : TRIGGER ON PC EXECUTION
    li x2, 0
    csrw tselect, x2
    #compare value encoding : here it's the PC we want to trigger on 
    la x3, trig0
    csrw tdata2, x3
    #tdata1 encoding
    li x4, 0x60000044 //or : 0x60001044 for debug mode
    csrw tdata1, x4
trig0:
    j fail
    j fail
    j fail
    j fail
handler_return0:
    # Trigger 1 configuration : TRIGGER ON INSTRUCTION
    li x2, 1
    csrw tselect, x2
    #compare value encoding : here it's the instruction we want to trigger on 
    li x3, 0xFFFF4104 //uses masked low match type
    csrw tdata2, x3
    #tdata1 encoding
    li x4, 0x60200244
    csrw tdata1, x4

    # Trigger 2 : TRIGGER ON STORE DATA
    li x2, 2
    csrw tselect, x2
    li x3, 0xBEEFBEEF //Data to match
    csrw tdata2, x3
    li x4, 0x60200042 //Config for store with data match
    csrw tdata1, x4


    # Trigger 3 : TRIGGER ON LOAD DATA
    li x2, 3
    csrw tselect, x2
    li x3, 0xBEEEBEEE //Data to match
    csrw tdata2, x3
    li x4, 0x60200041 //Config for load with data match
    csrw tdata1, x4

    #Random useless instruction
    li x5, 0xDEADDEAD
    #If the triggers were effectively raised and the trap handler correctly handled every one of them, 
    #we should never jump to fail
    beq x5, x5, trig1 #introduce some challenge for speculation handling units
    j fail

trig1: 
    lw x9, 0(x10)
handler_return1:
    beq x4, x5, fail
    li x6, 0xBEEFBEEF
    la x5, store_array
trig2:
    sw x6, 0(x5)
    lw x6, 0(x5)
    j fail
handler_return2:
    bne x6, x5, resume_test
    j fail
resume_test:
    li x6, 0xBEEEBEEE
    addi x9, x9, 4
    sw x6, 0(x9)
    la x1, store_array
    lw x3, 0(x1)
    lw x3, 0(x1)
    lw x3, 0(x1)
    lw x3, 0(x1)//flood with loads to see if we don't infinite loop on break generation logic(tests if load unit is stalled)
    lw x3, 0(x1)
    lw x3, 0(x8)
trig3:
    lw x6, 0(x9)
instruction_on_which_breakpoint_is_generated:
    # addi x13, x13, 2 
    sw x6, 0(x9)
    lw x3, 0(x1)
    lw x3, 0(x1)
    addi x6, x6, -1
    j fail

second_batch:

    ############### 
    #  2ND BATCH  # 
    ###############  
    #Trigger 4 configuration : TRIGGER ON STORE ADDR
    li x2, 0
    csrw tselect, x2
    la x3, store_array //Address to match
    addi x3, x3, 8
    csrw tdata2, x3
    li x4, 0x60000042 //Config for store with address match
    csrw tdata1, x4

    #Trigger 5 configuration : TRIGGER ON LOAD ADDR
    li x2, 1
    csrw tselect, x2
    la x3, load_array //Address to match
    addi x3, x3, 8
    csrw tdata2, x3
    li x4, 0x60000041 //Config for load with address match
    csrw tdata1, x4

    la x3, store_array //Address to match
    li x6, 0x11110000
trig4:
    sw x6, 8(x3)
    j fail
handler_return4:
    lw x6, 8(x3)
    la x5, load_array
    addi x5, x5, 8
    li x6, 0
trig5:
    lw x6, 0(x5)

trigger_chain_test:
    sw x6, 0(x5)
    
    # Trigger 0 CHAIN
    li x2, 0
    csrw tselect, x2
    la x5, 0x0002a303
    csrw tdata2, x5
    li x4, 0x60200844
    csrw tdata1, x4


    # Trigger 1 CHAIN
    li x2, 2
    csrw tselect, x2
    la x5, 0xBEEFBEEF
    csrw tdata2, x5
    li x4, 0x60200841
    csrw tdata1, x4
    
    # Trigger 2 CHAIN
    li x2, 1
    csrw tselect, x2
    #compare value encoding (address to match)
    la x5, load_array   
    csrw tdata2, x5
    li x4, 0x60000041
    csrw tdata1, x4

    la x5, load_array
trig6:
    lw x6, 0(x5)
    j fail

icountplusetrigger:
    li x2, 1
    csrw tselect, x2
    li x3, 0x00000008   # Icount will gen break (ex cause 3)
    csrw tdata2, x3
    li x4, 0x50000200   # match exception value with tdata2 and another break
    csrw tdata1, x4

    li x2, 0
    csrw tselect, x2
    li x2, 0x30003e00    # count 15 instructions break : ICOUNT
    csrw tdata1, x2
icount:
    j icount

itrigger:
    # Trigger setup
    li x2, 1
    csrw tselect, x2

    li x3, 0xFFFFFFFF  # match on software interrupt
    csrw tdata2, x3

    li x4, 0x40000200  # match on software interrupt and gen break
    csrw tdata1, x4
    csrr x5, tdata1

    li a1, 0xFFFFFFFF
    csrw mie, a1
    csrr a2, mie
    li a1, 0x8
    csrw mstatus, a1
it_trigg:
    j fail

.align 4
trap_handler:
    csrr a0, mcause
    csrr a1, mepc
    
    la a2, 0x80000000
    srli a0, a0, 28
    slli a0, a0, 28 //4 MSBs isolation
    bne a2, a0, skipDisableInt //checks if its an interrupt that caused trap handling if yes, disable them, if not, skip disabling
    li a1, 0x0
    csrw mie, a1
    csrr a2, mie
    li a1, 0x0
    csrw mstatus, a1
skipDisableInt:
    csrr a0, mcause
    la a2, icount
    beq a2, a1, default_ret_plus_offset
    li t3, 3
    bne a0, t3, default_ret #if we arent in trap handler for a breakpoint exception, resume execution
    la a2, trap_handler
    bne a2, a1, disable_trigger0
    li a3, 1
    csrw tselect, a3
    li a4, 0x00000000
    csrw tdata1, a4
    beq a2, a1, default_ret #we are here because of etrigger so icount worked, disable both and go to itrigger test
disable_trigger0:
    la a2, trig0
    bne a1, a2, disable_trigger1 //if pc != trig address, it means we aren't here for this trigger (i could keep only this if and remove the prior one)
    li a3, 0                     //else
    csrw tselect, a3             //select trigger 0
    li a4, 0x00000000                   
    csrw tdata1, a4              //disable trigger 0
    li a4, 0                     //wipe compare value
    csrw tdata2, a4
    la a3, handler_return0
    csrw mepc, a3
    beq a1, a2, default_ret //resume
disable_trigger1:
    la a2, trig1
    bne a1, a2, disable_trigger2
    li a3, 1
    csrw tselect, a3
    li a4, 0x00000000
    csrw tdata1, a4
    csrr a4, tdata1 //disable trigger 1
    li a4, 0
    csrw tdata2, a4
    la a3, handler_return1
    csrw mepc, a3
    beq a1, a2, default_ret
disable_trigger2:
    la a2, trig2
    bne a1, a2, disable_trigger3
    li a3, 2
    csrw tselect, a3
    li a4, 0x00000000
    csrw tdata1, a4 //disable trigger 2
    la a3, handler_return2
    csrw mepc, a3
    beq a1, a2, default_ret
disable_trigger3:
    la a2, instruction_on_which_breakpoint_is_generated
    bne a1, a2, disable_trigger4
    li a3, 3
    csrw tselect, a3
    li a4, 0x00000000
    csrw tdata1, a4 //disable trigger 3
    la a3, second_batch
    csrw mepc, a3
    beq a1, a2, default_ret #if load is complete and then trigger happened then jump to second batch of triggers
disable_trigger4:
    la a2, trig4
    bne a1, a2, disable_trigger5
    li a3, 0
    csrw tselect, a3
    li a4, 0x00000000
    csrw tdata1, a4 //disable trigger 4
    la a3, handler_return4
    csrw mepc, a3
    beq a1, a2, default_ret 
disable_trigger5:
    la a2, trig5
    bne a1, a2, disable_trigger6
    li a3, 1
    csrw tselect, a3
    li a4, 0x00000000
    csrw tdata1, a4 //disable trigger 4
    la a3, trigger_chain_test
    csrw mepc, a3
    beq a1, a2, default_ret
disable_trigger6:
    la a2, trig6
    bne a1, a2, disable_trigger7
    li a3, 0
    csrw tselect, a3
    li a4, 0x00000000
    csrw tdata1, a4 //disable chain
    li a3, 1
    csrw tselect, a3
    li a4, 0x00000000
    csrw tdata1, a4 //disable chain
    li a3, 2
    csrw tselect, a3
    li a4, 0x00000000
    csrw tdata1, a4 //disable chain
    la a3, icountplusetrigger
    csrw mepc, a3
    beq a1, a2, default_ret
disable_trigger7:
    la a2, it_trigg
    bne a1, a2, default_ret
    la a3, pass
    csrw mepc, a3
    beq a1, a2, default_ret

    j fail #if none of those condition is met, jump to fail 

default_ret:
    mret

default_ret_plus_offset:
    la a2, itrigger
    csrw mepc, a2
    mret

pass:
    li x1, 0
    slli x1, x1, 1
    addi x1, x1, 1
    sw x1, tohost, x30
    self_loop: j self_loop

fail:
    li x1, 1
    slli x1, x1, 1
    addi x1, x1, 1
    sw x1, tohost, x30
    self_loop_2: j self_loop_2
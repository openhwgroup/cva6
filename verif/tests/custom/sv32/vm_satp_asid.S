#=======================================================================
# SATP ASIDLEN
#-----------------------------------------------------------------------
# Test Description:
#
# ASIDLEN is the number of ASID bits implemented. MAXASID bits for 
# sv32 is 9
#
#=======================================================================

#include "macros.h"

.text
.global _start
_start:
    ALL_MEM_PMP                                                         # PMP permission to all the mem
    la t1,trap_handler                                                  # loads the address of trap handler 
    csrw mtvec,t1                                                       # sets the mtvec to trap handler 
    
    .set EXPECTED_ASID, 0x00400000
    .set ASID_IMPLE_CVA6, 0x00400000

    ALL_MEM_PMP                                                         # set the PMP permissions    	
    csrw satp,x0                                                        # write satp with all zeros (bare mode)
    la t5, EXPECTED_ASID                                                # ASID bits expected for CVA6     
    la t0, ASID_IMPLE_CVA6                                              # ASID bits implemented for CVA6	     
    csrw satp, t0                                                       # Writes the ASID bits implemented to SATP      
    csrr t1, satp                                                       # READS the ASID bits from the SATP     
    and t1, t1, t5                                                      # Checks the expected ASID bits and Implemented bits    
    beq t1, t5, test_pass                                               # Jumps to done if equal
    j test_fail
    
trap_handler:
    csrr t0, mcause                                                     # read the value of mcause
    la t1, rvtest_check                                                 # load the address of trvtest_check

    lw t2, 0(t1)                                                        # if cause expected then load 1 else 0
    lw t3, 4(t1)                                                        # load the expected value of mepc
    lw t4, 8(t1)                                                        # load the expected value of mcause

    li  t1, CAUSE_SUPERVISOR_ECALL                                      # load the value of supervisor ecall
    beq t0,t1,continue_in_m_mode                                        # checks if ecall is occured

    li  t1, CAUSE_USER_ECALL                                            # load the value of user ecall
    beq t0,t1,continue_in_m_mode                                        # checks for ecall is occured

    beqz t2, test_fail                                                  # Jumps to exit if cause is not expected
    csrr t5,mepc                                                        # read the value of mepc

    bne t3,t5, test_fail                                                # check the value of mepc with it's expected value
    bne t0, t4, test_fail                                               # jumps to exit if EXPECTED_CAUSE is'nt equal to mcause

    li t5, CAUSE_FETCH_PAGE_FAULT                                       # load the value of fetch page fault exception
    beq t0,t5,continue_in_m_mode                                        # if fetch page fault jump to next instr in M mode

continue_execution:

    INCREMENT_MEPC   _SUMODE_                                           # update the value of mepc
    j trap_epilogs

continue_in_m_mode:

    INCREMENT_MEPC   _MMODE_                                            # update the value of mepc
    li t1,MSTATUS_MPP                                                   # update the MPP to MSTATUS_MPP for M mode
    csrs mstatus,t1                                                     # update the value mstatus MPP

trap_epilogs:
    la t1, rvtest_check                                                 # load the addr of rvtest_check
    li t2, 0
    sw t2, 0(t1)                                                        # Clear the expected cause
    sw t2, 4(t1)                                                        # Clear the exception PC
    sw t2, 8(t1)                                                        # Clear cause execution number
    mret

test_pass:
    li x1, 0                                                            # Write 0 in x1 if test pass
    j exit                                                              # Jump to exit

test_fail:
    li x1, 1                                                            # Write 1 in x1 if test failed

COREV_VERIF_EXIT_LOGIC                                                  # Exit logic 

.data  
.align 24
    rvtest_check: 

        .word 0xdeadbeef                                                # 1 for cause expected 0  for no cause 
        .word 0xbeefdead                                                # write the value of mepc here (where  cause is expected)
        .word 0xcafecafe                                                # write the value of expect cause 
.align 22                                     
    rvtest_data:   
        .word 0xbeefcafe                                                 
        .word 0xdeadcafe                                                 
        .word 0x00000000                                                 
        .word 0x00000000  
.align 12                                                      
    pgtb_l1:                                                       
        .zero 4096                                                 
    pgtb_l0:                                                       
        .zero 4096                                                                                                     

.align 4; .global tohost;   tohost:   .dword 0;
.align 4; .global fromhost; fromhost: .dword 0;
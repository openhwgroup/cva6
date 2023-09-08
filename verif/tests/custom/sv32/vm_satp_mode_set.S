#=======================================================================
#      RW Access of satp to 
#      test whether SV-32 is working properly
#-----------------------------------------------------------------------
# Test Description:
# Verification of supported address translation scheme i.e sv32
# is selected by writing satp.mode=sv32 and reading back the satp/ This
# covers the following scenarios in machine mode.
#=======================================================================

#include "macros.h"
#define _MMODE_ "M"
#define _SUMODE_ "SU"

.text
.global _start
.option norvc

_start:
    ALL_MEM_PMP                                                             # PMP permission to all the memory    
    SATP_SETUP_SV32(pgtb_l1)                                                # set the SATP for virtualization

check_satp:
    csrr t1, satp                                                           # tests the load access 
    srli t1, t1, 31															# t1 should be equal to 1
    li t2,1
    bne t1,t2,test_fail                                                     # checks either t1 == t2 
    j test_pass
                                                                   
trap_handler:

    csrr t0, mcause                                                         # read the value of mcause 
    la t1, rvtest_check                                                     # load the address of trvtest_check
    
    lw t2, 0(t1)                                                            # if cause expected then load 1 else 0
    lw t3, 4(t1)                                                            # load the expected value of mepc 
    lw t4, 8(t1)                                                            # load the expected value of mcause  

    beqz t2, test_fail                                                      # Jumps to exit if cause is not expected
 
    csrr t5,mepc                                                            # read the value of mepc 
    bne t3,t5,test_fail                                                     # check the value of mepc with it's expected value

    bne  t0, t4, test_fail                                                  # jumps to exit if EXPECTED_CAUSE is'nt equal to mcause

continue_execution:

    INCREMENT_MEPC   _SUMODE_                                               # update the value of mepc
    j trap_epilogs

continue_in_m_mode:

    INCREMENT_MEPC   _MMODE_                                                # update the value of mepc
    li t1,MSTATUS_MPP                                                       # update the MPP to MSTATUS_MPP for M mode
    csrs mstatus,t1                                                         # update the value mstatus MPP

trap_epilogs:

    la t1, rvtest_check                                                     # load the addr of rvtest_check
    li t2, 0
    sw t2, 0(t1)                                                            # Clear the expected cause
    sw t2, 4(t1)                                                            # Clear the exception PC
    sw t2, 8(t1)                                                            # Clear cause execution number
    mret

test_pass:

    li x1, 0                                                                # Write 0 in x1 if test pass
    j exit                                                                  # Jump to exit

test_fail:

    li x1, 1                                                                # Write 1 in x1 if test failed

COREV_VERIF_EXIT_LOGIC                                                      # exit logic 

.data
rvtest_check: 

    .word 0xdeadbeef                                                         # 1 for cause expected 0  for no cause 
    .word 0xbeefdead                                                         # write the value of mepc here (where  cause is expected)
    .word 0xcafecafe                                                         # write the value of expect cause 
.align 12                                   
rvtest_data:   
    .word 0xbeefcafe                                                 
    .word 0xdeadcafe                                                 
    .word 0xcafecafe                                                 
    .word 0xbeefdead  
.align 12                                                      
    pgtb_l1:                                                       
        .zero 4096                                                 
    pgtb_l0:                                                       
        .zero 4096                                                                                                     

.align 4; .global tohost;   tohost:   .dword 0;
.align 4; .global fromhost; fromhost: .dword 0;

#=======================================================================
# SATP mode = Bare for Level 1 PTE 
#-----------------------------------------------------------------------
# Test Description:
#
# If PTE does not have the SATP setuped then, accessing it
# would raise a ILLEGAL_INSTRUCTION fault exception.
# When satp.mode=Bare and PTE has (r,w,x) PMP permissions, this test
# covers the following scenarios in both supervisor and user privilege
# modes for level 1 PTE.
#
# Set SATP = Bare and rest bits to zeros and test the access to PTE.
#=======================================================================

#include "macros.h"

#ifdef smode
    #define SET_PTE_U 0
#else
    #define SET_PTE_U PTE_U
#endif

#define _MMODE_  "M"
#define _SUMODE_ "SU"
.set va, 0x82000000

.text
.global _start
.option norvc

_start:

    ALL_MEM_PMP                                                             # PMP permission to all the memory
    la t1,trap_handler                                                      # loads the address of trap handler 
    csrw mtvec,t1                                                           # sets the mtvec to trap handler 

# ----------------LEVEL 1 PTE Setup for load and store test------------

    la a1,vm_en                                                             # loads the address of label vm_en
    mv a0, a1                                                               # set the VA to PA (identity mapping)
    ori a2, x0, ( PTE_D | PTE_A | SET_PTE_U | PTE_X | PTE_V )               # sets the permission bits
    PTE_SETUP_RV32 ( a1, a2, t1, a0, pgtb_l1, LEVEL1 )                      # setup the PTE for level1

    la a1,rvtest_data                                                       # loads the address of label rvtest_data
    mv a0, a1                                                               # set the VA to PA (identity mapping)
    ori a2, x0, ( PTE_D | PTE_A | SET_PTE_U | PTE_V)                        # sets the permission bits
    PTE_SETUP_RV32(a1, a2, t1, a0, pgtb_l1, LEVEL1)                         # setup the PTE for level1   

    la a1,rvtest_check                                                      # loads the address of label rvtest_check
    mv a0, a1                                                               # set the VA to PA (identity mapping)                                          
    ori a2, x0, ( PTE_D | PTE_A | SET_PTE_U | PTE_W | PTE_R | PTE_V )       # sets the permission bits
    PTE_SETUP_RV32(a1, a2, t1, a0, pgtb_l1, LEVEL1)                         # setup the PTE for level1

# ----------------Set the SATP to Bare_Mode and change the mode----------

    csrw satp, x0           	                                            # Write satp with all zeros (bare mode)
    la a1,vm_en                                                             # loads the address of vm_en
    #ifdef smode																													 
        CHANGE_T0_S_MODE(a1)                                        	    # changes mode M to S and set the MEPC value to a1
    #else
        CHANGE_T0_U_MODE(a1)                                        	    # changes mode M to U and set the MEPC value to a1
    #endif

# ----------------Virtualization Enabeled-------------------------------

vm_en:

    la a1,rvtest_data                                                       # loads the address of label rvtest_data

check_store:

    sw t1,0(a1)                                                             # test the store access  

check_load:

    lw t1,0(a1)                                                             # tests the load access                                                                                                 

    #ifdef smode
      SMODE_ECALL                                                           # changes mode M to S and set the MEPC
    #else
     UMODE_ECALL                                                            # changes mode M to U and set the MEPC
    #endif    
# ----------------------Access test prolog------------------------------                                               

    TEST_PROLOG(va,CAUSE_ILLEGAL_INSTRUCTION)                               # load the addr and expected cause 

# -------------LEVEL 1 PTE Setup for execute test------------------------
                                                                            # Setup a new PTE to test execute
    la a1,check_access                                                      # loads the address of label vm_en
    la a0, va                                                               # set the VA to PA (identity mapping)
    ori a2, x0, ( PTE_D | PTE_A | SET_PTE_U | PTE_X | PTE_V )               # sets the permission bits
    PTE_SETUP_RV32(a1, a2, t1, a0, pgtb_l1, LEVEL1)                         # setup the PTE for level1

# ----------------Set the SATP to Bare_Mode and change the mode---------------------

    csrw satp, x0           	                                            # Write satp with all zeros (bare mode)
    la a1 , va                                                              # loads the virual address of check_access
    #ifdef smode
      CHANGE_T0_S_MODE(a1)                                                  # changes mode M to S and set the MEPC
    #else
      CHANGE_T0_U_MODE(a1)                                                  # changes mode M to U and set the MEPC
    #endif

check_access:                                                               # check access to PTE first with va then with physical address

    li t1, 0x45                                                             
    TEST_STATUS                                                             # checks the status of the test
    j test_pass                                                             # Jump to exit

trap_handler:

    csrr t0, mcause                                                         # read the value of mcause 
    la t1, rvtest_check                                                     # load the address of trvtest_check

    lw t2, 0(t1)                                                            # if cause expected then load 1 else 0
    lw t3, 4(t1)                                                            # load the expected value of mepc 
    lw t4, 8(t1)                                                            # load the expected value of mcause  

    li  t1, CAUSE_SUPERVISOR_ECALL                                          # load the value of supervisor ecall
    beq t0,t1,continue_in_m_mode                                            # checks if ecall is occured

    li  t1, CAUSE_USER_ECALL                                                # load the value of user ecall
    beq t0,t1,continue_in_m_mode                                            # checks for ecall is occured

    beqz t2, test_fail                                                      # Jumps to exit if cause is not expected

    csrr t5,mepc                                                            # read the value of mepc 
    bne t3,t5,test_fail                                                     # check the value of mepc with it's expected value

    bne  t0, t4, test_fail                                                  # jumps to exit if EXPECTED_CAUSE is'nt equal to mcause

    li t5, CAUSE_ILLEGAL_INSTRUCTION                                        # load the value of illegal instruction fault 
    beq t0,t5,Back_to_check_access                                          # if illegal instruction fault jump to check access in M mod

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

Back_to_check_access:

    la t3,check_access                                                      # loads the address of check_access
    csrw mepc,t3                                                            # update the value of mepc with check_access address
    li t1,MSTATUS_MPP                                                       # update the MPP to MSTATUS_MPP for M mode
    csrs mstatus,t1                                                         # update the value mstatus MPP 
    j trap_epilogs

test_pass:

    li x1, 0                                                                # Write 0 in x1 if test pass
    j exit                                                                  # Jump to exit

test_fail:

    li x1, 1                                                                # Write 1 in x1 if test failed

COREV_VERIF_EXIT_LOGIC                                                      # Exit logic 

.data  
.align 24                                                                   # Superpage align  
    rvtest_check: 
      .word 0xdeadbeef                                                      # 1 for cause expected 0  for no cause 
      .word 0xbeefdead                                                      # write the value of mepc here (where  cause is expected)
      .word 0xcafecafe                                                      # write the value of expect cause 
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

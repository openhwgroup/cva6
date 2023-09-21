#=======================================================================
#      Read Access of PTE at level0 in User and Supervisor mode when 
#      mstatus.mxr = 1  and only PTE.X = 1
#-----------------------------------------------------------------------
# Test Description:
# If PTE has only execute permission (pte.x = 1) and s/mstatus.MXR=1,
# then read access on that PTE should be successful without having
# explicit read permission (pte.r=0). This test
# covers the following scenarios in both supervisor and user privilege
# modes for level0 PTE.
#                           Level 0
#   - mstatus.mxr = 1 and only PTE.X = 1  with the READ access
#     in the supervisor and user mode
#=======================================================================

#include "macros.h"

#ifdef smode
    #define SET_PTE_U 0
#else
    #define SET_PTE_U PTE_U
#endif

#define _MMODE_  "M"
#define _SUMODE_ "SU"

.text
.global _start
.option norvc

_start:
    ALL_MEM_PMP                                                            # PMP permission to all the memory
    la t1,trap_handler                                                     # loads the address of trap handler 
    csrw mtvec,t1                                                          # sets the mtvec to trap handler 

# ----------------LEVEL1 PTE Setup to point to LEVEL0 PTE----------------
    la a1,pgtb_l0                                                          # loads the address of label pbtb_l0
    mv a0, a1                                                              # generrates the VA for label pbtb_l0
    ori a2, x0, ( PTE_V )                                                  # sets the permission bits
    PTE_SETUP_RV32(a1, a2, t1, a0, pgtb_l1, LEVEL1)                        # setup the PTE for level1

# ----------------LEVEL 0 PTE Setup for load and store test--------------
    la a1,vm_en                                                            # loads the address of label vm_en
    mv a0, a1                                                              # set the VA to PA (identity mapping)
    ori a2, x0, ( PTE_D | PTE_A | SET_PTE_U | PTE_X | PTE_V )              # sets the permission bits
    PTE_SETUP_RV32(a1, a2, t1, a0, pgtb_l0, LEVEL0)                        # setup the PTE for level0
 
    la a1,rvtest_data                                                      # loads the address of label rvtest_data
    sw a1, 0(a1)                                                           # store the random number
    mv a0, a1                                                              # set the VA to PA (identity mapping)
    ori a2, x0, ( PTE_D | PTE_A | SET_PTE_U | PTE_X | PTE_V )			   # sets the permission bits -- only X permission
    PTE_SETUP_RV32(a1, a2, t1, a0, pgtb_l0, LEVEL0)                        # setup the PTE for level0

# ----------------Set the SATP and change the mode-----------------------

    SATP_SETUP_SV32(pgtb_l1)                                               # set the SATP for virtualization
    la a1,vm_en                                                            # loads the address of vm_en
    li t4, MSTATUS_MXR
    csrs mstatus, t4    				                                   # MXR bit set on mstatus
    #ifdef smode																													 
        CHANGE_T0_S_MODE(a1)                                        	   # changes mode M to S and set the MEPC value to a1
    #else
        CHANGE_T0_U_MODE(a1)                                        	   # changes mode M to U and set the MEPC value to a1
    #endif

# ----------------Virtualization Enabeled-------------------------------

vm_en:

    la a1, rvtest_data                                                      # loads the address of label rvtest_data

check_load:

    lw t1,0(a1)                                                             # tests the load access 

    #ifdef smode
        SMODE_ECALL                                                         # SMODE ecall 
    #else
        UMODE_ECALL                                                         # UMODE ecall 
    #endif	

test_pass:

    li x1, 0                                                                # Write 0 in x1 if test pass
    j exit                                                                  # Jump to exit

test_fail:

    li x1, 1                                                                # Write 1 in x1 if test failed
    j exit                                                                  # Jump to exit
                                                                   
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

COREV_VERIF_EXIT_LOGIC                                                      # exit logic 

.data  
.align                                                                     
    rvtest_check: 
      .word 0xdeadbeef                                                      # 1 for cause expected 0  for no cause 
      .word 0xbeefdead                                                      # write the value of mepc here (where  cause is expected)
      .word 0xcafecafe                                                      # write the value of expect cause 
.align 12                                     
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
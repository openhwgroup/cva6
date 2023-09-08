#=======================================================================
# RWX access on S-mode pages in S-mode for level1 PTE when pte.r=1, 
# pte.w=1, pte.x=1 
#-----------------------------------------------------------------------
# Test Description:
#
# If PTE belongs to supervisor mode i.e. its U permission bit is clear
# (pte.u = 0), then accessing that PTE in supervisor mode should be
# successful if the corresponding (r,w,x) permission of PTE is granted.
# Otherwise raise page fault exception of the corresponding access type.
# 
# When satp.mode=sv32, PTE has (r,w,x) PMP permissions, PTE has 
# non-reserved RWX encoding, pte.u=0 and pte.v=1, then test the 
# following in supervisor privilege mode for level 0 and level 1 PTE.
# 
# - Test the read access for pte.r=1 
# - Test the write access for pte.w=1
# - Test the execute access for pte.x=1 
# 
#=======================================================================

#include "macros.h"
#define _MMODE_ "M"
#define _SUMODE_ "SU"

.text
.global _start
.option norvc

_start:

    ALL_MEM_PMP                                                             # PMP permission to all the memory
    la t1,trap_handler                                                      # loads the address of trap handler 
    csrw mtvec,t1                                                           # sets the mtvec to trap handler 
    
# --------LEVEL 1 PTE Setup for load and store and execute access-------

    la a1,vm_en                                                             # loads the address of label vm_en
    mv a0, a1                                                               # set the VA to PA (identity mapping)
    ori a2, x0, ( PTE_D | PTE_A | PTE_X | PTE_V )                           # sets the permission bits
    PTE_SETUP_RV32 ( a1, a2, t1, a0, pgtb_l1, LEVEL1 )                      # setup the PTE for level1
 
    la a1,rvtest_data                                                       # loads the address of label rvtest_data
    mv a0, a1                                                               # set the VA to PA (identity mapping)
    ori a2, x0,( PTE_D | PTE_A | PTE_W | PTE_R | PTE_V)                     # sets the permission bits
    PTE_SETUP_RV32(a1, a2, t1, a0, pgtb_l1, LEVEL1)                         # setup the PTE for level1   

    la a1,rvtest_check                                                      # loads the address of label rvtest_check
    mv a0, a1                                                               # set the VA to PA (identity mapping)                                          
    ori a2, x0, ( PTE_D | PTE_A | PTE_W | PTE_R | PTE_V )                   # sets the permission bits
    PTE_SETUP_RV32(a1, a2, t1, a0, pgtb_l1, LEVEL1)                         # setup the PTE for level1

# ----------------Set the SATP and change the mode----------------------

    SATP_SETUP_SV32(pgtb_l1)                                                # set the SATP for virtualization
    la a1,vm_en                                                             # loads the address of vm_en
																													 
    CHANGE_T0_S_MODE(a1)                                        	        # changes mode M to S and set the MEPC value to a1

# ----------------Virtualization Enabeled-------------------------------
vm_en:

    la a1, rvtest_data                                                      # loads the address of label rvtest_data

check_store:

    sw t1,0(a1)                                                             # test the store access
        
check_load:

    lw t1,0(a1)                                                             # tests the load access 

check_execute:
   
    li t1, 0x45                                                             # test the execute access
    SMODE_ECALL                                                             # to go back to M mode
    j test_pass
    
trap_handler:

    csrr t0, mcause                                                         # read the value of mcause 
    la t1, rvtest_check                                                     # load the address of trvtest_check
    
    lw t2, 0(t1)                                                            # if cause expected then load 1 else 0
    lw t3, 4(t1)                                                            # load the expected value of mepc 
    lw t4, 8(t1)                                                            # load the expected value of mcause  

    li  t1, CAUSE_SUPERVISOR_ECALL                                          # load the value of supervisor ecall
    beq t0,t1,continue_in_m_mode                                            # checks if ecall is occured

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

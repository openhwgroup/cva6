/*
**
** Copyright 2020 OpenHW Group
**
** Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
** you may not use this file except in compliance with the License.
** You may obtain a copy of the License at
**
**     https://solderpad.org/licenses/
**
** Unless required by applicable law or agreed to in writing, software
** distributed under the License is distributed on an "AS IS" BASIS,
** WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
** See the License for the specific language governing permissions and
** limitations under the License.
**
** SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
**
*******************************************************************************
**
** Performance counter directed test
**
** Very basic sanity check for:
**
**  - Count load use hazards
**  - Count jump register hazards
**  - Count memory read transactions
**  - Count memory write transactions
**  - Count jumps
**  - Count branches (conditional)
**  - Count branches taken (conditional)
**  - Compressed instructions
**  - Retired instructions
**
** Make sure to instantiate cv32e40s_wrapper with the parameter
** NUM_MHPMCOUNTERS = 1 (or higher)
**
*******************************************************************************
*/

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAX_STALL_CYCLES 5

static int chck(unsigned int is, unsigned int should)
{
  int err;
  err = is == should ? 0 : 1;
  if (err)
    printf("fail\n");
  else
    printf("pass\n");
  return err;
}

static int chck_le(unsigned int is, unsigned int should)
{
  int err;
  err = is <= should ? 0 : 1;
  if (err)
    printf("fail\n");
  else
    printf("pass\n");
  return err;
}

static int chck_with_pos_margin(unsigned int is, unsigned int should, unsigned int margin)
{
  int err;
  err = (is >= should) && (is <= should + margin) ? 0 : 1;
  if (err)
    printf("fail\n");
  else
    printf("pass\n");
  return err;
}

int main(int argc, char *argv[])
{
  int err_cnt = 0;

  enum event_e { EVENT_CYCLES        = 1 << 0,
                 EVENT_INSTR         = 1 << 1,
                 EVENT_COMP_INSTR    = 1 << 2,
                 EVENT_JUMP          = 1 << 3,
                 EVENT_BRANCH        = 1 << 4,
                 EVENT_BRANCH_TAKEN  = 1 << 5,
                 EVENT_INTR_TAKEN    = 1 << 6,
                 EVENT_DATA_READ     = 1 << 7,
                 EVENT_DATA_WRITE    = 1 << 8,
                 EVENT_IF_INVALID    = 1 << 9,
                 EVENT_ID_INVALID    = 1 << 10,
                 EVENT_EX_INVALID    = 1 << 11,
                 EVENT_WB_INVALID    = 1 << 12,
                 EVENT_ID_LD_STALL   = 1 << 13,
                 EVENT_ID_JMP_STALL  = 1 << 14,
                 EVENT_WB_DATA_STALL = 1 << 15 };

  volatile unsigned int event;
  volatile unsigned int count;
  volatile unsigned int minstret;
  volatile unsigned int count_while_on;

  volatile unsigned int mcycle_count;

  __asm__ volatile(".option rvc");

  //////////////////////////////////////////////////////////////
  // Cycle count
  printf("\nCycle count");

  // Setup events and set csrs to 0
  event = EVENT_CYCLES;
  __asm__ volatile("csrw 0x323, %0 " :: "r"(event));
  __asm__ volatile("csrwi 0xB00, 0x0");
  __asm__ volatile("csrwi 0xB02, 0x0");
  __asm__ volatile("csrwi 0xB03, 0x0");

  // Readback Counter to verify 0
  __asm__ volatile("csrr %0, 0xB00" : "=r"(mcycle_count));
  __asm__ volatile("csrr %0, 0xB02" : "=r"(minstret));
  __asm__ volatile("csrr %0, 0xB03" : "=r"(count));
  printf("\nCheck proper zeroization\n");
  err_cnt += chck(minstret, 0);
  err_cnt += chck(count, 0);
  err_cnt += chck(count, mcycle_count);

  // Enable counters
  __asm__ volatile("csrwi 0x320, 0x0");

  __asm__ volatile("csrr t0, minstret\n\t\
                    addi t1, x0, 0\n\t\
                    addi t2, x0, 0" \
                    : : : "t0", "t1", "t2");

  __asm__ volatile("csrwi 0x320, 0x1F");
  __asm__ volatile("csrr %0, 0xB00" : "=r"(mcycle_count));
  __asm__ volatile("csrr %0, 0xB02" : "=r"(minstret));
  __asm__ volatile("csrr %0, 0xB03" : "=r"(count));

  printf("\nminstret count = %d\n", minstret);
  err_cnt += chck(minstret, 4);
  printf("\nCycle count while running = %d", count);
  printf("\nMCYCLE counted cycles = %d\n", mcycle_count);
  err_cnt += chck(count, mcycle_count);
  err_cnt += chck_with_pos_margin(count, 6, 4*MAX_STALL_CYCLES);

  //////////////////////////////////////////////////////////////
  // IF_INVALID
  printf("\nIF_INVALID");

  event = EVENT_IF_INVALID;
  __asm__ volatile("csrw 0x323, %0 " :: "r"(event));
  __asm__ volatile("csrwi 0xB02, 0x0");
  __asm__ volatile("csrwi 0xB03, 0x0");
  __asm__ volatile("csrwi 0x320, 0x0");

  __asm__ volatile("addi t1, x0, 0\n\t\
                    addi t0, x0, 5\n\t\
                    branch_target_ifinv_1: addi t1, t1, 1\n\t\
                    bne t0, t1, branch_target_ifinv_1\n\t\
                    nop" \
                    : : : "t0", "t1");

  __asm__ volatile("csrwi 0x320, 0x1F");
  __asm__ volatile("csrr %0, 0xB02" : "=r"(minstret));
  __asm__ volatile("csrr %0, 0xB03" : "=r"(count));

  printf("\nminstret count = %d\n", minstret);
  err_cnt += chck(minstret, 4+(2*5));
  printf("\nUnderutilized cycles on ID-stage due to IF stage = %d\n", count);

  err_cnt += chck_with_pos_margin(count, 4, (4 /*non looped*/ +
                                             5 /*looped addi*/ +
                                             4*2 /*taken branches, potenially misaligned*/ +
                                             2 /*non-taken, potentially misaligned*/)*MAX_STALL_CYCLES);

  //////////////////////////////////////////////////////////////
  // ID_INVALID - LD_STALL
  printf("\nID_INVALID");
  event = EVENT_ID_INVALID;
  __asm__ volatile("csrw 0x323, %0 " :: "r"(event));
  __asm__ volatile("csrwi 0xB02, 0x0");
  __asm__ volatile("csrwi 0xB03, 0x0");
  __asm__ volatile("csrwi 0x320, 0x0");

  __asm__ volatile("lw x4, 0(sp)\n\t\
                    addi x5, x4, 1\n\t\
                    lw x6, 0(sp)\n\t\
                    addi x7, x0, 1" \
                    : : : "x4", "x5", "x6", "x7");

  __asm__ volatile("csrwi 0x320, 0x1F");
  __asm__ volatile("csrr %0, 0xB02" : "=r"(minstret));
  __asm__ volatile("csrr %0, 0xB03" : "=r"(count));

  printf("\nminstret count = %d\n", minstret);
  err_cnt += chck(minstret, 5);
  printf("\nUnderutilized cycles on EX-stage due to ID stage = %d\n", count);
  err_cnt += chck_with_pos_margin(count, 2, 5*MAX_STALL_CYCLES);

  //////////////////////////////////////////////////////////////
  // ID_INVALID - JR STALL
  printf("\nID_INVALID");
  event = EVENT_ID_INVALID;
  __asm__ volatile("csrw 0x323, %0 " :: "r"(event));
  __asm__ volatile("csrwi 0xB02, 0x0");
  __asm__ volatile("csrwi 0xB03, 0x0");
  __asm__ volatile("csrwi 0x320, 0x0");

  __asm__ volatile("auipc x4, 0\n\t\
                    jalr x0, x4, 8\n\t\
                    nop" \
                    : : : "x4");

  __asm__ volatile("csrwi 0x320, 0x1F");
  __asm__ volatile("csrr %0, 0xB02" : "=r"(minstret));
  __asm__ volatile("csrr %0, 0xB03" : "=r"(count));

  printf("\nminstret count = %d\n", minstret);
  err_cnt += chck(minstret, 4);
  printf("\nUnderutilized cycles on EX-stage due to ID stage = %d\n", count);
  err_cnt += chck_with_pos_margin(count, 3, 4*MAX_STALL_CYCLES);

  //////////////////////////////////////////////////////////////
  // EX_INVALID
  printf("\nEX_INVALID");
  event = EVENT_EX_INVALID;
  __asm__ volatile("csrw 0x323, %0 " :: "r"(event));

  __asm__ volatile("csrwi 0xB02, 0x0");
  __asm__ volatile("csrwi 0xB03, 0x0");
  __asm__ volatile("csrwi 0x320, 0x0");

  __asm__ volatile("lw x0, 0(x0)");
  __asm__ volatile("lw x31, 0(x31)");
  __asm__ volatile("lw x30, 0(x30)");
  __asm__ volatile("lw x29, 0(x29)");
  __asm__ volatile("lw x28, 0(x28)");
  __asm__ volatile("mulh x0, x0, x0");                            // 3 cycles
  __asm__ volatile("li x31, 4");
  __asm__ volatile("li x30, 3");
  __asm__ volatile("mulh x0, x31, x30");                          // 3 cycles
  __asm__ volatile("li x31, 9");
  __asm__ volatile("li x30, 7");;
  __asm__ volatile("mulh x0, x31, x30");                          // 3 cycles
  __asm__ volatile("li x31, 47");
  __asm__ volatile("li x30, 17");
  __asm__ volatile("div x0, x31, x30");                           // 32 cycles
  __asm__ volatile("li x31, 1");
  __asm__ volatile("li x30, 1");
  __asm__ volatile("div x0, x31, x30");                           // 32 cycles
  __asm__ volatile("rem x0, x31, x30");                           // 32 cycles
  __asm__ volatile("lw x0, 0(sp)");

  __asm__ volatile("csrwi 0x320, 0x1F");
  __asm__ volatile("csrr %0, 0xB02" : "=r"(minstret));
  __asm__ volatile("csrr %0, 0xB03" : "=r"(count));

  printf("\nminstret count = %d\n", minstret);
  err_cnt += chck(minstret, 21);
  printf("\nUnderutilized cycles on WB-stage due to EX stage = %d\n", count);
  // -6 due to potential random stalls preventing hazard stalls
  err_cnt += chck_with_pos_margin(count, 104 - 6, 21*MAX_STALL_CYCLES + 6);

  //////////////////////////////////////////////////////////////
  // WB_INVALID Write port underutilization

  printf("\nWrite port underutilization");
  event = EVENT_WB_INVALID;
  __asm__ volatile("csrw 0x323, %0 " :: "r"(event));            // Set mphmevent3
  __asm__ volatile("csrwi 0xB02, 0x0");                         // minstret = 0
  __asm__ volatile("csrwi 0xB03, 0x0");                         // mhpmcounter3 = 0
  __asm__ volatile("csrwi 0x320, 0x0");                         // Enable counters

  __asm__ volatile("li x31, 1\n\t\
                    li x30, 1\n\t\
                    div x0, x31, x30\n\t\
                    lw x29, 0(sp)\n\t\
                    sw x29, 0(sp)" \
                    : : : "x28", "x29", "x30", "x31");

  __asm__ volatile("csrwi 0x320, 0x1F");                        // Inhibit mcycle, minstret, mhpmcounter3-4
  __asm__ volatile("csrr %0, 0xB02" : "=r"(minstret));
  __asm__ volatile("csrr %0, 0xB03" : "=r"(count));             // mhpmcounter3

  printf("\nminstret count = %d\n", minstret);
  err_cnt += chck(minstret, 6);
  printf("\nWrite port underutilization cycles: %d\n", count);
  err_cnt += chck_with_pos_margin(count, 34, 6*MAX_STALL_CYCLES);

  //////////////////////////////////////////////////////////////
  // WB_DATA_STALL Write port underutilization due to data_rvalid_i (0)
  printf("\nWrite port underutilization due to data_rvalid_i");
  event = EVENT_WB_DATA_STALL;

  __asm__ volatile("csrw 0x323, %0 " :: "r"(event));            // Set mphmevent3
  __asm__ volatile("csrwi 0xB02, 0x0");                         // minstret = 0
  __asm__ volatile("csrwi 0xB03, 0x0");                         // mhpmcounter3 = 0
  __asm__ volatile("csrwi 0x320, 0x0");                         // Enable counters

  __asm__ volatile("li x31, 7\n\t\
                    li x30, 3\n\t\
                    addi x0, x31, 1\n\t\
                    lw x29, 0(sp)\n\t\
                    lw x28, -1(sp)\n\t\
                    srli x30, x29, 2\n\t\
                    slli x30, x30, 2\n\t\
                    xori x30, x30, 1\n\t\
                    sw x29, 0(x30)\n\t\
                    sw x29, 0(sp)\n\t\
                    lw x28, -1(sp)\n\t\
                    csrr x29, 0xB00\n\t\
                    div x0, x31, x30" \
                    : : : "x28", "x29", "x30", "x31");

  __asm__ volatile("csrwi 0x320, 0x1F");                        // Inhibit mcycle, minstret, mhpmcounter3-4
  __asm__ volatile("csrr %0, 0xB02" : "=r"(minstret));
  __asm__ volatile("csrr %0, 0xB03" : "=r"(count));             // mhpmcounter3

  printf("\nminstret count = %d\n", minstret);
  err_cnt += chck(minstret, 14);
  printf("\nWrite port underutilization cycles: %d\n", count);
  err_cnt += chck_with_pos_margin(count, 3, 14*MAX_STALL_CYCLES);

  //////////////////////////////////////////////////////////////
  // Retired instruction count (0) - Immediate minstret read
  printf("\nRetired instruction count (0)");

  event = EVENT_INSTR;                                          // Trigger on retired instructions
  __asm__ volatile("csrw 0x323, %0 " :: "r"(event));            // Set mphmevent3
  __asm__ volatile("csrwi 0xB02, 0x0");                         // minstret = 0
  __asm__ volatile("csrwi 0xB03, 0x0");                         // mhpmcounter3 = 0
  __asm__ volatile("csrwi 0x320, 0x0");                         // Enable counters

  __asm__ volatile("csrr t0, minstret\n\t\
                    addi t1, x0, 0\n\t\
                    addi t2, x0, 0" \
                    : : : "t0", "t1", "t2");
  __asm__ volatile("csrwi 0x320, 0x1F");                        // Inhibit mcycle, minstret, mhpmcounter3-4
  __asm__ volatile("csrr %0, 0xB02" : "=r"(minstret));          // minstret
  __asm__ volatile("csrr %0, 0xB03" : "=r"(count));             // mhpmcounter3
  __asm__ volatile("addi %0, t0, 0" : "=r"(count_while_on));    // count_while_on

  printf("\nminstret count while running = %d\n", count_while_on);
  err_cnt += chck(count_while_on, 0);

  printf("\nminstret count = %d\n", minstret);
  err_cnt += chck(minstret, 4);

  //////////////////////////////////////////////////////////////
  // Retired instruction count (1) - minstret read-after-write
  printf("\nRetired instruction count (1)");

  event = EVENT_INSTR;                                          // Trigger on retired instructions
  __asm__ volatile("csrw 0x323, %0 " :: "r"(event));            // Set mphmevent3
  __asm__ volatile("csrwi 0xB02, 0x0");                         // minstret = 0
  __asm__ volatile("csrwi 0xB03, 0x0");                         // mhpmcounter3 = 0
  __asm__ volatile("csrwi 0x320, 0x0");                         // Enable counters
  __asm__ volatile("csrwi minstret, 0xA\n\t\
                    csrr t0, minstret\n\t\
                    addi t1, x0, 0\n\t\
                    addi t2, x0, 0\n\t\
                    nop" \
                    : : : "t0", "t1", "t2");
  __asm__ volatile("csrwi 0x320, 0x1F");                        // Inhibit mcycle, minstret, mhpmcounter3-4
  __asm__ volatile("csrr %0, 0xB02" : "=r"(minstret));          // minstret
  __asm__ volatile("csrr %0, 0xB03" : "=r"(count));             // mhpmcounter3
  __asm__ volatile("addi %0, t0, 0" : "=r"(count_while_on));    //

  printf("\nminstret count while running = %d\n", count_while_on);
  err_cnt += chck(count_while_on, 0xA);

  printf("\nminstret count = %d\n", minstret);
  err_cnt += chck(minstret, 0xF);

  //////////////////////////////////////////////////////////////
  // Retired instruction count (2)
  printf("\nRetired instruction count (2)");

  event = EVENT_INSTR;                                          // Trigger on retired instructions
  __asm__ volatile("csrw 0x323, %0 " :: "r"(event));            // Set mphmevent3
  __asm__ volatile("csrwi 0xB02, 0x0");                         // minstret = 0
  __asm__ volatile("csrwi 0xB03, 0x0");                         // mhpmcounter3 = 0
  __asm__ volatile("csrwi 0x320, 0x0");                         // Enable counters
  __asm__ volatile("sw x0, 0(sp)\n\t\
                    addi t0, x0, 5\n\t\
                    addi t1, x0, 0\n\t\
                    addi t2, x0, 0\n\t\
                    lw t2, 0(sp)\n\t\
                    branch_target: addi t2, t2, 1\n\t\
                    addi t1, t1, 1\n\t\
                    lw t2, 0(sp)\n\t\
                    sw t1, 0(sp)\n\t\
                    sw t1, 0(sp)\n\t\
                    bne t0, t1, branch_target\n\t\
                    j jump_target\n\t\
                    lw t2, 0(sp)\n\t\
                    lw t2, 0(sp)\n\t\
                    jump_target: nop\n\t\
                    nop\n\t\
                    nop" \
                    : : : "t0", "t1", "t2");
  __asm__ volatile("csrwi 0x320, 0x1F");                        // Inhibit mcycle, minstret, mhpmcounter3-4
  __asm__ volatile("csrr %0, 0xB02" : "=r"(minstret));          // minstret
  __asm__ volatile("csrr %0, 0xB03" : "=r"(count));             // mhpmcounter3

  printf("\nminstret count = %d\n", minstret);
  err_cnt += chck(minstret, 5 + 6*5 + 4 + 1);

  //////////////////////////////////////////////////////////////
  // Count load use hazards
  printf("\nCount load use hazards");

  event = EVENT_ID_LD_STALL;                                    // Trigger on load use hazards
  __asm__ volatile("csrw 0x323, %0 " :: "r"(event));            // Set mphmevent3
  __asm__ volatile("csrwi 0xB02, 0x0");                         // minstret = 0
  __asm__ volatile("csrwi 0xB03, 0x0");                         // mhpmcounter3 = 0
  __asm__ volatile("csrwi 0x320, 0x0");                         // Enable counters
  __asm__ volatile("lw x4, 0(sp)\n\t\
                    addi x5, x4, 1\n\t\
                    lw x6, 0(sp)\n\t\
                    addi x7, x0, 1" \
                    : : : "x4", "x5", "x6", "x7");
  __asm__ volatile("csrwi 0x320, 0x1F");                        // Inhibit mcycle, minstret, mhpmcounter3-4
  __asm__ volatile("csrr %0, 0xB02" : "=r"(minstret));          // minstret
  __asm__ volatile("csrr %0, 0xB03" : "=r"(count));             // mhpmcounter3

  printf("\nminstret count = %d\n", minstret);
  err_cnt += chck(minstret, 5);

  printf("Load use hazards count = %d\n", count);
  err_cnt += chck_le(count, 1);                                 // Hazard count is 0 or 1 (0 if due to instruction interface stalls 'use' did not closely follow the load)

  //////////////////////////////////////////////////////////////
  // Count jump register hazards
  printf("\nCount Jump register hazards");

  event = EVENT_ID_JMP_STALL;                                   // Trigger on jump register hazards
  __asm__ volatile("csrw 0x323, %0 " :: "r"(event));            // Set mphmevent3
  __asm__ volatile("csrwi 0xB02, 0x0");                         // minstret = 0
  __asm__ volatile("csrwi 0xB03, 0x0");                         // mhpmcounter3 = 0
  __asm__ volatile("csrwi 0x320, 0x0");                         // Enable counters
  __asm__ volatile("auipc x4, 0x0\n\t\
                    addi x4, x4, 10\n\t\
                    jalr x0, x4, 0x0" \
                    : : : "x4");
  __asm__ volatile("csrwi 0x320, 0x1F");                        // Inhibit mcycle, minstret, mhpmcounter3-4
  __asm__ volatile("csrr %0, 0xB02" : "=r"(minstret));          // minstret
  __asm__ volatile("csrr %0, 0xB03" : "=r"(count));             // mhpmcounter3

  printf("\nminstret count = %d\n", minstret);
  err_cnt += chck(minstret, 4);

  printf("Jump register hazards count = %d\n", count);
  err_cnt += chck_le(count, 1);                                 // Hazard count is 0 or 1 (0 if due to instruction interface stalls jalr did not closely follow the addi before it)

  //////////////////////////////////////////////////////////////
  // Count memory read transactions - Read while enabled
  printf("\nCount memory read transactions (0)");

  event = EVENT_DATA_READ;                                      // Trigger on loads
  __asm__ volatile("csrw 0x323, %0 " :: "r"(event));            // Set mphmevent3
  __asm__ volatile("csrwi 0xB02, 0x0");                         // minstret = 0
  __asm__ volatile("csrwi 0xB03, 0x0");                         // mhpmcounter3 = 0
  __asm__ volatile("csrwi 0x320, 0x0");                         // Enable counters
  __asm__ volatile("lw x0, 0(sp)\n\t\
                    csrr t0, mhpmcounter3\n\t\
                    addi t1, x0, 0\n\t\
                    addi t2, x0, 0" \
                    : : : "t0", "t1", "t2");
  __asm__ volatile("csrwi 0x320, 0x1F");                        // Inhibit mcycle, minstret, mhpmcounter3-4
  __asm__ volatile("csrr %0, 0xB02" : "=r"(minstret));          // minstret
  __asm__ volatile("csrr %0, 0xB03" : "=r"(count));             // mhpmcounter3
  __asm__ volatile("addi %0, t0, 0" : "=r"(count_while_on));    // count_while_on

  printf("\nminstret count = %d\n", minstret);
  err_cnt += chck(minstret, 5);

  printf("Load count while running = %d\n", count_while_on);
  err_cnt += chck(count_while_on, 1);

  printf("Load count = %d\n", count);
  err_cnt += chck(count, 1);

  //////////////////////////////////////////////////////////////
  // Count memory read transactions - Write after load event
  printf("\nCount memory read transactions (1)");

  event = EVENT_DATA_READ;                                      // Trigger on loads
  __asm__ volatile("csrw 0x323, %0 " :: "r"(event));            // Set mphmevent3
  __asm__ volatile("csrwi 0xB02, 0x0");                         // minstret = 0
  __asm__ volatile("csrwi 0xB03, 0x0");                         // mhpmcounter3 = 0
  __asm__ volatile("csrwi 0x320, 0x0");                         // Enable counters
  __asm__ volatile("lw x0, 0(sp)\n\t\
                    csrwi mhpmcounter3, 0xA\n\t\
                    addi t1, x0, 0\n\t\
                    addi t2, x0, 0" \
                    : : : "t0", "t1", "t2");
  __asm__ volatile("csrwi 0x320, 0x1F");                        // Inhibit mcycle, minstret, mhpmcounter3-4
  __asm__ volatile("csrr %0, 0xB02" : "=r"(minstret));          // minstret
  __asm__ volatile("csrr %0, 0xB03" : "=r"(count));             // mhpmcounter3
  __asm__ volatile("addi %0, t0, 0" : "=r"(count_while_on));    // count_while_on

  printf("\nminstret count = %d\n", minstret);
  err_cnt += chck(minstret, 5);

  printf("Load count = %d\n", count);
  err_cnt += chck(count, 0xA);

  //////////////////////////////////////////////////////////////
  // Count memory read transactions
  printf("\nCount memory read transactions (2)");

  event = EVENT_DATA_READ;                                      // Trigger on loads
  __asm__ volatile("csrw 0x323, %0 " :: "r"(event));            // Set mphmevent3
  __asm__ volatile("csrwi 0xB02, 0x0");                         // minstret = 0
  __asm__ volatile("csrwi 0xB03, 0x0");                         // mhpmcounter3 = 0
  __asm__ volatile("csrwi 0x320, 0x0");                         // Enable counters
  __asm__ volatile("lw x0, 0(sp)");                             // count++
  __asm__ volatile("mulh x0, x0, x0");
  __asm__ volatile("j jump_target_memread");                    // do not count jump in mphmevent3
  __asm__ volatile("nop");                                      // do not count nop in instret
  __asm__ volatile("jump_target_memread:");
  __asm__ volatile("lw x0, 0(sp)");                             // count++
  __asm__ volatile("csrwi 0x320, 0x1F");                        // Inhibit mcycle, minstret, mhpmcounter3-4
  __asm__ volatile("csrr %0, 0xB02" : "=r"(minstret));          // minstret
  __asm__ volatile("csrr %0, 0xB03" : "=r"(count));             // mhpmcounter3

  printf("\nminstret count = %d\n", minstret);
  err_cnt += chck(minstret, 5);

  printf("Load count = %d\n", count);
  err_cnt += chck(count, 2);

  //////////////////////////////////////////////////////////////
  // Count memory write transactions
  printf("\nCount memory write transactions");

  event = EVENT_DATA_WRITE;                                     // Trigger on stores
  __asm__ volatile("csrw 0x323, %0 " :: "r"(event));            // Set mphmevent3
  __asm__ volatile("csrwi 0xB02, 0x0");                         // minstret = 0
  __asm__ volatile("csrwi 0xB03, 0x0");                         // mhpmcounter3 = 0
  __asm__ volatile("csrwi 0x320, 0x0");                         // Enable counters
  __asm__ volatile("sw x0, 0(sp)");                             // count++
  __asm__ volatile("mulh x0, x0, x0");
  __asm__ volatile("sw x0, 0(sp)");                             // count++
  __asm__ volatile("csrwi 0x320, 0x1F");                        // Inhibit mcycle, minstret, mhpmcounter3-4
  __asm__ volatile("csrr %0, 0xB02" : "=r"(minstret));          // minstret
  __asm__ volatile("csrr %0, 0xB03" : "=r"(count));             // mhpmcounter3

  printf("\nminstret count = %d\n", minstret);
  err_cnt += chck(minstret, 4);

  printf("Store count = %d\n", count);
  err_cnt += chck(count, 2);

  //////////////////////////////////////////////////////////////
  // Count jumps
  printf("\nCount jumps");

  event = EVENT_JUMP;                                           // Trigger on jumps
  __asm__ volatile("csrw 0x323, %0 " :: "r"(event));            // Set mphmevent3
  __asm__ volatile("csrwi 0xB02, 0x0");                         // minstret = 0
  __asm__ volatile("csrwi 0xB03, 0x0");                         // mhpmcounter3 = 0
  __asm__ volatile("csrwi 0x320, 0x0");                         // Enable counters
  __asm__ volatile("j jump_target_0");                          // count++
  __asm__ volatile("jump_target_0:");
  __asm__ volatile("j jump_target_1");                          // count++
  __asm__ volatile("jump_target_1:");
  __asm__ volatile("csrwi 0x320, 0x1F");                        // Inhibit mcycle, minstret, mhpmcounter3-4
  __asm__ volatile("csrr %0, 0xB02" : "=r"(minstret));          // minstret
  __asm__ volatile("csrr %0, 0xB03" : "=r"(count));             // mhpmcounter3

  printf("\nminstret count = %d\n", minstret);
  err_cnt += chck(minstret, 3);

  printf("Jump count = %d\n", count);
  err_cnt += chck(count, 2);

  //////////////////////////////////////////////////////////////
  // Count branches (conditional)
  printf("\nCount branches (conditional)");

  event = EVENT_BRANCH;                                         // Trigger on on taken branches
  __asm__ volatile("csrw 0x323, %0 " :: "r"(event));            // Set mphmevent3
  __asm__ volatile("csrwi 0xB02, 0x0");                         // minstret = 0
  __asm__ volatile("csrwi 0xB03, 0x0");                         // mhpmcounter3 = 0
  __asm__ volatile("csrwi 0x320, 0x0");                         // Enable counters
  __asm__ volatile("beq x0, x0, branch_target_0");              // count++
  __asm__ volatile("branch_target_0:");
  __asm__ volatile("bne x0, x0, branch_target_1");              // count++
  __asm__ volatile("branch_target_1:");
  __asm__ volatile("beq x0, x0, branch_target_2");              // count++
  __asm__ volatile("branch_target_2:");
  __asm__ volatile("csrwi 0x320, 0x1F");                        // Inhibit mcycle, minstret, mhpmcounter3-4
  __asm__ volatile("csrr %0, 0xB02" : "=r"(minstret));          // minstret
  __asm__ volatile("csrr %0, 0xB03" : "=r"(count));             // mhpmcounter3

  printf("\nminstret count = %d\n", minstret);
  err_cnt += chck(minstret, 4);

  printf("Branch count = %d\n", count);
  err_cnt += chck(count, 3);

  //////////////////////////////////////////////////////////////
  // Count branches taken (conditional)
  printf("\nCount branches taken (conditional)");

  event = EVENT_BRANCH_TAKEN;                                   // Trigger on on taken branches
  __asm__ volatile("csrw 0x323, %0 " :: "r"(event));            // Set mphmevent3
  __asm__ volatile("csrwi 0xB02, 0x0");                         // minstret = 0
  __asm__ volatile("csrwi 0xB03, 0x0");                         // mhpmcounter3 = 0
  __asm__ volatile("csrwi 0x320, 0x0");                         // Enable counters
  __asm__ volatile("beq x0, x0, branch_target_3");              // count++
  __asm__ volatile("branch_target_3:");
  __asm__ volatile("bne x0, x0, branch_target_4");              // (not taken)
  __asm__ volatile("branch_target_4:");
  __asm__ volatile("beq x0, x0, branch_target_5");              // count++
  __asm__ volatile("branch_target_5:");
  __asm__ volatile("csrwi 0x320, 0x1F");                        // Inhibit mcycle, minstret, mhpmcounter3-4
  __asm__ volatile("csrr %0, 0xB02" : "=r"(minstret));          // minstret
  __asm__ volatile("csrr %0, 0xB03" : "=r"(count));             // mhpmcounter3

  printf("\nminstret count = %d\n", minstret);
  err_cnt += chck(minstret, 4);

  printf("Branch taken count = %d\n", count);
  err_cnt += chck(count, 2);

  //////////////////////////////////////////////////////////////
  // Compressed instructions
  printf("\nCompressed instructions");

  event = EVENT_COMP_INSTR;                                     // Trigger on compressed instructions
  __asm__ volatile("csrw 0x323, %0 " :: "r"(event));            // Set mphmevent3
  __asm__ volatile("csrwi 0xB02, 0x0");                         // minstret = 0
  __asm__ volatile("csrwi 0xB03, 0x0");                         // mhpmcounter3 = 0
  __asm__ volatile("csrwi 0x320, 0x0");                         // Enable counters
  __asm__ volatile("c.addi x15, 1\n\t\
                    c.nop\n\t\
                    c.addi x15, 1" \
                    : : : "x15");
  __asm__ volatile("csrwi 0x320, 0x1F");                        // Inhibit mcycle, minstret, mhpmcounter3-4
  __asm__ volatile("csrr %0, 0xB02" : "=r"(minstret));          // minstret
  __asm__ volatile("csrr %0, 0xB03" : "=r"(count));             // mhpmcounter3

  printf("\nminstret count = %d\n", minstret);
  err_cnt += chck(minstret, 4);

  printf("Compressed count = %d\n", count);
  err_cnt += chck(count, 3);

  //////////////////////////////////////////////////////////////
  // Check for errors
  printf("\nDone\n\n");

  if (err_cnt)
    printf("FAILURE. %d errors\n\n", err_cnt);
  else
    printf("SUCCESS\n\n");

  return err_cnt;
}

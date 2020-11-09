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
** Make sure to instantiate cv32e40p_wrapper with the parameter
** NUM_MHPMCOUNTERS = 1 (or higher)
**
*******************************************************************************
*/

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

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

int main(int argc, char *argv[])
{
  int err_cnt = 0;

  volatile unsigned int event;
  volatile unsigned int count;
  volatile unsigned int minstret;
  volatile unsigned int count_while_on;

  __asm__ volatile(".option rvc");

  //////////////////////////////////////////////////////////////
  // Retired instruction count (0) - Immediate minstret read
  printf("\nRetired instruction count (0)");

  event = 0x2;                                                  // Trigger on retired instructions
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

  event = 0x2;                                                  // Trigger on retired instructions
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

  event = 0x2;                                                  // Trigger on retired instructions
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

  event = 0x4;                                                  // Trigger on load use hazards
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

  event = 0x8;                                                  // Trigger on jump register hazards
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

  event = 0x20;                                                 // Trigger on loads
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

  event = 0x20;                                                 // Trigger on loads
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

  event = 0x20;                                                 // Trigger on loads
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

  event = 0x40;                                                 // Trigger on stores
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

  event = 0x80;                                                 // Trigger on jumps
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

  event = 0x100;                                                // Trigger on on taken branches
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

  event = 0x200;                                                // Trigger on on taken branches
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

  event = 0x400;                                                // Trigger on compressed instructions
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
  printf("\nDone");

  if (err_cnt)
    printf("FAILURE. %d errors\n\n", err_cnt);
  else
    printf("SUCCESS\n\n");

  return err_cnt;
}

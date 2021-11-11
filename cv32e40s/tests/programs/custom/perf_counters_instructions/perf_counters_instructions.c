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
*******************************************************************************
**
** Performance Counters Basic  test:
**
*******************************************************************************
                    //lw x8, 4(sp)\n\t\
                    //lh x8, 4(sp)\n\t\
                    //lhu x8, 4(sp)\n\t\
                    //lb x8, 4(sp)\n\t\
                    //lbu x8, 4(sp)\n\t\
*/

#include <stdio.h>
#include <stdlib.h>

#ifndef NUM_MPHMCOUNTERS
#define NUM_MHPMCOUNTERS 1
#endif

static int chck(unsigned int is, unsigned int should)
{
  int err;
  err = is == should ? 0 : 1;
  if (err)
    printf("fail %d %d\n", is, should);
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

  volatile unsigned int mcycle_rval;
  volatile unsigned int minstret_rval;
  volatile unsigned int mcountinhibit_rval;
  volatile unsigned int mhpmcounter_rval[32];
  volatile unsigned int mhpmevent_rval[32];
  volatile unsigned int mhartid_rval;
  volatile unsigned int sum;
  volatile unsigned int count;
  volatile unsigned int event;
  volatile unsigned int err_cnt;

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


  __asm__ volatile(".option rvc");

  sum = 0;
  err_cnt = 0;
  count = 0;
  event = 0;

  unsigned int writable_counters_l = 0;
  unsigned int writable_counters_h = 0;
  unsigned int temp_readable;

  // Check number of implemented counters
  // and test read/write by reading and writing all bits of
  // the respective counter CSRs - verify that the
  // read CSRs that are nonzero match up with the bits read
  // from mcountinhibit
  __asm__ volatile("addi t1, x0, 0xFFFFFFFF");
  __asm__ volatile("csrrw x0, 0x320, t1");

  __asm__ volatile("csrw 0xB03, t1");
  __asm__ volatile("csrw 0xB04, t1");
  __asm__ volatile("csrw 0xB05, t1");
  __asm__ volatile("csrw 0xB06, t1");
  __asm__ volatile("csrw 0xB07, t1");
  __asm__ volatile("csrw 0xB08, t1");
  __asm__ volatile("csrw 0xB09, t1");
  __asm__ volatile("csrw 0xB0A, t1");
  __asm__ volatile("csrw 0xB0B, t1");
  __asm__ volatile("csrw 0xB0C, t1");
  __asm__ volatile("csrw 0xB0D, t1");
  __asm__ volatile("csrw 0xB0E, t1");
  __asm__ volatile("csrw 0xB0F, t1");
  __asm__ volatile("csrw 0xB10, t1");
  __asm__ volatile("csrw 0xB11, t1");
  __asm__ volatile("csrw 0xB12, t1");
  __asm__ volatile("csrw 0xB13, t1");
  __asm__ volatile("csrw 0xB14, t1");
  __asm__ volatile("csrw 0xB15, t1");
  __asm__ volatile("csrw 0xB16, t1");
  __asm__ volatile("csrw 0xB17, t1");
  __asm__ volatile("csrw 0xB18, t1");
  __asm__ volatile("csrw 0xB19, t1");
  __asm__ volatile("csrw 0xB1A, t1");
  __asm__ volatile("csrw 0xB1B, t1");
  __asm__ volatile("csrw 0xB1C, t1");
  __asm__ volatile("csrw 0xB1D, t1");
  __asm__ volatile("csrw 0xB1E, t1");
  __asm__ volatile("csrw 0xB1F, t1");

  __asm__ volatile("csrw 0xB83, t1");
  __asm__ volatile("csrw 0xB84, t1");
  __asm__ volatile("csrw 0xB85, t1");
  __asm__ volatile("csrw 0xB86, t1");
  __asm__ volatile("csrw 0xB87, t1");
  __asm__ volatile("csrw 0xB88, t1");
  __asm__ volatile("csrw 0xB89, t1");
  __asm__ volatile("csrw 0xB8A, t1");
  __asm__ volatile("csrw 0xB8B, t1");
  __asm__ volatile("csrw 0xB8C, t1");
  __asm__ volatile("csrw 0xB8D, t1");
  __asm__ volatile("csrw 0xB8E, t1");
  __asm__ volatile("csrw 0xB8F, t1");
  __asm__ volatile("csrw 0xB90, t1");
  __asm__ volatile("csrw 0xB91, t1");
  __asm__ volatile("csrw 0xB92, t1");
  __asm__ volatile("csrw 0xB93, t1");
  __asm__ volatile("csrw 0xB94, t1");
  __asm__ volatile("csrw 0xB95, t1");
  __asm__ volatile("csrw 0xB96, t1");
  __asm__ volatile("csrw 0xB97, t1");
  __asm__ volatile("csrw 0xB98, t1");
  __asm__ volatile("csrw 0xB99, t1");
  __asm__ volatile("csrw 0xB9A, t1");
  __asm__ volatile("csrw 0xB9B, t1");
  __asm__ volatile("csrw 0xB9C, t1");
  __asm__ volatile("csrw 0xB9D, t1");
  __asm__ volatile("csrw 0xB9E, t1");
  __asm__ volatile("csrw 0xB9F, t1");

  __asm__ volatile("addi x0, %0, 0" : "=r"(temp_readable));
  __asm__ volatile("csrr %0, 0xB03" : "=r"(temp_readable));
  writable_counters_l = temp_readable ? writable_counters_l | (1 << 3) : writable_counters_l;
  __asm__ volatile("addi x0, %0, 0" : "=r"(temp_readable));
  __asm__ volatile("csrr t1, 0xB04" : "=r"(temp_readable));
  writable_counters_l = temp_readable ? writable_counters_l | (1 << 4) : writable_counters_l;
  __asm__ volatile("addi x0, %0, 0" : "=r"(temp_readable));
  __asm__ volatile("csrr t1, 0xB05" : "=r"(temp_readable));
  writable_counters_l = temp_readable ? writable_counters_l | (1 << 5) : writable_counters_l;
  __asm__ volatile("addi x0, %0, 0" : "=r"(temp_readable));
  __asm__ volatile("csrr t1, 0xB06" : "=r"(temp_readable));
  writable_counters_l = temp_readable ? writable_counters_l | (1 << 6) : writable_counters_l;
  __asm__ volatile("addi x0, %0, 0" : "=r"(temp_readable));
  __asm__ volatile("csrr t1, 0xB07" : "=r"(temp_readable));
  writable_counters_l = temp_readable ? writable_counters_l | (1 << 7) : writable_counters_l;
  __asm__ volatile("addi x0, %0, 0" : "=r"(temp_readable));
  __asm__ volatile("csrr t1, 0xB08" : "=r"(temp_readable));
  writable_counters_l = temp_readable ? writable_counters_l | (1 << 8) : writable_counters_l;
  __asm__ volatile("addi x0, %0, 0" : "=r"(temp_readable));
  __asm__ volatile("csrr t1, 0xB09" : "=r"(temp_readable));
  writable_counters_l = temp_readable ? writable_counters_l | (1 << 9) : writable_counters_l;
  __asm__ volatile("addi x0, %0, 0" : "=r"(temp_readable));
  __asm__ volatile("csrr t1, 0xB0A" : "=r"(temp_readable));
  writable_counters_l = temp_readable ? writable_counters_l | (1 << 10) : writable_counters_l;
  __asm__ volatile("addi x0, %0, 0" : "=r"(temp_readable));
  __asm__ volatile("csrr t1, 0xB0B" : "=r"(temp_readable));
  writable_counters_l = temp_readable ? writable_counters_l | (1 << 11) : writable_counters_l;
  __asm__ volatile("addi x0, %0, 0" : "=r"(temp_readable));
  __asm__ volatile("csrr t1, 0xB0C" : "=r"(temp_readable));
  writable_counters_l = temp_readable ? writable_counters_l | (1 << 12) : writable_counters_l;
  __asm__ volatile("addi x0, %0, 0" : "=r"(temp_readable));
  __asm__ volatile("csrr t1, 0xB0D" : "=r"(temp_readable));
  writable_counters_l = temp_readable ? writable_counters_l | (1 << 13) : writable_counters_l;
  __asm__ volatile("addi x0, %0, 0" : "=r"(temp_readable));
  __asm__ volatile("csrr t1, 0xB0E" : "=r"(temp_readable));
  writable_counters_l = temp_readable ? writable_counters_l | (1 << 14) : writable_counters_l;
  __asm__ volatile("addi x0, %0, 0" : "=r"(temp_readable));
  __asm__ volatile("csrr t1, 0xB0F" : "=r"(temp_readable));
  writable_counters_l = temp_readable ? writable_counters_l | (1 << 15) : writable_counters_l;
  __asm__ volatile("addi x0, %0, 0" : "=r"(temp_readable));
  __asm__ volatile("csrr t1, 0xB10" : "=r"(temp_readable));
  writable_counters_l = temp_readable ? writable_counters_l | (1 << 16) : writable_counters_l;
  __asm__ volatile("addi x0, %0, 0" : "=r"(temp_readable));
  __asm__ volatile("csrr t1, 0xB11" : "=r"(temp_readable));
  writable_counters_l = temp_readable ? writable_counters_l | (1 << 17) : writable_counters_l;
  __asm__ volatile("addi x0, %0, 0" : "=r"(temp_readable));
  __asm__ volatile("csrr t1, 0xB12" : "=r"(temp_readable));
  writable_counters_l = temp_readable ? writable_counters_l | (1 << 18) : writable_counters_l;
  __asm__ volatile("addi x0, %0, 0" : "=r"(temp_readable));
  __asm__ volatile("csrr t1, 0xB13" : "=r"(temp_readable));
  writable_counters_l = temp_readable ? writable_counters_l | (1 << 19) : writable_counters_l;
  __asm__ volatile("addi x0, %0, 0" : "=r"(temp_readable));
  __asm__ volatile("csrr t1, 0xB14" : "=r"(temp_readable));
  writable_counters_l = temp_readable ? writable_counters_l | (1 << 20) : writable_counters_l;
  __asm__ volatile("addi x0, %0, 0" : "=r"(temp_readable));
  __asm__ volatile("csrr t1, 0xB15" : "=r"(temp_readable));
  writable_counters_l = temp_readable ? writable_counters_l | (1 << 21) : writable_counters_l;
  __asm__ volatile("addi x0, %0, 0" : "=r"(temp_readable));
  __asm__ volatile("csrr t1, 0xB16" : "=r"(temp_readable));
  writable_counters_l = temp_readable ? writable_counters_l | (1 << 22) : writable_counters_l;
  __asm__ volatile("addi x0, %0, 0" : "=r"(temp_readable));
  __asm__ volatile("csrr t1, 0xB17" : "=r"(temp_readable));
  writable_counters_l = temp_readable ? writable_counters_l | (1 << 23) : writable_counters_l;
  __asm__ volatile("addi x0, %0, 0" : "=r"(temp_readable));
  __asm__ volatile("csrr t1, 0xB18" : "=r"(temp_readable));
  writable_counters_l = temp_readable ? writable_counters_l | (1 << 24) : writable_counters_l;
  __asm__ volatile("addi x0, %0, 0" : "=r"(temp_readable));
  __asm__ volatile("csrr t1, 0xB19" : "=r"(temp_readable));
  writable_counters_l = temp_readable ? writable_counters_l | (1 << 25) : writable_counters_l;
  __asm__ volatile("addi x0, %0, 0" : "=r"(temp_readable));
  __asm__ volatile("csrr t1, 0xB1A" : "=r"(temp_readable));
  writable_counters_l = temp_readable ? writable_counters_l | (1 << 26) : writable_counters_l;
  __asm__ volatile("addi x0, %0, 0" : "=r"(temp_readable));
  __asm__ volatile("csrr t1, 0xB1B" : "=r"(temp_readable));
  writable_counters_l = temp_readable ? writable_counters_l | (1 << 27) : writable_counters_l;
  __asm__ volatile("addi x0, %0, 0" : "=r"(temp_readable));
  __asm__ volatile("csrr t1, 0xB1C" : "=r"(temp_readable));
  writable_counters_l = temp_readable ? writable_counters_l | (1 << 28) : writable_counters_l;
  __asm__ volatile("addi x0, %0, 0" : "=r"(temp_readable));
  __asm__ volatile("csrr t1, 0xB1D" : "=r"(temp_readable));
  writable_counters_l = temp_readable ? writable_counters_l | (1 << 29) : writable_counters_l;
  __asm__ volatile("addi x0, %0, 0" : "=r"(temp_readable));
  __asm__ volatile("csrr t1, 0xB1E" : "=r"(temp_readable));
  writable_counters_l = temp_readable ? writable_counters_l | (1 << 30) : writable_counters_l;
  __asm__ volatile("addi x0, %0, 0" : "=r"(temp_readable));
  __asm__ volatile("csrr t1, 0xB1F" : "=r"(temp_readable));
  writable_counters_l = temp_readable ? writable_counters_l | (1 << 31) : writable_counters_l;

  __asm__ volatile("addi x0, %0, 0" : "=r"(temp_readable));
  __asm__ volatile("csrr %0, 0xB83" : "=r"(temp_readable));
  writable_counters_h = temp_readable ? writable_counters_h | (1 << 3) : writable_counters_h;
  __asm__ volatile("addi x0, %0, 0" : "=r"(temp_readable));
  __asm__ volatile("csrr t1, 0xB84" : "=r"(temp_readable));
  writable_counters_h = temp_readable ? writable_counters_h | (1 << 4) : writable_counters_h;
  __asm__ volatile("addi x0, %0, 0" : "=r"(temp_readable));
  __asm__ volatile("csrr t1, 0xB85" : "=r"(temp_readable));
  writable_counters_h = temp_readable ? writable_counters_h | (1 << 5) : writable_counters_h;
  __asm__ volatile("addi x0, %0, 0" : "=r"(temp_readable));
  __asm__ volatile("csrr t1, 0xB86" : "=r"(temp_readable));
  writable_counters_h = temp_readable ? writable_counters_h | (1 << 6) : writable_counters_h;
  __asm__ volatile("addi x0, %0, 0" : "=r"(temp_readable));
  __asm__ volatile("csrr t1, 0xB87" : "=r"(temp_readable));
  writable_counters_h = temp_readable ? writable_counters_h | (1 << 7) : writable_counters_h;
  __asm__ volatile("addi x0, %0, 0" : "=r"(temp_readable));
  __asm__ volatile("csrr t1, 0xB88" : "=r"(temp_readable));
  writable_counters_h = temp_readable ? writable_counters_h | (1 << 8) : writable_counters_h;
  __asm__ volatile("addi x0, %0, 0" : "=r"(temp_readable));
  __asm__ volatile("csrr t1, 0xB89" : "=r"(temp_readable));
  writable_counters_h = temp_readable ? writable_counters_h | (1 << 9) : writable_counters_h;
  __asm__ volatile("addi x0, %0, 0" : "=r"(temp_readable));
  __asm__ volatile("csrr t1, 0xB8A" : "=r"(temp_readable));
  writable_counters_h = temp_readable ? writable_counters_h | (1 << 10) : writable_counters_h;
  __asm__ volatile("addi x0, %0, 0" : "=r"(temp_readable));
  __asm__ volatile("csrr t1, 0xB8B" : "=r"(temp_readable));
  writable_counters_h = temp_readable ? writable_counters_h | (1 << 11) : writable_counters_h;
  __asm__ volatile("addi x0, %0, 0" : "=r"(temp_readable));
  __asm__ volatile("csrr t1, 0xB8C" : "=r"(temp_readable));
  writable_counters_h = temp_readable ? writable_counters_h | (1 << 12) : writable_counters_h;
  __asm__ volatile("addi x0, %0, 0" : "=r"(temp_readable));
  __asm__ volatile("csrr t1, 0xB8D" : "=r"(temp_readable));
  writable_counters_h = temp_readable ? writable_counters_h | (1 << 13) : writable_counters_h;
  __asm__ volatile("addi x0, %0, 0" : "=r"(temp_readable));
  __asm__ volatile("csrr t1, 0xB8E" : "=r"(temp_readable));
  writable_counters_h = temp_readable ? writable_counters_h | (1 << 14) : writable_counters_h;
  __asm__ volatile("addi x0, %0, 0" : "=r"(temp_readable));
  __asm__ volatile("csrr t1, 0xB8F" : "=r"(temp_readable));
  writable_counters_h = temp_readable ? writable_counters_h | (1 << 15) : writable_counters_h;
  __asm__ volatile("addi x0, %0, 0" : "=r"(temp_readable));
  __asm__ volatile("csrr t1, 0xB90" : "=r"(temp_readable));
  writable_counters_h = temp_readable ? writable_counters_h | (1 << 16) : writable_counters_h;
  __asm__ volatile("addi x0, %0, 0" : "=r"(temp_readable));
  __asm__ volatile("csrr t1, 0xB91" : "=r"(temp_readable));
  writable_counters_h = temp_readable ? writable_counters_h | (1 << 17) : writable_counters_h;
  __asm__ volatile("addi x0, %0, 0" : "=r"(temp_readable));
  __asm__ volatile("csrr t1, 0xB92" : "=r"(temp_readable));
  writable_counters_h = temp_readable ? writable_counters_h | (1 << 18) : writable_counters_h;
  __asm__ volatile("addi x0, %0, 0" : "=r"(temp_readable));
  __asm__ volatile("csrr t1, 0xB93" : "=r"(temp_readable));
  writable_counters_h = temp_readable ? writable_counters_h | (1 << 19) : writable_counters_h;
  __asm__ volatile("addi x0, %0, 0" : "=r"(temp_readable));
  __asm__ volatile("csrr t1, 0xB94" : "=r"(temp_readable));
  writable_counters_h = temp_readable ? writable_counters_h | (1 << 20) : writable_counters_h;
  __asm__ volatile("addi x0, %0, 0" : "=r"(temp_readable));
  __asm__ volatile("csrr t1, 0xB95" : "=r"(temp_readable));
  writable_counters_h = temp_readable ? writable_counters_h | (1 << 21) : writable_counters_h;
  __asm__ volatile("addi x0, %0, 0" : "=r"(temp_readable));
  __asm__ volatile("csrr t1, 0xB96" : "=r"(temp_readable));
  writable_counters_h = temp_readable ? writable_counters_h | (1 << 22) : writable_counters_h;
  __asm__ volatile("addi x0, %0, 0" : "=r"(temp_readable));
  __asm__ volatile("csrr t1, 0xB97" : "=r"(temp_readable));
  writable_counters_h = temp_readable ? writable_counters_h | (1 << 23) : writable_counters_h;
  __asm__ volatile("addi x0, %0, 0" : "=r"(temp_readable));
  __asm__ volatile("csrr t1, 0xB98" : "=r"(temp_readable));
  writable_counters_h = temp_readable ? writable_counters_h | (1 << 24) : writable_counters_h;
  __asm__ volatile("addi x0, %0, 0" : "=r"(temp_readable));
  __asm__ volatile("csrr t1, 0xB99" : "=r"(temp_readable));
  writable_counters_h = temp_readable ? writable_counters_h | (1 << 25) : writable_counters_h;
  __asm__ volatile("addi x0, %0, 0" : "=r"(temp_readable));
  __asm__ volatile("csrr t1, 0xB9A" : "=r"(temp_readable));
  writable_counters_h = temp_readable ? writable_counters_h | (1 << 26) : writable_counters_h;
  __asm__ volatile("addi x0, %0, 0" : "=r"(temp_readable));
  __asm__ volatile("csrr t1, 0xB9B" : "=r"(temp_readable));
  writable_counters_h = temp_readable ? writable_counters_h | (1 << 27) : writable_counters_h;
  __asm__ volatile("addi x0, %0, 0" : "=r"(temp_readable));
  __asm__ volatile("csrr t1, 0xB9C" : "=r"(temp_readable));
  writable_counters_h = temp_readable ? writable_counters_h | (1 << 28) : writable_counters_h;
  __asm__ volatile("addi x0, %0, 0" : "=r"(temp_readable));
  __asm__ volatile("csrr t1, 0xB9D" : "=r"(temp_readable));
  writable_counters_h = temp_readable ? writable_counters_h | (1 << 29) : writable_counters_h;
  __asm__ volatile("addi x0, %0, 0" : "=r"(temp_readable));
  __asm__ volatile("csrr t1, 0xB9E" : "=r"(temp_readable));
  writable_counters_h = temp_readable ? writable_counters_h | (1 << 30) : writable_counters_h;
  __asm__ volatile("addi x0, %0, 0" : "=r"(temp_readable));
  __asm__ volatile("csrr t1, 0xB9F" : "=r"(temp_readable));
  writable_counters_h = temp_readable ? writable_counters_h | (1 << 31) : writable_counters_h;

  __asm__ volatile("addi t0, x0, 0");
  __asm__ volatile("csrw 0xB03, t0");
  __asm__ volatile("csrw 0xB04, t0");
  __asm__ volatile("csrw 0xB05, t0");
  __asm__ volatile("csrw 0xB06, t0");
  __asm__ volatile("csrw 0xB07, t0");
  __asm__ volatile("csrw 0xB08, t0");
  __asm__ volatile("csrw 0xB09, t0");
  __asm__ volatile("csrw 0xB0A, t0");
  __asm__ volatile("csrw 0xB0B, t0");
  __asm__ volatile("csrw 0xB0C, t0");
  __asm__ volatile("csrw 0xB0D, t0");
  __asm__ volatile("csrw 0xB0E, t0");
  __asm__ volatile("csrw 0xB0F, t0");
  __asm__ volatile("csrw 0xB10, t0");
  __asm__ volatile("csrw 0xB11, t0");
  __asm__ volatile("csrw 0xB12, t0");
  __asm__ volatile("csrw 0xB13, t0");
  __asm__ volatile("csrw 0xB14, t0");
  __asm__ volatile("csrw 0xB15, t0");
  __asm__ volatile("csrw 0xB16, t0");
  __asm__ volatile("csrw 0xB17, t0");
  __asm__ volatile("csrw 0xB18, t0");
  __asm__ volatile("csrw 0xB19, t0");
  __asm__ volatile("csrw 0xB1A, t0");
  __asm__ volatile("csrw 0xB1B, t0");
  __asm__ volatile("csrw 0xB1C, t0");
  __asm__ volatile("csrw 0xB1D, t0");
  __asm__ volatile("csrw 0xB1E, t0");
  __asm__ volatile("csrw 0xB1F, t0");

  __asm__ volatile("csrw 0xB83, t0");
  __asm__ volatile("csrw 0xB84, t0");
  __asm__ volatile("csrw 0xB85, t0");
  __asm__ volatile("csrw 0xB86, t0");
  __asm__ volatile("csrw 0xB87, t0");
  __asm__ volatile("csrw 0xB88, t0");
  __asm__ volatile("csrw 0xB89, t0");
  __asm__ volatile("csrw 0xB8A, t0");
  __asm__ volatile("csrw 0xB8B, t0");
  __asm__ volatile("csrw 0xB8C, t0");
  __asm__ volatile("csrw 0xB8D, t0");
  __asm__ volatile("csrw 0xB8E, t0");
  __asm__ volatile("csrw 0xB8F, t0");
  __asm__ volatile("csrw 0xB90, t0");
  __asm__ volatile("csrw 0xB91, t0");
  __asm__ volatile("csrw 0xB92, t0");
  __asm__ volatile("csrw 0xB93, t0");
  __asm__ volatile("csrw 0xB94, t0");
  __asm__ volatile("csrw 0xB95, t0");
  __asm__ volatile("csrw 0xB96, t0");
  __asm__ volatile("csrw 0xB97, t0");
  __asm__ volatile("csrw 0xB98, t0");
  __asm__ volatile("csrw 0xB99, t0");
  __asm__ volatile("csrw 0xB9A, t0");
  __asm__ volatile("csrw 0xB9B, t0");
  __asm__ volatile("csrw 0xB9C, t0");
  __asm__ volatile("csrw 0xB9D, t0");
  __asm__ volatile("csrw 0xB9E, t0");
  __asm__ volatile("csrw 0xB9F, t0");

  __asm__ volatile("csrr %0, 0x320" : "=r"(mcountinhibit_rval));

  int v = writable_counters_l & writable_counters_h;
  int num_implemented_counters = 0;
  if ((mcountinhibit_rval >> 3) && ((writable_counters_l & writable_counters_h) >> 3)) {
    printf("\nWritable: %0x", writable_counters_l & writable_counters_h);
    for (num_implemented_counters = 0; v; num_implemented_counters++) {
      v &= v - 1;
    }
    printf("\nNumber of detected writable/readable counters: %0d", num_implemented_counters);
  }
  else {
    printf("\nError, writable counters / mcountinhibit mismatch: %0x, %0x", v, mcountinhibit_rval);
    err_cnt += 1;
  }

  printf("\n\nPerformance Counters Basic Test\n");

  __asm__ volatile("csrr %0, 0xB00" : "=r"(mcycle_rval));
  __asm__ volatile("csrr %0, 0xB02" : "=r"(minstret_rval));


  __asm__ volatile("csrr %0, 0x320" : "=r"(mcountinhibit_rval));


  __asm__ volatile("csrr %0, 0xB03" : "=r"(mhpmcounter_rval[3]));
  __asm__ volatile("csrr %0, 0xB04" : "=r"(mhpmcounter_rval[4]));
  __asm__ volatile("csrr %0, 0xB05" : "=r"(mhpmcounter_rval[5]));
  __asm__ volatile("csrr %0, 0xB06" : "=r"(mhpmcounter_rval[6]));
  __asm__ volatile("csrr %0, 0xB07" : "=r"(mhpmcounter_rval[7]));
  __asm__ volatile("csrr %0, 0xB08" : "=r"(mhpmcounter_rval[8]));
  __asm__ volatile("csrr %0, 0xB09" : "=r"(mhpmcounter_rval[9]));
  __asm__ volatile("csrr %0, 0xB0A" : "=r"(mhpmcounter_rval[10]));
  __asm__ volatile("csrr %0, 0xB0B" : "=r"(mhpmcounter_rval[11]));
  __asm__ volatile("csrr %0, 0xB0C" : "=r"(mhpmcounter_rval[12]));
  __asm__ volatile("csrr %0, 0xB0D" : "=r"(mhpmcounter_rval[13]));
  __asm__ volatile("csrr %0, 0xB0E" : "=r"(mhpmcounter_rval[14]));
  __asm__ volatile("csrr %0, 0xB0F" : "=r"(mhpmcounter_rval[15]));
  __asm__ volatile("csrr %0, 0xB10" : "=r"(mhpmcounter_rval[16]));
  __asm__ volatile("csrr %0, 0xB11" : "=r"(mhpmcounter_rval[17]));
  __asm__ volatile("csrr %0, 0xB12" : "=r"(mhpmcounter_rval[18]));
  __asm__ volatile("csrr %0, 0xB13" : "=r"(mhpmcounter_rval[19]));
  __asm__ volatile("csrr %0, 0xB14" : "=r"(mhpmcounter_rval[20]));
  __asm__ volatile("csrr %0, 0xB15" : "=r"(mhpmcounter_rval[21]));
  __asm__ volatile("csrr %0, 0xB16" : "=r"(mhpmcounter_rval[22]));
  __asm__ volatile("csrr %0, 0xB17" : "=r"(mhpmcounter_rval[23]));
  __asm__ volatile("csrr %0, 0xB18" : "=r"(mhpmcounter_rval[24]));
  __asm__ volatile("csrr %0, 0xB19" : "=r"(mhpmcounter_rval[25]));
  __asm__ volatile("csrr %0, 0xB1A" : "=r"(mhpmcounter_rval[26]));
  __asm__ volatile("csrr %0, 0xB1B" : "=r"(mhpmcounter_rval[27]));
  __asm__ volatile("csrr %0, 0xB1C" : "=r"(mhpmcounter_rval[28]));
  __asm__ volatile("csrr %0, 0xB1D" : "=r"(mhpmcounter_rval[29]));
  __asm__ volatile("csrr %0, 0xB1E" : "=r"(mhpmcounter_rval[30]));
  __asm__ volatile("csrr %0, 0xB1F" : "=r"(mhpmcounter_rval[31]));


  __asm__ volatile("csrr %0, 0x323" : "=r"(mhpmevent_rval[3]));
  __asm__ volatile("csrr %0, 0x324" : "=r"(mhpmevent_rval[4]));
  __asm__ volatile("csrr %0, 0x325" : "=r"(mhpmevent_rval[5]));
  __asm__ volatile("csrr %0, 0x326" : "=r"(mhpmevent_rval[6]));
  __asm__ volatile("csrr %0, 0x327" : "=r"(mhpmevent_rval[7]));
  __asm__ volatile("csrr %0, 0x328" : "=r"(mhpmevent_rval[8]));
  __asm__ volatile("csrr %0, 0x329" : "=r"(mhpmevent_rval[9]));
  __asm__ volatile("csrr %0, 0x32A" : "=r"(mhpmevent_rval[10]));
  __asm__ volatile("csrr %0, 0x32B" : "=r"(mhpmevent_rval[11]));
  __asm__ volatile("csrr %0, 0x32C" : "=r"(mhpmevent_rval[12]));
  __asm__ volatile("csrr %0, 0x32D" : "=r"(mhpmevent_rval[13]));
  __asm__ volatile("csrr %0, 0x32E" : "=r"(mhpmevent_rval[14]));
  __asm__ volatile("csrr %0, 0x32F" : "=r"(mhpmevent_rval[15]));
  __asm__ volatile("csrr %0, 0x330" : "=r"(mhpmevent_rval[16]));
  __asm__ volatile("csrr %0, 0x331" : "=r"(mhpmevent_rval[17]));
  __asm__ volatile("csrr %0, 0x332" : "=r"(mhpmevent_rval[18]));
  __asm__ volatile("csrr %0, 0x333" : "=r"(mhpmevent_rval[19]));
  __asm__ volatile("csrr %0, 0x334" : "=r"(mhpmevent_rval[20]));
  __asm__ volatile("csrr %0, 0x335" : "=r"(mhpmevent_rval[21]));
  __asm__ volatile("csrr %0, 0x336" : "=r"(mhpmevent_rval[22]));
  __asm__ volatile("csrr %0, 0x337" : "=r"(mhpmevent_rval[23]));
  __asm__ volatile("csrr %0, 0x338" : "=r"(mhpmevent_rval[24]));
  __asm__ volatile("csrr %0, 0x339" : "=r"(mhpmevent_rval[25]));
  __asm__ volatile("csrr %0, 0x33A" : "=r"(mhpmevent_rval[26]));
  __asm__ volatile("csrr %0, 0x33B" : "=r"(mhpmevent_rval[27]));
  __asm__ volatile("csrr %0, 0x33C" : "=r"(mhpmevent_rval[28]));
  __asm__ volatile("csrr %0, 0x33D" : "=r"(mhpmevent_rval[29]));
  __asm__ volatile("csrr %0, 0x33E" : "=r"(mhpmevent_rval[30]));
  __asm__ volatile("csrr %0, 0x33F" : "=r"(mhpmevent_rval[31]));

  for (int i=3; i<32; i++) {
    sum += mhpmevent_rval[i];
  }
  if (sum) {
    printf("ERROR: CSR MHPMEVENT[3..31] not 0x0!\n\n");
    ++err_cnt;
  }


  sum = 0;
  for (int i=3; i<32; i++) {
    sum += mhpmcounter_rval[i];
  }
  if (sum) {
    printf("ERROR: CSR MHPMCOUNTER[3..31] not 0x0!\n\n");
    ++err_cnt;
  }


  if (mcycle_rval != 0x0) {
    printf("ERROR: CSR MCYCLE not 0x0!\n\n");
    ++err_cnt;
  }

  if (minstret_rval != 0x0) {
    printf("ERROR: CSR MINSTRET not 0x0!\n\n");
    ++err_cnt;
  }

  if (mcountinhibit_rval != 0xD) {
    printf("ERROR: CSR MCOUNTINHIBIT not 0xD!\n\n");
    ++err_cnt;
  }


  printf("MCYCLE Initial  Value is %0x\n", mcycle_rval);
  printf("MINSTRET Initial  Value is %0x\n", minstret_rval);
  printf("MCOUNTINHIBIT Initial  Value is %0x\n", mcountinhibit_rval);

//////////////////////////////////////////////////////////////
  // To complete code coverage try to write all unimplemented HPMEVENT<n> registers
  for (int i = 3; i <= 31; i++) {
    volatile unsigned int revent;
    volatile unsigned int wevent = (unsigned int) -1;


    if (i >= NUM_MHPMCOUNTERS+3) {
      switch (i) {
        case 3:
          __asm__ volatile("csrw mhpmevent3, %0" : : "r"(wevent));
          __asm__ volatile("csrr %0, mhpmevent3" : "=r"(revent));
          break;
        case 4:
          __asm__ volatile("csrw mhpmevent4, %0" : : "r"(wevent));
          __asm__ volatile("csrr %0, mhpmevent4" : "=r"(revent));
          break;
        case 5:
          __asm__ volatile("csrw mhpmevent5, %0" : : "r"(wevent));
          __asm__ volatile("csrr %0, mhpmevent5" : "=r"(revent));
          break;
        case 6:
          __asm__ volatile("csrw mhpmevent6, %0" : : "r"(wevent));
          __asm__ volatile("csrr %0, mhpmevent6" : "=r"(revent));
          break;
        case 7:
          __asm__ volatile("csrw mhpmevent7, %0" : : "r"(wevent));
          __asm__ volatile("csrr %0, mhpmevent7" : "=r"(revent));
          break;
        case 8:
          __asm__ volatile("csrw mhpmevent8, %0" : : "r"(wevent));
          __asm__ volatile("csrr %0, mhpmevent8" : "=r"(revent));
          break;
        case 9:
          __asm__ volatile("csrw mhpmevent9, %0" : : "r"(wevent));
          __asm__ volatile("csrr %0, mhpmevent9" : "=r"(revent));
          break;
        case 10:
          __asm__ volatile("csrw mhpmevent10, %0" : : "r"(wevent));
          __asm__ volatile("csrr %0, mhpmevent10" : "=r"(revent));
          break;
        case 11:
          __asm__ volatile("csrw mhpmevent11, %0" : : "r"(wevent));
          __asm__ volatile("csrr %0, mhpmevent11" : "=r"(revent));
          break;
        case 12:
          __asm__ volatile("csrw mhpmevent12, %0" : : "r"(wevent));
          __asm__ volatile("csrr %0, mhpmevent12" : "=r"(revent));
          break;
        case 13:
          __asm__ volatile("csrw mhpmevent13, %0" : : "r"(wevent));
          __asm__ volatile("csrr %0, mhpmevent13" : "=r"(revent));
          break;
        case 14:
          __asm__ volatile("csrw mhpmevent14, %0" : : "r"(wevent));
          __asm__ volatile("csrr %0, mhpmevent14" : "=r"(revent));
          break;
        case 15:
          __asm__ volatile("csrw mhpmevent15, %0" : : "r"(wevent));
          __asm__ volatile("csrr %0, mhpmevent15" : "=r"(revent));
          break;
        case 16:
          __asm__ volatile("csrw mhpmevent16, %0" : : "r"(wevent));
          __asm__ volatile("csrr %0, mhpmevent16" : "=r"(revent));
          break;
        case 17:
          __asm__ volatile("csrw mhpmevent17, %0" : : "r"(wevent));
          __asm__ volatile("csrr %0, mhpmevent17" : "=r"(revent));
          break;
        case 18:
          __asm__ volatile("csrw mhpmevent18, %0" : : "r"(wevent));
          __asm__ volatile("csrr %0, mhpmevent18" : "=r"(revent));
          break;
        case 19:
          __asm__ volatile("csrw mhpmevent19, %0" : : "r"(wevent));
          __asm__ volatile("csrr %0, mhpmevent19" : "=r"(revent));
          break;
        case 20:
          __asm__ volatile("csrw mhpmevent20, %0" : : "r"(wevent));
          __asm__ volatile("csrr %0, mhpmevent20" : "=r"(revent));
          break;
        case 21:
          __asm__ volatile("csrw mhpmevent21, %0" : : "r"(wevent));
          __asm__ volatile("csrr %0, mhpmevent21" : "=r"(revent));
          break;
        case 22:
          __asm__ volatile("csrw mhpmevent22, %0" : : "r"(wevent));
          __asm__ volatile("csrr %0, mhpmevent22" : "=r"(revent));
          break;
        case 23:
          __asm__ volatile("csrw mhpmevent23, %0" : : "r"(wevent));
          __asm__ volatile("csrr %0, mhpmevent23" : "=r"(revent));
          break;
        case 24:
          __asm__ volatile("csrw mhpmevent24, %0" : : "r"(wevent));
          __asm__ volatile("csrr %0, mhpmevent24" : "=r"(revent));
          break;
        case 25:
          __asm__ volatile("csrw mhpmevent25, %0" : : "r"(wevent));
          __asm__ volatile("csrr %0, mhpmevent25" : "=r"(revent));
          break;
        case 26:
          __asm__ volatile("csrw mhpmevent26, %0" : : "r"(wevent));
          __asm__ volatile("csrr %0, mhpmevent26" : "=r"(revent));
          break;
        case 27:
          __asm__ volatile("csrw mhpmevent27, %0" : : "r"(wevent));
          __asm__ volatile("csrr %0, mhpmevent27" : "=r"(revent));
          break;
        case 28:
          __asm__ volatile("csrw mhpmevent28, %0" : : "r"(wevent));
          __asm__ volatile("csrr %0, mhpmevent28" : "=r"(revent));
          break;
        case 29:
          __asm__ volatile("csrw mhpmevent29, %0" : : "r"(wevent));
          __asm__ volatile("csrr %0, mhpmevent29" : "=r"(revent));
          break;
        case 30:
          __asm__ volatile("csrw mhpmevent30, %0" : : "r"(wevent));
          __asm__ volatile("csrr %0, mhpmevent30" : "=r"(revent));
          break;
        case 31:
          __asm__ volatile("csrw mhpmevent31, %0" : : "r"(wevent));
          __asm__ volatile("csrr %0, mhpmevent31" : "=r"(revent));
          break;
      }

      if (revent != 0) {
        printf("ERROR: MHPMEVENT%d does not read back zero 0x%0x\n", i, revent);
        ++err_cnt;
      }
    }
  }

//////////////////////////////////////////////////////////////
  // Count load use hazards
  printf("\nCount load use hazards");

  event = EVENT_ID_LD_STALL;                                    // Trigger on load use hazards
  __asm__ volatile("csrw 0x323, %0 " : : "r"(event));           // Set mhpmevent3
  __asm__ volatile("csrwi 0xB02, 0x0");                         // minstret = 0
  __asm__ volatile("csrwi 0xB03, 0x0");                         // mhpmcounter3 = 0
  __asm__ volatile("csrwi 0x320, 0x0");                         // Enable counters
  __asm__ volatile("lw x4, 0(sp)\n\t\
                    addi x5, x4, 1\n\t\
                    lw x4, 0(sp)\n\t\
                    lw x4, 4(sp)\n\t\
                    addi x6, x4, 4\n\t\
                    lh x8, 4(sp)\n\t\
                    addi x6, x8, 4\n\t\
                    lhu x6, 4(sp)\n\t\
                    lb x6, 4(sp)\n\t\
                    addi x5, x6, 1\n\t\
                    lbu x6, 4(sp)\n\t\
                    lh x5, 4(sp)\n\t\
                    addi x5, x5, 4\n\t\
                    addi x7, x0, 1" \
                    : : : "x4", "x5", "x6", "x7", "x8");
  __asm__ volatile("csrwi 0x320, 0x1F");                        // Inhibit mcycle, minstret, mhpmcounter3-4
  __asm__ volatile("csrr %0, 0xB02" : "=r"(minstret_rval));     // minstret
  __asm__ volatile("csrr %0, 0xB03" : "=r"(count));             // mhpmcounter3

  printf("\nminstret count = %d\n", minstret_rval);
  err_cnt += chck(minstret_rval, 15);


  printf("Load use hazards count = %d\n", count);

  err_cnt += chck_le(count, 5);


  //////////////////////////////////////////////////////////////
  // Count jump register hazards
  printf("\nCount Jump register hazards");

  event = EVENT_ID_JMP_STALL;                                   // Trigger on jump register hazards
  __asm__ volatile("csrw 0x323, %0 " : : "r"(event));           // Set mhpmevent3
  __asm__ volatile("csrwi 0xB02, 0x0");                         // minstret = 0
  __asm__ volatile("csrwi 0xB03, 0x0");                         // mhpmcounter3 = 0
  __asm__ volatile("csrwi 0x320, 0x0");                         // Enable counters
  __asm__ volatile("auipc x4, 0x0\n\t\
                    addi x4, x4, 10\n\t\
                    jalr x0, x4, 0x0\n\t\
                    addi x4, x4, 10\n\t\
		    auipc x4, 0x0\n\t\
		    addi x4, x4, 10\n\t\
                    jalr x0, x4, 0x0\n\t\
		    addi x4, x4, 10\n\t\
                    lh x4, 4(sp)\n\t\
		    addi x4, x4, 10\n\t\
                    lw x4, 4(sp)\n\t\
                    addi x4, x4, 10\n\t\
                    addi x4, x4, 10\n\t\
                    addi x4, x4, 10\n\t\
		    auipc x4, 0x0\n\t\
		    addi x4, x4, 10\n\t\
                    jalr x0, x4, 0x0" \
                    : : : "x4");
  __asm__ volatile("csrwi 0x320, 0x1F");                        // Inhibit mcycle, minstret, mhpmcounter3-4
  __asm__ volatile("csrr %0, 0xB02" : "=r"(minstret_rval));     // minstret
  __asm__ volatile("csrr %0, 0xB03" : "=r"(count));             // mhpmcounter3

  printf("\nminstret count = %d\n", minstret_rval);
  err_cnt += chck(minstret_rval, 18);

  printf("Jump register hazards count = %d\n", count);
  err_cnt += chck_le(count, 3);                                 // 3 if no instruction if stalls are present

  //////////////////////////////////////////////////////////////
  // Count memory read transactions
  printf("\nCount memory read transactions");

  event = EVENT_DATA_READ;                                      // Trigger on loads
  __asm__ volatile("csrw 0x323, %0 " : : "r"(event));           // Set mhpmevent3
  __asm__ volatile("csrwi 0xB02, 0x0");                         // minstret = 0
  __asm__ volatile("csrwi 0xB03, 0x0");                         // mhpmcounter3 = 0
  __asm__ volatile("csrwi 0x320, 0x0");                         // Enable counters
  __asm__ volatile("lw x4, 0(sp)");                             // count++
  __asm__ volatile("mulh x0, x0, x0");
  __asm__ volatile("j jump_target_memread");                    // do not count jump in mhpmevent3
  __asm__ volatile("nop");                                      // do not count nop in instret
  __asm__ volatile("jump_target_memread:");
  __asm__ volatile("lw x4, 0(sp)");                             // count++
  __asm__ volatile("addi x4, x4, 10");
  __asm__ volatile("csrwi 0x320, 0x1F");                        // Inhibit mcycle, minstret, mhpmcounter3-4
  __asm__ volatile("csrr %0, 0xB02" : "=r"(minstret_rval));          // minstret
  __asm__ volatile("csrr %0, 0xB03" : "=r"(count));             // mhpmcounter3

  printf("\nminstret count = %d\n", minstret_rval);
  err_cnt += chck(minstret_rval, 6);

  printf("Load count = %d\n", count);
  err_cnt += chck(count, 2);

  //////////////////////////////////////////////////////////////
  // Count memory write transactions
  printf("\nCount memory write transactions");

  event = EVENT_DATA_WRITE;                                     // Trigger on stores
  __asm__ volatile("csrw 0x323, %0 " : : "r"(event));           // Set mhpmevent3
  __asm__ volatile("csrwi 0xB02, 0x0");                         // minstret = 0
  __asm__ volatile("csrwi 0xB03, 0x0");                         // mhpmcounter3 = 0
  __asm__ volatile("csrwi 0x320, 0x0");                         // Enable counters
  __asm__ volatile("sw x0, 0(sp)");                             // count++
  __asm__ volatile("mulh x0, x0, x0");
  __asm__ volatile("sw x0, 0(sp)");                             // count++
  __asm__ volatile("csrwi 0x320, 0x1F");                        // Inhibit mcycle, minstret, mhpmcounter3-4
  __asm__ volatile("csrr %0, 0xB02" : "=r"(minstret_rval));     // minstret
  __asm__ volatile("csrr %0, 0xB03" : "=r"(count));             // mhpmcounter3

  printf("\nminstret count = %d\n", minstret_rval);
  err_cnt += chck(minstret_rval, 4);

  printf("Store count = %d\n", count);
  err_cnt += chck(count, 2);

  //////////////////////////////////////////////////////////////
  // Count jumps
  printf("\nCount jumps");

  event = EVENT_JUMP;                                           // Trigger on jumps
  __asm__ volatile("csrw 0x323, %0 " : : "r"(event));           // Set mhpmevent3
  __asm__ volatile("csrwi 0xB02, 0x0");                         // minstret = 0
  __asm__ volatile("csrwi 0xB03, 0x0");                         // mhpmcounter3 = 0
  __asm__ volatile("csrwi 0x320, 0x0");                         // Enable counters
  __asm__ volatile("j jump_target_0");                          // count++
  __asm__ volatile("jump_target_0:");
  __asm__ volatile("j jump_target_1");                          // count++
  __asm__ volatile("jump_target_1:");
  __asm__ volatile("csrwi 0x320, 0x1F");                        // Inhibit mcycle, minstret, mhpmcounter3-4
  __asm__ volatile("csrr %0, 0xB02" : "=r"(minstret_rval));     // minstret
  __asm__ volatile("csrr %0, 0xB03" : "=r"(count));             // mhpmcounter3

  printf("\nminstret count = %d\n", minstret_rval);
  err_cnt += chck(minstret_rval, 3);

  printf("Jump count = %d\n", count);
  err_cnt += chck(count, 2);

  //////////////////////////////////////////////////////////////
  // Count branches (conditional)
  printf("\nCount branches (conditional)");

  event = EVENT_BRANCH;                                         // Trigger on on taken branches
  __asm__ volatile("csrw 0x323, %0 " : : "r"(event));           // Set mhpmevent3
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
  __asm__ volatile("csrr %0, 0xB02" : "=r"(minstret_rval));     // minstret
  __asm__ volatile("csrr %0, 0xB03" : "=r"(count));             // mhpmcounter3

  printf("\nminstret count = %d\n", minstret_rval);
  err_cnt += chck(minstret_rval, 4);

  printf("Branch count = %d\n", count);
  err_cnt += chck(count, 3);

  //////////////////////////////////////////////////////////////
  // Count branches taken (conditional)
  printf("\nCount branches taken (conditional)");

  event = EVENT_BRANCH_TAKEN;                                   // Trigger on on taken branches
  __asm__ volatile("csrw 0x323, %0 " : : "r"(event));           // Set mhpmevent3
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
  __asm__ volatile("csrr %0, 0xB02" : "=r"(minstret_rval));     // minstret
  __asm__ volatile("csrr %0, 0xB03" : "=r"(count));             // mhpmcounter3

  printf("\nminstret count = %d\n", minstret_rval);
  err_cnt += chck(minstret_rval, 4);

  printf("Branch taken count = %d\n", count);
  err_cnt += chck(count, 2);

  //////////////////////////////////////////////////////////////
  // Compressed instructions
  printf("\nCompressed instructions");

  event = EVENT_COMP_INSTR;                                     // Trigger on compressed instructions
  __asm__ volatile("csrw 0x323, %0 " : : "r"(event));           // Set mhpmevent3
  __asm__ volatile("csrwi 0xB02, 0x0");                         // minstret = 0
  __asm__ volatile("csrwi 0xB03, 0x0");                         // mhpmcounter3 = 0
  __asm__ volatile("csrwi 0x320, 0x0");                         // Enable counters
  __asm__ volatile("c.addi x15, 1\n\t\
                    c.nop\n\t\
                    c.addi x15, 1" \
                    : : : "x15");
  __asm__ volatile("csrwi 0x320, 0x1F");                        // Inhibit mcycle, minstret, mhpmcounter3-4
  __asm__ volatile("csrr %0, 0xB02" : "=r"(minstret_rval));     // minstret
  __asm__ volatile("csrr %0, 0xB03" : "=r"(count));             // mhpmcounter3

  printf("\nminstret count = %d\n", minstret_rval);
  err_cnt += chck(minstret_rval, 4);

  printf("Compressed count = %d\n", count);
  err_cnt += chck(count, 3);

  //////////////////////////////////////////////////////////////
  // Retired instruction count
  printf("\nRetired instruction count");

  event = EVENT_INSTR;                                          // Trigger on retired instructions
  __asm__ volatile(".option rvc");
  __asm__ volatile("csrw 0x323, %0 " : : "r"(event));           // Set mhpmevent3
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
  __asm__ volatile("csrr %0, 0xB02" : "=r"(minstret_rval));     // minstret
  __asm__ volatile("csrr %0, 0xB03" : "=r"(count));             // mhpmcounter3

  printf("\nminstret count = %d\n", minstret_rval);
  err_cnt += chck(minstret_rval, 5 + 6*5 + 4 + 1);

  printf("Retired instruction count = %d\n", count);
  err_cnt += chck(count, 5 + 6*5 + 4 + 1);

  //////////////////////////////////////////////////////////////
  // Check for errors
  printf("\nDone\n");

  if (err_cnt)
    printf("FAILURE. %d errors\n\n", err_cnt);
  else
    printf("SUCCESS\n\n");

  return err_cnt;


  printf("MCYCLE Final Read Value is %0x\n", mcycle_rval);
  printf("MINSTRET Final Read Value is %0x\n", minstret_rval);
  printf("MCOUNTINHIBIT Final Read Value is %0x\n", mcountinhibit_rval);
  printf("MHARTID Final Read Value is %0x\n", mhartid_rval);

  printf("DONE!\n\n");

}


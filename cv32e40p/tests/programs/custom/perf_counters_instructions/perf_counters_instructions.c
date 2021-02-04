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



  __asm__ volatile(".option rvc");

  sum = 0;
  err_cnt = 0;
  count = 0;
  event = 0;

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
        case 7:
          __asm__ volatile("csrw mhpmevent7, %0" : : "r"(wevent)); 
          __asm__ volatile("csrr %0, mhpmevent7" : "=r"(revent)); 
        case 8:
          __asm__ volatile("csrw mhpmevent8, %0" : : "r"(wevent)); 
          __asm__ volatile("csrr %0, mhpmevent8" : "=r"(revent)); 
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
        case 17:
          __asm__ volatile("csrw mhpmevent17, %0" : : "r"(wevent)); 
          __asm__ volatile("csrr %0, mhpmevent17" : "=r"(revent)); 
        case 18:
          __asm__ volatile("csrw mhpmevent18, %0" : : "r"(wevent)); 
          __asm__ volatile("csrr %0, mhpmevent18" : "=r"(revent)); 
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
        case 27:
          __asm__ volatile("csrw mhpmevent27, %0" : : "r"(wevent)); 
          __asm__ volatile("csrr %0, mhpmevent27" : "=r"(revent)); 
        case 28:
          __asm__ volatile("csrw mhpmevent28, %0" : : "r"(wevent)); 
          __asm__ volatile("csrr %0, mhpmevent28" : "=r"(revent)); 
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

  event = 0x4;                                                  // Trigger on load use hazards
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
  __asm__ volatile("csrr %0, 0xB02" : "=r"(minstret_rval));          // minstret
  __asm__ volatile("csrr %0, 0xB03" : "=r"(count));             // mhpmcounter3

  printf("\nminstret count = %d\n", minstret_rval);
  err_cnt += chck(minstret_rval, 15);


  printf("Load use hazards count = %d\n", count);

  err_cnt += chck(count, 5);


  //////////////////////////////////////////////////////////////
  // Count jump register hazards
  printf("\nCount Jump register hazards");

  event = 0x8;                                                  // Trigger on jump register hazards
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
  __asm__ volatile("csrr %0, 0xB02" : "=r"(minstret_rval));          // minstret
  __asm__ volatile("csrr %0, 0xB03" : "=r"(count));             // mhpmcounter3

  printf("\nminstret count = %d\n", minstret_rval);
  err_cnt += chck(minstret_rval, 18);

  printf("Jump register hazards count = %d\n", count);
  err_cnt += chck(count, 3);

  //////////////////////////////////////////////////////////////
  // Count memory read transactions
  printf("\nCount memory read transactions");

  event = 0x20;                                                 // Trigger on loads
  __asm__ volatile("csrw 0x323, %0 " : : "r"(event));             // Set mhpmevent3
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

  event = 0x40;                                                 // Trigger on stores
  __asm__ volatile("csrw 0x323, %0 " : : "r"(event));           // Set mhpmevent3
  __asm__ volatile("csrwi 0xB02, 0x0");                         // minstret = 0
  __asm__ volatile("csrwi 0xB03, 0x0");                         // mhpmcounter3 = 0
  __asm__ volatile("csrwi 0x320, 0x0");                         // Enable counters
  __asm__ volatile("sw x0, 0(sp)");                             // count++
  __asm__ volatile("mulh x0, x0, x0");
  __asm__ volatile("sw x0, 0(sp)");                             // count++
  __asm__ volatile("csrwi 0x320, 0x1F");                        // Inhibit mcycle, minstret, mhpmcounter3-4
  __asm__ volatile("csrr %0, 0xB02" : "=r"(minstret_rval));          // minstret
  __asm__ volatile("csrr %0, 0xB03" : "=r"(count));             // mhpmcounter3

  printf("\nminstret count = %d\n", minstret_rval);
  err_cnt += chck(minstret_rval, 4);

  printf("Store count = %d\n", count);
  err_cnt += chck(count, 2);

  //////////////////////////////////////////////////////////////
  // Count jumps
  printf("\nCount jumps");

  event = 0x80;                                                 // Trigger on jumps
  __asm__ volatile("csrw 0x323, %0 " : : "r"(event));           // Set mhpmevent3
  __asm__ volatile("csrwi 0xB02, 0x0");                         // minstret = 0
  __asm__ volatile("csrwi 0xB03, 0x0");                         // mhpmcounter3 = 0
  __asm__ volatile("csrwi 0x320, 0x0");                         // Enable counters
  __asm__ volatile("j jump_target_0");                          // count++
  __asm__ volatile("jump_target_0:");
  __asm__ volatile("j jump_target_1");                          // count++
  __asm__ volatile("jump_target_1:");
  __asm__ volatile("csrwi 0x320, 0x1F");                        // Inhibit mcycle, minstret, mhpmcounter3-4
  __asm__ volatile("csrr %0, 0xB02" : "=r"(minstret_rval));          // minstret
  __asm__ volatile("csrr %0, 0xB03" : "=r"(count));             // mhpmcounter3

  printf("\nminstret count = %d\n", minstret_rval);
  err_cnt += chck(minstret_rval, 3);

  printf("Jump count = %d\n", count);
  err_cnt += chck(count, 2);

  //////////////////////////////////////////////////////////////
  // Count Icache Misses
  printf("\nCount Icache Misses");

  event = 0x10;                                                 // Trigger on jumps
  __asm__ volatile("csrw 0x323, %0 " : : "r"(event));             // Set mhpmevent3
  __asm__ volatile("csrwi 0xB02, 0x0");                         // minstret = 0
  __asm__ volatile("csrwi 0xB03, 0x0");                         // mhpmcounter3 = 0
  __asm__ volatile("csrwi 0x320, 0x0");                         // Enable counters
  __asm__ volatile("fence.i");               
  __asm__ volatile("j jump_target_5");                          // count++
  __asm__ volatile("addi x4, x4, 10");               
  __asm__ volatile("addi x4, x4, 10");               
  __asm__ volatile("addi x4, x4, 10");               
  __asm__ volatile("addi x4, x4, 10");               
  __asm__ volatile("addi x4, x4, 10");               
  __asm__ volatile("addi x4, x4, 10");               
  __asm__ volatile("addi x4, x4, 10");               
  __asm__ volatile("addi x4, x4, 10");               
  __asm__ volatile("addi x4, x4, 10");               
  __asm__ volatile("addi x4, x4, 10");               
  __asm__ volatile("addi x4, x4, 10");               
  __asm__ volatile("addi x4, x4, 10");               
  __asm__ volatile("addi x4, x4, 10");               
  __asm__ volatile("addi x4, x4, 10");               
  __asm__ volatile("addi x4, x4, 10");               
  __asm__ volatile("addi x4, x4, 10");               
  __asm__ volatile("addi x4, x4, 10");               
  __asm__ volatile("addi x4, x4, 10");               
  __asm__ volatile("addi x4, x4, 10");               
  __asm__ volatile("addi x4, x4, 10");               
  __asm__ volatile("addi x4, x4, 10");               
  __asm__ volatile("addi x4, x4, 10");               
  __asm__ volatile("addi x4, x4, 10");               
  __asm__ volatile("addi x4, x4, 10");               
  __asm__ volatile("addi x4, x4, 10");               
  __asm__ volatile("addi x4, x4, 10");               
  __asm__ volatile("addi x4, x4, 10");               
  __asm__ volatile("addi x4, x4, 10");               
  __asm__ volatile("addi x4, x4, 10");               
  __asm__ volatile("addi x4, x4, 10");               
  __asm__ volatile("addi x4, x4, 10");               
  __asm__ volatile("addi x4, x4, 10");               
  __asm__ volatile("addi x4, x4, 10");               
  __asm__ volatile("addi x4, x4, 10");               
  __asm__ volatile("addi x4, x4, 10");               
  __asm__ volatile("addi x4, x4, 10");               
  __asm__ volatile("addi x4, x4, 10");               
  __asm__ volatile("addi x4, x4, 10");               
  __asm__ volatile("addi x4, x4, 10");               
  __asm__ volatile("addi x4, x4, 10");               
  __asm__ volatile("addi x4, x4, 10");               
  __asm__ volatile("addi x4, x4, 10");               
  __asm__ volatile("addi x4, x4, 10");               
  __asm__ volatile("addi x4, x4, 10");               
  __asm__ volatile("addi x4, x4, 10");               
  __asm__ volatile("addi x4, x4, 10");               
  __asm__ volatile("addi x4, x4, 10");               
  __asm__ volatile("addi x4, x4, 10");               
  __asm__ volatile("addi x4, x4, 10");               
  __asm__ volatile("addi x4, x4, 10");               
  __asm__ volatile("addi x4, x4, 10");               
  __asm__ volatile("addi x4, x4, 10");               
  __asm__ volatile("addi x4, x4, 10");               
  __asm__ volatile("addi x4, x4, 10");               
  __asm__ volatile("addi x4, x4, 10");               
  __asm__ volatile("addi x4, x4, 10");               
  __asm__ volatile("addi x4, x4, 10");               
  __asm__ volatile("addi x4, x4, 10");               
  __asm__ volatile("addi x4, x4, 10");               
  __asm__ volatile("addi x4, x4, 10");               
  __asm__ volatile("addi x4, x4, 10");               
  __asm__ volatile("addi x4, x4, 10");               
  __asm__ volatile("addi x4, x4, 10");               
  __asm__ volatile("addi x4, x4, 10");               
  __asm__ volatile("addi x4, x4, 10");               
  __asm__ volatile("addi x4, x4, 10");               
  __asm__ volatile("addi x4, x4, 10");               
  __asm__ volatile("addi x4, x4, 10");               
  __asm__ volatile("addi x4, x4, 10");               
  __asm__ volatile("addi x4, x4, 10");               
  __asm__ volatile("addi x4, x4, 10");               
  __asm__ volatile("addi x4, x4, 10");               
  __asm__ volatile("addi x4, x4, 10");               
  __asm__ volatile("addi x4, x4, 10");               
  __asm__ volatile("addi x4, x4, 10");               
  __asm__ volatile("addi x4, x4, 10");               
  __asm__ volatile("addi x4, x4, 10");               
  __asm__ volatile("addi x4, x4, 10");               
  __asm__ volatile("addi x4, x4, 10");               
  __asm__ volatile("addi x4, x4, 10");               
  __asm__ volatile("addi x4, x4, 10");               
  __asm__ volatile("addi x4, x4, 10");               
  __asm__ volatile("addi x4, x4, 10");               
  __asm__ volatile("addi x4, x4, 10");               
  __asm__ volatile("addi x4, x4, 10");               
  __asm__ volatile("addi x4, x4, 10");               
  __asm__ volatile("addi x4, x4, 10");               
  __asm__ volatile("addi x4, x4, 10");               
  __asm__ volatile("addi x4, x4, 10");               
  __asm__ volatile("addi x4, x4, 10");               
  __asm__ volatile("addi x4, x4, 10");               
  __asm__ volatile("addi x4, x4, 10");               
  __asm__ volatile("addi x4, x4, 10");               
  __asm__ volatile("addi x4, x4, 10");               
  __asm__ volatile("addi x4, x4, 10");               
  __asm__ volatile("addi x4, x4, 10");               
  __asm__ volatile("addi x4, x4, 10");               
  __asm__ volatile("addi x4, x4, 10");               
  __asm__ volatile("addi x4, x4, 10");               
  __asm__ volatile("addi x4, x4, 10");               
  __asm__ volatile("addi x4, x4, 10");               
  __asm__ volatile("addi x4, x4, 10");               
  __asm__ volatile("addi x4, x4, 10");               
  __asm__ volatile("addi x4, x4, 10");               
  __asm__ volatile("addi x4, x4, 10");               
  __asm__ volatile("addi x4, x4, 10");               
  __asm__ volatile("addi x4, x4, 10");               
  __asm__ volatile("addi x4, x4, 10");               
  __asm__ volatile("addi x4, x4, 10");               
  __asm__ volatile("addi x4, x4, 10");               
  __asm__ volatile("addi x4, x4, 10");               
  __asm__ volatile("addi x4, x4, 10");               
  __asm__ volatile("addi x4, x4, 10");               
  __asm__ volatile("addi x4, x4, 10");               
  __asm__ volatile("addi x4, x4, 10");               
  __asm__ volatile("addi x4, x4, 10");               
  __asm__ volatile("addi x4, x4, 10");               
  __asm__ volatile("addi x4, x4, 10");               
  __asm__ volatile("addi x4, x4, 10");               
  __asm__ volatile("addi x4, x4, 10");               
  __asm__ volatile("addi x4, x4, 10");               
  __asm__ volatile("addi x4, x4, 10");               
  __asm__ volatile("addi x4, x4, 10");               
  __asm__ volatile("addi x4, x4, 10");               
  __asm__ volatile("addi x4, x4, 10");               
  __asm__ volatile("addi x4, x4, 10");               
  __asm__ volatile("jump_target_5:");
  __asm__ volatile("j jump_target_6");                          // count++
  __asm__ volatile("jump_target_6:");
  __asm__ volatile("csrwi 0x320, 0x1F");                        // Inhibit mcycle, minstret, mhpmcounter3-4
  __asm__ volatile("csrr %0, 0xB02" : "=r"(minstret_rval));          // minstret
  __asm__ volatile("csrr %0, 0xB03" : "=r"(count));             // mhpmcounter3

  printf("\nminstret count = %d\n", minstret_rval);
  err_cnt += chck(minstret_rval, 4);

  printf("Jump count = %d\n", count);
  err_cnt += chck(count, 0);

  //////////////////////////////////////////////////////////////
  // Count branches (conditional)
  printf("\nCount branches (conditional)");

  event = 0x100;                                                // Trigger on on taken branches
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
  __asm__ volatile("csrr %0, 0xB02" : "=r"(minstret_rval));          // minstret
  __asm__ volatile("csrr %0, 0xB03" : "=r"(count));             // mhpmcounter3

  printf("\nminstret count = %d\n", minstret_rval);
  err_cnt += chck(minstret_rval, 4);

  printf("Branch count = %d\n", count);
  err_cnt += chck(count, 3);

  //////////////////////////////////////////////////////////////
  // Count branches taken (conditional)
  printf("\nCount branches taken (conditional)");

  event = 0x200;                                                // Trigger on on taken branches
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
  __asm__ volatile("csrr %0, 0xB02" : "=r"(minstret_rval));          // minstret
  __asm__ volatile("csrr %0, 0xB03" : "=r"(count));             // mhpmcounter3

  printf("\nminstret count = %d\n", minstret_rval);
  err_cnt += chck(minstret_rval, 4);

  printf("Branch taken count = %d\n", count);
  err_cnt += chck(count, 2);

  //////////////////////////////////////////////////////////////
  // Compressed instructions
  printf("\nCompressed instructions");

  event = 0x400;                                                // Trigger on compressed instructions
  __asm__ volatile("csrw 0x323, %0 " : : "r"(event));           // Set mhpmevent3
  __asm__ volatile("csrwi 0xB02, 0x0");                         // minstret = 0
  __asm__ volatile("csrwi 0xB03, 0x0");                         // mhpmcounter3 = 0
  __asm__ volatile("csrwi 0x320, 0x0");                         // Enable counters
  __asm__ volatile("c.addi x15, 1\n\t\
                    c.nop\n\t\
                    c.addi x15, 1" \
                    : : : "x15");
  __asm__ volatile("csrwi 0x320, 0x1F");                        // Inhibit mcycle, minstret, mhpmcounter3-4
  __asm__ volatile("csrr %0, 0xB02" : "=r"(minstret_rval));          // minstret
  __asm__ volatile("csrr %0, 0xB03" : "=r"(count));             // mhpmcounter3

  printf("\nminstret count = %d\n", minstret_rval);
  err_cnt += chck(minstret_rval, 4);

  printf("Compressed count = %d\n", count);
  err_cnt += chck(count, 3);

  //////////////////////////////////////////////////////////////
  // Retired instruction count
  printf("\nRetired instruction count");

  event = 0x2;                                                  // Trigger on retired instructions
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
  __asm__ volatile("csrr %0, 0xB02" : "=r"(minstret_rval));          // minstret
  __asm__ volatile("csrr %0, 0xB03" : "=r"(count));             // mhpmcounter3

  printf("\nminstret count = %d\n", minstret_rval);
  err_cnt += chck(minstret_rval, 5 + 6*5 + 4 + 1);

  printf("Retired instruction count = %d\n", count);
  err_cnt += chck(count, 5 + 6*5 + 4 + 1);

  //////////////////////////////////////////////////////////////
  // Check for errors
  printf("\nDone");

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


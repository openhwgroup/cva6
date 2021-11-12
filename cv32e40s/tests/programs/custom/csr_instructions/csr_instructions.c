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
** CSR instruction test: Execute each Zicsr instruction at least once.
**                       This test exists purely to debug functional coverage.
**
*******************************************************************************
*/

#include <stdio.h>
#include <stdlib.h>

int main(int argc, char *argv[])
{
  unsigned int readd;  // Read data
  unsigned int writed; // Write data
  unsigned int mask;   // Make value

  int err_cnt, sum;

  readd   = 0;
  writed  = 0;
  mask    = 0;
  err_cnt = 0;
  sum     = 0;

  printf("\n\nCSR Instruction Test\n");

  // Control and Status Register Read
  // pseudoinstruction: expands to csrrs rd, csr, x0
  __asm__ volatile("csrr %0, 0x340" : "=r"(readd));    // CSR 0x340 is a 32-bit R/W scratch-pad

  // Control and Status Register Clear
  // pseudoinstruction: expands to csrrc x0, csr, rs1
  __asm__ volatile("csrc 0x340, %0" : "=r"(writed));

  // Control and Status Register Clear Immediate
  // pseudoinstruction: expands to csrrci x0, csr, zimm
  __asm__ volatile("csrci 0x340, 0xF");

  // Control and Status Register Read and Clear
  __asm__ volatile("csrrc %0, 0x340, %1" : "=r"(readd) : "r"(mask));

  // Control and Status Register Read and Clear Immediate
  __asm__ volatile("csrrci %0, 0x340, 0xF" : "=r"(readd));

  // Control and Status Register Read and Set
  __asm__ volatile("csrrs %0, 0x340, %1" : "=r"(readd) : "r"(mask));

  // Control and Status Register Read and Set Immediate
  __asm__ volatile("csrrsi %0, 0x340, 0xF" : "=r"(readd));

  // Control and Status Register Read and Write
  __asm__ volatile("csrrw %0, 0x340, %1" : "=r"(readd) : "r"(mask));

  // Control and Status Register Read and Write Immediate
  __asm__ volatile("csrrwi %0, 0x340, 0xF" : "=r"(readd));

  // Control and Status Register Set
  // pseudoinstruction: expands to csrrs x0, csr, rs1
  __asm__ volatile("csrs 0x340, %0" : "=r"(mask));

  // Control and Status Register Set Immediate
  // pseudoinstruction: expands to csrrsi x0, csr, zimm
  __asm__ volatile("csrsi 0x340, 0xF");

  // Control and Status Register Write
  // pseudoinstruction: expands to csrrw x0, csr, rs1
  __asm__ volatile("csrw 0x340, %0" : "=r"(mask));

  // Control and Status Register Write Immediate
  // pseudoinstruction: expands to csrrwi x0, csr, rs1
  __asm__ volatile("csrwi 0x340, 0xF");

  printf("\n\nMSTATUS (0x300) CSR Write-Read Test\n");
  // Control and Status Register Read
  // pseudoinstruction: expands to csrrs rd, csr, x0
  __asm__ volatile("csrr %0, 0x300" : "=r"(readd));
  printf("MSTATUS Read Value is %0x\n", readd);
  // Control and Status Register Write
  // pseudoinstruction: expands to csrrw x0, csr, rs1
  mask = 0xFFFFFFFF;
  __asm__ volatile("li a5, 0x0");
  __asm__ volatile("li a5,0xFFFFFFFF");
  __asm__ volatile("csrw 0x300, a5");
  // Control and Status Register Read
  // pseudoinstruction: expands to csrrs rd, csr, x0
  __asm__ volatile("csrr %0, 0x300" : "=r"(readd));
  printf("MSTATUS Read Value is %0x\n", readd);



  printf("DONE!\n\n");

	if (!err_cnt) {
    return EXIT_SUCCESS;
	} else {
    printf("\n%0d failures\n", sum);
    return EXIT_FAILURE;
	}

}

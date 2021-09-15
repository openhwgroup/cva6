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
** Sanity test for the CV32E40X core.  Reads the MISA and MVENDORID CSRs and
**                                     prints some useful (?) messages to
**                                     stdout.  Will fail if MISA is not sane.
**
*******************************************************************************
*/

#include <stdio.h>
#include <stdlib.h>

int main(int argc, char *argv[])
{
    unsigned int mvendorid_rval, misa_rval, mxl;
             int reserved, tentative, nonstd, user, super;

    mxl = 0; reserved = 0; tentative = 0; nonstd = 0; user = 0; super = 0;

    /* inline assembly: read mvendorid and misa */
    asm volatile("ecall");
    __asm__ volatile("csrr %0, 0xF11" : "=r"(mvendorid_rval));
    __asm__ volatile("csrr %0, 0x301" : "=r"(misa_rval));

    /* Check MISA CSR: if its zero, it might not be implemented at all */
    if (misa_rval == 0x0) {
      printf("\tERROR: CSR MISA returned zero!\n\n");
      return EXIT_FAILURE;
    }

    /* Print a banner to stdout and interpret MISA CSR */
    printf("\nThis is the OpenHW Group CV32E40X RISC-V processor core\n");
    printf("running an example \"custom\" test-program.\n");
    printf("Please consult the CORE-V Verification Strategy for more information\n");
    printf("on the distinction between a UVM testcase and a core test-program.\n");
    printf("\tmvendorid = 0x%0x\n", mvendorid_rval);
    printf("\tmisa      = 0x%0x\n", misa_rval);
    mxl = ((misa_rval & 0xC0000000) >> 30); // MXL == MISA[31:30]
    switch (mxl) {
      case 0:  printf("\tERROR: MXL cannot be zero!\n");
               return EXIT_FAILURE;
               break;
      case 1:  printf("\tXLEN is 32-bits\n");
               break;
      case 2:  printf("\tXLEN is 64-bits\n");
               break;
      case 3:  printf("\tXLEN is 128-bits\n");
               break;
      default: printf("\tERROR: mxl (%0d) not in 0..3, your code is broken!\n", mxl);
               return EXIT_FAILURE;
    }

    printf("\tSupported Instructions: ");
    if ((misa_rval >> 25) & 0x00000001) ++reserved;
    if ((misa_rval >> 24) & 0x00000001) ++reserved;
    if ((misa_rval >> 23) & 0x00000001) ++nonstd;
    if ((misa_rval >> 22) & 0x00000001) ++reserved;
    if ((misa_rval >> 21) & 0x00000001) ++tentative;
    if ((misa_rval >> 20) & 0x00000001) ++user;
    if ((misa_rval >> 19) & 0x00000001) ++tentative;
    if ((misa_rval >> 18) & 0x00000001) ++super;
    if ((misa_rval >> 17) & 0x00000001) ++reserved;
    if ((misa_rval >> 16) & 0x00000001) printf("Q");
    if ((misa_rval >> 15) & 0x00000001) ++tentative;
    if ((misa_rval >> 14) & 0x00000001) ++reserved;
    if ((misa_rval >> 13) & 0x00000001) printf("N");
    if ((misa_rval >> 12) & 0x00000001) printf("M");
    if ((misa_rval >> 11) & 0x00000001) ++tentative;
    if ((misa_rval >> 10) & 0x00000001) ++reserved;
    if ((misa_rval >>  9) & 0x00000001) printf("J");
    if ((misa_rval >>  8) & 0x00000001) printf("I");
    if ((misa_rval >>  7) & 0x00000001) printf("H");
    if ((misa_rval >>  6) & 0x00000001) printf("G");
    if ((misa_rval >>  5) & 0x00000001) printf("F");
    if ((misa_rval >>  4) & 0x00000001) printf("E");
    if ((misa_rval >>  3) & 0x00000001) printf("D");
    if ((misa_rval >>  2) & 0x00000001) printf("C");
    if ((misa_rval >>  1) & 0x00000001) printf("B");
    if ((misa_rval      ) & 0x00000001) printf("A");
    printf("\n");
    if (super) {
      printf("\tThis machine supports SUPERVISOR mode.\n");
    }
    if (user) {
      printf("\tThis machine supports USER mode.\n");
    }
    if (nonstd) {
      printf("\tThis machine supports non-standard instructions.\n");
    }
    if (tentative) {
      printf("\tWARNING: %0d tentative instruction extensions are defined!\n", tentative);
    }
    if (reserved) {
      printf("\tERROR: %0d reserved instruction extensions are defined!\n\n", reserved);
      return EXIT_FAILURE;
    }
    else {
      printf("\n");
      return EXIT_SUCCESS;
    }
}

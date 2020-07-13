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
** CSR power-on-reset test:   Reads the CSRs and prints some useful (?)
**                            messages to stdout.  Will fail if PoR not correct.
**
*******************************************************************************
*/

#include <stdio.h>
#include <stdlib.h>

int main(int argc, char *argv[])
{
    unsigned int mvendorid_rval, misa_rval, marchid_rval, mimpid_rval, mhartid_rval;
    unsigned int mxl;
             int reserved, tentative, nonstd, user, super, err_cnt;

    mxl = 0; reserved = 0; tentative = 0; nonstd = 0; user = 0; super = 0; err_cnt = 0;

    /* inline assembly: read mvendorid and misa */
    __asm__ volatile("csrr %0, 0xF11" : "=r"(mvendorid_rval));
    __asm__ volatile("csrr %0, 0xF12" : "=r"(marchid_rval));
    __asm__ volatile("csrr %0, 0xF13" : "=r"(mimpid_rval));
    __asm__ volatile("csrr %0, 0xF14" : "=r"(mhartid_rval));
    __asm__ volatile("csrr %0, 0x301" : "=r"(misa_rval));

	printf("\n\n");

    /* Check MVENDOR CSR: should be 0 */
    if (mvendorid_rval != 0x0) {
      printf("ERROR: CSR MVENDOR not zero!\n\n");
      ++err_cnt;
    }

    /* Check MARCHID CSR: should be 0 */
    if (marchid_rval != 0x0) {
      printf("ERROR: CSR MARCHID not zero!\n\n");
      ++err_cnt;
    }

    /* Check MIMPLID CSR: should be 0 */
    if (mimpid_rval != 0x0) {
      printf("ERROR: CSR MIMPLID not zero!\n\n");
      ++err_cnt;
    }

    /* Check MISA CSR: if its zero, it might not be implemented at all */
    if (misa_rval == 0x0) {
      printf("ERROR: CSR MISA returned zero!\n\n");
      ++err_cnt;
    }

    /* Check MHARTID CSR: fail if its zero, */
    if (mhartid_rval == 0x0) {
      printf("ERROR: CSR MHARTID returned zero!\n\n");
      ++err_cnt;
    }

    /* Print a banner to stdout and interpret MISA CSR */
    printf("\nCSR PoR Test\n");
    printf("\tmvendorid = 0x%0x\n", mvendorid_rval);
    printf("\tmmarchid  = 0x%0x\n", marchid_rval);
    printf("\tmimpid    = 0x%0x\n", mimpid_rval);
    printf("\tmhartid   = 0x%0x\n", mhartid_rval);
    printf("\tmisa      = 0x%0x\n", misa_rval);
	printf("\n\n");

	if (!err_cnt) {
      return EXIT_SUCCESS;
	} else {
      return EXIT_FAILURE;
	}

}

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
**                            messages to stdout.  Will fail if read value does
**                            not match the documented PoR value.
**
** This is a manually written prototype of a (planned) generated test-program.
** In this prototype, all addresses and expected values are hand-coded.
**
*******************************************************************************
*/

#include <stdio.h>
#include <stdlib.h>

int main(int argc, char *argv[])
{
	// User CSRs
    unsigned int fflags_rval, frm_rval, fcsr_rval;
	// User Custom CSRs
	unsigned int lpstart0_rval, lpend0_rval, lpcount0_rval, lpstart1_rval, lpend1_rval, lpcount1_rval;
	unsigned int fprec_rval, privlv_rval, uhartid_rval;
	// Machine CSRs
	unsigned int mstatus_rval, misa_rval, mie_rval, mtvec_rval;
	//unsigned int mcounteren_rval, mcountinhibit_rval;
	//unsigned int mphmevent3_rval; //make array 31..3
	//
    unsigned int mvendorid_rval, marchid_rval, mimpid_rval, mhartid_rval;
    unsigned int mxl;
             int reserved, tentative, nonstd, user, super, err_cnt;

    mxl = 0; reserved = 0; tentative = 0; nonstd = 0; user = 0; super = 0; err_cnt = 0;

	printf("\n\n");

    // These CSRs only exist if FPU=1 at RTL compile-time.
	// Reading these when FPU=0 yields an illegal instruction exception (which is not tested here).
    //__asm__ volatile("csrr %0, 0x001" : "=r"(fflags_rval));
    //__asm__ volatile("csrr %0, 0x002" : "=r"(frm_rval));
    //__asm__ volatile("csrr %0, 0x003" : "=r"(fcsr_rval));

	/*
    if (fflags_rval != 0x0) {
      printf("ERROR: CSR FFLAGS not zero!\n\n");
      ++err_cnt;
    }
    if (frm_rval != 0x0) {
      printf("ERROR: CSR FRM not zero!\n\n");
      ++err_cnt;
    }
    if (fcsr_rval != 0x0) {
      printf("ERROR: CSR FCSR not zero!\n\n");
      ++err_cnt;
    }
	*/

	/*
    __asm__ volatile("csrr %0, 0x7C0" : "=r"(lpstart0_rval));
    __asm__ volatile("csrr %0, 0x7C1" : "=r"(lpend0_rval));
    __asm__ volatile("csrr %0, 0x7C2" : "=r"(lpcount0_rval));
    __asm__ volatile("csrr %0, 0x7C4" : "=r"(lpstart1_rval));
    __asm__ volatile("csrr %0, 0x7C5" : "=r"(lpend1_rval));
    __asm__ volatile("csrr %0, 0x7C6" : "=r"(lpcount1_rval));
 
	//
    if (lpstart0_rval != 0x0) {
      printf("ERROR: CSR LPSTART0 not zero!\n\n");
      ++err_cnt;
    }
    if (lpend0_rval != 0x0) {
      printf("ERROR: CSR LPEND0 not zero!\n\n");
      ++err_cnt;
    }
    if (lpcount0_rval != 0x0) {
      printf("ERROR: CSR LPCOUNT0 not zero!\n\n");
      ++err_cnt;
    }
    if (lpstart1_rval != 0x0) {
      printf("ERROR: CSR LPSTART1 not zero!\n\n");
      ++err_cnt;
    }
    if (lpend1_rval != 0x0) {
      printf("ERROR: CSR LPEND1 not zero!\n\n");
      ++err_cnt;
    }
    if (lpcount1_rval != 0x0) {
      printf("ERROR: CSR LPCOUNT1 not zero!\n\n");
      ++err_cnt;
    }
	*/

    //__asm__ volatile("csrr %0, 0x006" : "=r"(fprec_rval));
    __asm__ volatile("csrr %0, 0xC10" : "=r"(privlv_rval));
    //__asm__ volatile("csrr %0, 0xC14" : "=r"(uhartid_rval));

    //if (fprec_rval != 0x0) {
    //  printf("ERROR: CSR FPREC not zero!\n\n");
    //  ++err_cnt;
    //}
    if (privlv_rval != 0x3) {
      printf("ERROR: CSR PRIVLV not 0x3!\n\n");
      ++err_cnt;
    }
    //if (uhartid_rval != 0x0) {
    //  printf("ERROR: CSR UHARTID not zero!\n\n");
    //  ++err_cnt;
    //}

    __asm__ volatile("csrr %0, 0x300" : "=r"(mstatus_rval));
    __asm__ volatile("csrr %0, 0x301" : "=r"(misa_rval));
    __asm__ volatile("csrr %0, 0x304" : "=r"(mie_rval));
    __asm__ volatile("csrr %0, 0x305" : "=r"(mtvec_rval));

    if (mstatus_rval != 0x1800) {
      printf("ERROR: CSR MSTATUS not 0x1800!\n\n");
      ++err_cnt;
    }
    if (misa_rval != 0x40801104) {
      printf("ERROR: CSR MISA not 0x0!\n\n");
      ++err_cnt;
    }
    if (mie_rval != 0x0) {
      printf("ERROR: CSR MIE not 0x0!\n\n");
      ++err_cnt;
    }
    if (mtvec_rval != 0x0001) {
      printf("ERROR: CSR MTVEC not 0x0!\n\n");
      ++err_cnt;
    }

    __asm__ volatile("csrr %0, 0xF11" : "=r"(mvendorid_rval));
    __asm__ volatile("csrr %0, 0xF12" : "=r"(marchid_rval));
    __asm__ volatile("csrr %0, 0xF13" : "=r"(mimpid_rval));
    __asm__ volatile("csrr %0, 0xF14" : "=r"(mhartid_rval));

    if (mvendorid_rval != 0x0602) {
      printf("ERROR: CSR MVENDOR not zero!\n\n");
      ++err_cnt;
    }

    if (marchid_rval != 0x0) {
      printf("ERROR: CSR MARCHID not zero!\n\n");
      ++err_cnt;
    }

    if (mimpid_rval != 0x0) {
      printf("ERROR: CSR MIMPLID not zero!\n\n");
      ++err_cnt;
    }

    if (mhartid_rval != 0x0) {
      printf("ERROR: CSR MHARTID not zero!\n\n");
      ++err_cnt;
    }

    /* Print a banner to stdout and interpret MISA CSR */
    printf("\nCSR PoR Test\n");
    //printf("\tlpstart0  = 0x%0x\n", lpstart0_rval);
    //printf("\tlpend0    = 0x%0x\n", lpend0_rval);
    //printf("\tlpcount0  = 0x%0x\n", lpcount0_rval);
    //printf("\tlpstart1  = 0x%0x\n", lpstart1_rval);
    //printf("\tlpend1    = 0x%0x\n", lpend1_rval);
    //printf("\tlpcount1  = 0x%0x\n", lpcount1_rval);
    printf("\tprivlv    = 0x%0x\n", privlv_rval);
    printf("\tmstatus   = 0x%0x\n", mstatus_rval);
    printf("\tmisa      = 0x%0x\n", misa_rval);
    printf("\tmie       = 0x%0x\n", mie_rval);
    printf("\tmtvec     = 0x%0x\n", mtvec_rval);
    printf("\tmvendorid = 0x%0x\n", mvendorid_rval);
    printf("\tmmarchid  = 0x%0x\n", marchid_rval);
    printf("\tmimpid    = 0x%0x\n", mimpid_rval);
    printf("\tmhartid   = 0x%0x\n", mhartid_rval);
	printf("\n\n");

	if (!err_cnt) {
      return EXIT_SUCCESS;
	} else {
	  // TODO: drive virtual peripheral in TB to signal testcase failure
      return EXIT_FAILURE;
	}

}

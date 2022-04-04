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
** The primary goals of this test-program is to get proof of life from all CV32E40S
** CSRs and asertain the status of CSR modeling in the OVPsim Reference Model.
** In this prototype, all addresses and expected values are hand-coded.
**
*******************************************************************************
*/

#include <stdio.h>
#include <stdlib.h>

#define EXP_MISA 0x40101104

int main(int argc, char *argv[])
{
  // User CSRs
  // Not in RM
  // unsigned int fflags_rval, frm_rval, fcsr_rval;
  // User Custom CSRs
  // Not in RM
  // unsigned int lpstart0_rval, lpend0_rval, lpcount0_rval, lpstart1_rval, lpend1_rval, lpcount1_rval;
  // unsigned int fprec_rval, privlv_rval, uhartid_rval;
  // Machine CSRs
  unsigned int mstatus_rval, misa_rval, mie_rval, mtvec_rval;
  unsigned int mcounteren_rval, mcountinhibit_rval, mphmevent_rval[32];
  unsigned int mscratch_rval, mepc_rval, mcause_rval, mtval_rval, mip_rval;
  unsigned int tselect_rval, tdata1_rval, tdata2_rval, tdata3_rval, tinfo_rval;
  unsigned int mcontext_rval, scontext_rval, dcsr_rval, dpc_rval, dscratch0_rval, dscratch1_rval;
  unsigned int mcycle_rval, minstret_rval, mhpmcounter_rval[32], mcycleh_rval;
  unsigned int minstreth_rval, mhpmcounterh[32];
  unsigned int mvendorid_rval, marchid_rval, mimpid_rval, mhartid_rval;

  int err_cnt, sum;

  err_cnt = 0;
  sum     = 0;

	printf("\n\n");

  __asm__ volatile("csrr %0, 0x300" : "=r"(mstatus_rval));
  __asm__ volatile("csrr %0, 0x301" : "=r"(misa_rval));
  __asm__ volatile("csrr %0, 0x304" : "=r"(mie_rval));
  __asm__ volatile("csrr %0, 0x305" : "=r"(mtvec_rval));

  if (mstatus_rval != 0x1800) {
    printf("ERROR: CSR MSTATUS not 0x1800!\n\n");
    ++err_cnt;
  }
  if (misa_rval != EXP_MISA) {
    printf("ERROR: CSR MISA not 0x%x!\n\n", EXP_MISA);
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

  // This doesn't work because __asm__ is a macro (sigh)
  //num = (int)strtol(addr, NULL, 16);
  //for (int i=3; i<32; i++) {
  //  n = sprintf(string, "csrr %%0, 0x%0x", num++);
  //  printf("%s\n",string);
  //  __asm__ volatile(string : "=r"(mphmevent_rval[i]));
  //}
  __asm__ volatile("csrr %0, 0x323" : "=r"(mphmevent_rval[3]));
  //__asm__ volatile("csrr %0, 0x324" : "=r"(mphmevent_rval[4]));
  //__asm__ volatile("csrr %0, 0x325" : "=r"(mphmevent_rval[5]));
  //__asm__ volatile("csrr %0, 0x326" : "=r"(mphmevent_rval[6]));
  //__asm__ volatile("csrr %0, 0x327" : "=r"(mphmevent_rval[7]));
  //__asm__ volatile("csrr %0, 0x328" : "=r"(mphmevent_rval[8]));
  //__asm__ volatile("csrr %0, 0x329" : "=r"(mphmevent_rval[9]));
  //__asm__ volatile("csrr %0, 0x32A" : "=r"(mphmevent_rval[10]));
  //__asm__ volatile("csrr %0, 0x32B" : "=r"(mphmevent_rval[11]));
  //__asm__ volatile("csrr %0, 0x32C" : "=r"(mphmevent_rval[12]));
  //__asm__ volatile("csrr %0, 0x32D" : "=r"(mphmevent_rval[13]));
  //__asm__ volatile("csrr %0, 0x32E" : "=r"(mphmevent_rval[14]));
  //__asm__ volatile("csrr %0, 0x32F" : "=r"(mphmevent_rval[15]));
  //__asm__ volatile("csrr %0, 0x330" : "=r"(mphmevent_rval[16]));
  //__asm__ volatile("csrr %0, 0x331" : "=r"(mphmevent_rval[17]));
  //__asm__ volatile("csrr %0, 0x332" : "=r"(mphmevent_rval[18]));
  //__asm__ volatile("csrr %0, 0x333" : "=r"(mphmevent_rval[19]));
  //__asm__ volatile("csrr %0, 0x334" : "=r"(mphmevent_rval[20]));
  //__asm__ volatile("csrr %0, 0x335" : "=r"(mphmevent_rval[21]));
  //__asm__ volatile("csrr %0, 0x336" : "=r"(mphmevent_rval[22]));
  //__asm__ volatile("csrr %0, 0x337" : "=r"(mphmevent_rval[23]));
  //__asm__ volatile("csrr %0, 0x338" : "=r"(mphmevent_rval[24]));
  //__asm__ volatile("csrr %0, 0x339" : "=r"(mphmevent_rval[25]));
  //__asm__ volatile("csrr %0, 0x33A" : "=r"(mphmevent_rval[26]));
  //__asm__ volatile("csrr %0, 0x33B" : "=r"(mphmevent_rval[27]));
  //__asm__ volatile("csrr %0, 0x33C" : "=r"(mphmevent_rval[28]));
  //__asm__ volatile("csrr %0, 0x33D" : "=r"(mphmevent_rval[29]));
  //__asm__ volatile("csrr %0, 0x33E" : "=r"(mphmevent_rval[30]));
  //__asm__ volatile("csrr %0, 0x33F" : "=r"(mphmevent_rval[31]));

  //for (int i=3; i<32; i++) {
  for (int i=3; i<4; i++) {
    sum += mphmevent_rval[i];
  }
  if (sum) {
    //printf("ERROR: CSR MPHMEVENT[3..31] not 0x0!\n\n");
    printf("ERROR: CSR MPHMEVENT[3] not 0x0!\n\n");
    ++err_cnt;
  }

  __asm__ volatile("csrr %0, 0x7A0" : "=r"(tselect_rval)); // unimplemented in model, hardwired to zero
  __asm__ volatile("csrr %0, 0x7A1" : "=r"(tdata1_rval));  // unimplemented in model, hardwired to zero
  __asm__ volatile("csrr %0, 0x7A2" : "=r"(tdata2_rval));  // unimplemented in model, hardwired to zero
  __asm__ volatile("csrr %0, 0x7A3" : "=r"(tdata3_rval));  // unimplemented in model, hardwired to zero
  __asm__ volatile("csrr %0, 0x7A4" : "=r"(tinfo_rval));   // unimplemented in model

  if (tselect_rval != 0x0) {
    printf("ERROR: CSR TSELECT not zero!\n\n");
    ++err_cnt;
  }

  if (tdata1_rval != 0x28001040) {
    printf("ERROR: CSR TDATA1 not 0x28001040!\n\n");
    ++err_cnt;
  }

  if (tdata2_rval != 0x0) {
    printf("ERROR: CSR TDATA2 not 0x0!\n\n");
    ++err_cnt;
  }

  if (tdata3_rval != 0x0) {
    printf("ERROR: CSR TDATA3 not 0x0!\n\n");
    ++err_cnt;
  }

  if (tinfo_rval != 0x4) {
    printf("ERROR: CSR TINFO not 0x4!\n\n");
    ++err_cnt;
  }

  __asm__ volatile("csrr %0, 0x7A8" : "=r"(mcontext_rval));  // unimplemented in model
  __asm__ volatile("csrr %0, 0x7AA" : "=r"(scontext_rval));  // unimplemented in model
  // IMPERAS - Debug mode enabled
  //__asm__ volatile("csrr %0, 0x7B0" : "=r"(dcsr_rval));      // only accessible in Debug mode
  //__asm__ volatile("csrr %0, 0x7B1" : "=r"(dpc_rval));       // only accessible in Debug mode
  //__asm__ volatile("csrr %0, 0x7B2" : "=r"(dscratch0_rval)); // only accessible in Debug mode
  //__asm__ volatile("csrr %0, 0x7B3" : "=r"(dscratch1_rval)); // only accessible in Debug mode

  if (mcontext_rval != 0x0) {
    printf("ERROR: CSR MCONTEXT not 0x0!\n\n");
    ++err_cnt;
  }

  if (scontext_rval != 0x0) {
    printf("ERROR: CSR SCONTEXT not 0x0!\n\n");
    ++err_cnt;
  }

  //if (dcsr_rval != 0x0) {
  //  printf("ERROR: CSR DCSR not 0x0!\n\n");
  //  ++err_cnt;
  //}

  //if (dpc_rval != 0x0) {
  //  printf("ERROR: CSR DPC not 0x0!\n\n");
  //  ++err_cnt;
  //}

  //if (dscratch0_rval != 0x0) {
  //  printf("ERROR: CSR DSCRATCH0 not 0x0!\n\n");
  //  ++err_cnt;
  //}

  //if (dscratch1_rval != 0x0) {
  //  printf("ERROR: CSR DSCRATCH1 not 0x0!\n\n");
  //  ++err_cnt;
  //}

  __asm__ volatile("csrr %0, 0xB00" : "=r"(mcycle_rval));         // CSR unimplemented in the model
  __asm__ volatile("csrr %0, 0xB02" : "=r"(minstret_rval));       // CSR unimplmented in the model

  if (mcycle_rval != 0x0) {
    printf("ERROR: CSR MCYCLE not 0x0!\n\n");
    ++err_cnt;
  }

  if (minstret_rval != 0x0) {
    printf("ERROR: CSR MINSTRET not 0x0!\n\n");
    ++err_cnt;
  }

  __asm__ volatile("csrr %0, 0xB03" : "=r"(mhpmcounter_rval[3]));
  //__asm__ volatile("csrr %0, 0xB04" : "=r"(mhpmcounter_rval[4]));
  //__asm__ volatile("csrr %0, 0xB05" : "=r"(mhpmcounter_rval[5]));
  //__asm__ volatile("csrr %0, 0xB06" : "=r"(mhpmcounter_rval[6]));
  //__asm__ volatile("csrr %0, 0xB07" : "=r"(mhpmcounter_rval[7]));
  //__asm__ volatile("csrr %0, 0xB08" : "=r"(mhpmcounter_rval[8]));
  //__asm__ volatile("csrr %0, 0xB09" : "=r"(mhpmcounter_rval[9]));
  //__asm__ volatile("csrr %0, 0xB0A" : "=r"(mhpmcounter_rval[10]));
  //__asm__ volatile("csrr %0, 0xB0B" : "=r"(mhpmcounter_rval[11]));
  //__asm__ volatile("csrr %0, 0xB0C" : "=r"(mhpmcounter_rval[12]));
  //__asm__ volatile("csrr %0, 0xB0D" : "=r"(mhpmcounter_rval[13]));
  //__asm__ volatile("csrr %0, 0xB0E" : "=r"(mhpmcounter_rval[14]));
  //__asm__ volatile("csrr %0, 0xB0F" : "=r"(mhpmcounter_rval[15]));
  //__asm__ volatile("csrr %0, 0xB10" : "=r"(mhpmcounter_rval[16]));
  //__asm__ volatile("csrr %0, 0xB11" : "=r"(mhpmcounter_rval[17]));
  //__asm__ volatile("csrr %0, 0xB12" : "=r"(mhpmcounter_rval[18]));
  //__asm__ volatile("csrr %0, 0xB13" : "=r"(mhpmcounter_rval[19]));
  //__asm__ volatile("csrr %0, 0xB14" : "=r"(mhpmcounter_rval[20]));
  //__asm__ volatile("csrr %0, 0xB15" : "=r"(mhpmcounter_rval[21]));
  //__asm__ volatile("csrr %0, 0xB16" : "=r"(mhpmcounter_rval[22]));
  //__asm__ volatile("csrr %0, 0xB17" : "=r"(mhpmcounter_rval[23]));
  //__asm__ volatile("csrr %0, 0xB18" : "=r"(mhpmcounter_rval[24]));
  //__asm__ volatile("csrr %0, 0xB19" : "=r"(mhpmcounter_rval[25]));
  //__asm__ volatile("csrr %0, 0xB1A" : "=r"(mhpmcounter_rval[26]));
  //__asm__ volatile("csrr %0, 0xB1B" : "=r"(mhpmcounter_rval[27]));
  //__asm__ volatile("csrr %0, 0xB1C" : "=r"(mhpmcounter_rval[28]));
  //__asm__ volatile("csrr %0, 0xB1D" : "=r"(mhpmcounter_rval[29]));
  //__asm__ volatile("csrr %0, 0xB1E" : "=r"(mhpmcounter_rval[30]));
  //__asm__ volatile("csrr %0, 0xB1F" : "=r"(mhpmcounter_rval[31]));

  sum = 0;
  //for (int i=3; i<32; i++) {
  for (int i=3; i<4; i++) {
    sum += mhpmcounter_rval[i];
  }
  if (sum) {
    //printf("ERROR: CSR MHPMCOUNTER[3..31] not 0x0!\n\n");
    printf("ERROR: CSR MHPMCOUNTER[3] not 0x0!\n\n");
    ++err_cnt;
  }

  __asm__ volatile("csrr %0, 0xB80" : "=r"(mcycleh_rval));   // CSR unimplemented in the model

  if (mcycleh_rval != 0x0) {
    printf("ERROR: CSR MCYCLEH not 0x0!\n\n");
    ++err_cnt;
  }

  __asm__ volatile("csrr %0, 0xB82" : "=r"(minstreth_rval)); // CSR unimplemented in the model

  if (minstreth_rval != 0x0) {
    printf("ERROR: CSR MINSTRETH not 0x0!\n\n");
    ++err_cnt;
  }

  __asm__ volatile("csrr %0, 0xB83" : "=r"(mhpmcounterh[3]));
  //__asm__ volatile("csrr %0, 0xB84" : "=r"(mhpmcounterh[4]));
  //__asm__ volatile("csrr %0, 0xB85" : "=r"(mhpmcounterh[5]));
  //__asm__ volatile("csrr %0, 0xB86" : "=r"(mhpmcounterh[6]));
  //__asm__ volatile("csrr %0, 0xB87" : "=r"(mhpmcounterh[7]));
  //__asm__ volatile("csrr %0, 0xB88" : "=r"(mhpmcounterh[8]));
  //__asm__ volatile("csrr %0, 0xB89" : "=r"(mhpmcounterh[9]));
  //__asm__ volatile("csrr %0, 0xB8A" : "=r"(mhpmcounterh[10]));
  //__asm__ volatile("csrr %0, 0xB8B" : "=r"(mhpmcounterh[11]));
  //__asm__ volatile("csrr %0, 0xB8C" : "=r"(mhpmcounterh[12]));
  //__asm__ volatile("csrr %0, 0xB8D" : "=r"(mhpmcounterh[13]));
  //__asm__ volatile("csrr %0, 0xB8E" : "=r"(mhpmcounterh[14]));
  //__asm__ volatile("csrr %0, 0xB8F" : "=r"(mhpmcounterh[15]));
  //__asm__ volatile("csrr %0, 0xB90" : "=r"(mhpmcounterh[16]));
  //__asm__ volatile("csrr %0, 0xB91" : "=r"(mhpmcounterh[17]));
  //__asm__ volatile("csrr %0, 0xB92" : "=r"(mhpmcounterh[18]));
  //__asm__ volatile("csrr %0, 0xB93" : "=r"(mhpmcounterh[19]));
  //__asm__ volatile("csrr %0, 0xB94" : "=r"(mhpmcounterh[20]));
  //__asm__ volatile("csrr %0, 0xB95" : "=r"(mhpmcounterh[21]));
  //__asm__ volatile("csrr %0, 0xB96" : "=r"(mhpmcounterh[22]));
  //__asm__ volatile("csrr %0, 0xB97" : "=r"(mhpmcounterh[23]));
  //__asm__ volatile("csrr %0, 0xB98" : "=r"(mhpmcounterh[24]));
  //__asm__ volatile("csrr %0, 0xB99" : "=r"(mhpmcounterh[25]));
  //__asm__ volatile("csrr %0, 0xB9A" : "=r"(mhpmcounterh[26]));
  //__asm__ volatile("csrr %0, 0xB9B" : "=r"(mhpmcounterh[27]));
  //__asm__ volatile("csrr %0, 0xB9C" : "=r"(mhpmcounterh[28]));
  //__asm__ volatile("csrr %0, 0xB9D" : "=r"(mhpmcounterh[29]));
  //__asm__ volatile("csrr %0, 0xB9E" : "=r"(mhpmcounterh[30]));
  //__asm__ volatile("csrr %0, 0xB9F" : "=r"(mhpmcounterh[31]));

  sum = 0;
  //for (int i=3; i<32; i++) {
  for (int i=3; i<4; i++) {
    sum += mhpmcounterh[i];
  }
  if (sum) {
    //printf("ERROR: CSR MHPMCOUNTERH[3..31] not 0x0!\n\n");
    printf("ERROR: CSR MHPMCOUNTERH[3] not 0x0!\n\n");
    ++err_cnt;
  }

  __asm__ volatile("csrr %0, 0xF11" : "=r"(mvendorid_rval));
  __asm__ volatile("csrr %0, 0xF12" : "=r"(marchid_rval));
  __asm__ volatile("csrr %0, 0xF13" : "=r"(mimpid_rval));
  __asm__ volatile("csrr %0, 0xF14" : "=r"(mhartid_rval));

  if (mvendorid_rval != 0x0602) {
    printf("ERROR: CSR MVENDOR not 0x602!\n\n");
    ++err_cnt;
  }

  if (marchid_rval != 0x15) {
    printf("ERROR: CSR MARCHID not 0x15!\n\n");
    ++err_cnt;
  }

  if (mimpid_rval != 0x0) {
    printf("ERROR: CSR MIMPLID not zero!\n\n");
    ++err_cnt;
  }

  if (mhartid_rval != 0x0) {
    printf("ERROR: CSR MHARTID not equal to hart_id_i!\n\n");
    ++err_cnt;
  }

  __asm__ volatile("csrr %0, 0x320" : "=r"(mcountinhibit_rval));

  if (mcountinhibit_rval != 0xD) {
    printf("ERROR: CSR MCOUNTINHIBIT not 0xD!\n\n");
    ++err_cnt;
  }

  //__asm__ volatile("csrr %0, 0x306" : "=r"(mcounteren_rval));    // Not currently modeled

  //if (mcounteren_rval != 0x0) {
  //  printf("ERROR: CSR MCOUNTEREN not 0x0!\n\n");
  //  ++err_cnt;
  //}

  /////////////////////////////////////////////////////////////////////////////
  // These are read last because there should not have been any events which
  // caused these CSRs to be incremented up to this point.
  __asm__ volatile("csrr %0, 0x340" : "=r"(mscratch_rval));
  __asm__ volatile("csrr %0, 0x341" : "=r"(mepc_rval));
  __asm__ volatile("csrr %0, 0x342" : "=r"(mcause_rval));
  __asm__ volatile("csrr %0, 0x343" : "=r"(mtval_rval));  // UM says "writes are ignored, reads return 0x0"
                                                          // RM says "mtval: Unimplemented CSR (hardwired to zero)"
  __asm__ volatile("csrr %0, 0x344" : "=r"(mip_rval));

  if (mscratch_rval != 0x0) {
    printf("ERROR: CSR MSCRATCH not zero!\n\n");
    ++err_cnt;
  }

  if (mepc_rval != 0x0) {
    printf("ERROR: CSR MEPC not zero!\n\n");
    ++err_cnt;
  }

  if (mcause_rval != 0x0) {
    printf("ERROR: CSR MCAUSE not zero!\n\n");
    ++err_cnt;
  }

  if (mtval_rval != 0x0) {
    printf("ERROR: CSR MTVAL not zero!\n\n");
    ++err_cnt;
  }

  if (mip_rval != 0x0) {
    printf("ERROR: CSR MIP not zero!\n\n");
    ++err_cnt;
  }

  /////////////////////////////////////////////////////////////////////////////
  // Print a summary to stdout
  printf("\nCSR PoR Test\n");
  //printf("\tfflags        = 0x%0x\n", fflags_rval);
  //printf("\tfrm           = 0x%0x\n", frm_rval);
  //printf("\tfcsr          = 0x%0x\n", fcsr_rval);
  //printf("\tlpstart0      = 0x%0x\n", lpstart0_rval);
  //printf("\tlpend0        = 0x%0x\n", lpend0_rval);
  //printf("\tlpcount0      = 0x%0x\n", lpcount0_rval);
  //printf("\tlpstart1      = 0x%0x\n", lpstart1_rval);
  //printf("\tlpend1        = 0x%0x\n", lpend1_rval);
  //printf("\tlpcount1      = 0x%0x\n", lpcount1_rval);
  //printf("\tprivlv        = 0x%0x\n", privlv_rval);
  //printf("\tuhartid       = 0x%0x\n", uhartid_rval);
  printf("\tmstatus       = 0x%0x\n", mstatus_rval);
  printf("\tmisa          = 0x%0x\n", misa_rval);
  printf("\tmie           = 0x%0x\n", mie_rval);
  printf("\tmtvec         = 0x%0x\n", mtvec_rval);
  //printf("\tmcounteren    = 0x%0x\n", mcounteren_rval);
  printf("\tmcountinhibit = 0x%0x\n", mcountinhibit_rval);
  printf("\tmphmevent3    = 0x%0x\n", mphmevent_rval[3]);
  //printf("\tmphmevent31   = 0x%0x\n", mphmevent_rval[31]);
  printf("\tmscratch      = 0x%0x\n", mscratch_rval);
  printf("\tmepc          = 0x%0x\n", mepc_rval);
  printf("\tmcause        = 0x%0x\n", mcause_rval);
  printf("\tmtval         = 0x%0x\n", mtval_rval);
  printf("\tmip           = 0x%0x\n", mip_rval);
  printf("\ttselect       = 0x%0x\n", tselect_rval);
  printf("\ttdata1        = 0x%0x\n", tdata1_rval);
  printf("\ttdata2        = 0x%0x\n", tdata2_rval);
  printf("\ttdata3        = 0x%0x\n", tdata3_rval);
  printf("\ttinfo         = 0x%0x\n", tinfo_rval);
  printf("\tmcontext      = 0x%0x\n", mcontext_rval);
  printf("\tscontext      = 0x%0x\n", scontext_rval);
  //printf("\tdcsr          = 0x%0x\n", dcsr_rval);
  //printf("\tdpc           = 0x%0x\n", dpc_rval);
  //printf("\tdscratch0     = 0x%0x\n", dscratch0_rval);
  //printf("\tdscratch1     = 0x%0x\n", dscratch1_rval);
  printf("\tmcycle        = 0x%0x\n", mcycle_rval);
  printf("\tminstret      = 0x%0x\n", minstret_rval);
  printf("\tmhpmcounter3  = 0x%0x\n", mhpmcounter_rval[3]);
  //printf("\tmhpmcounter31 = 0x%0x\n", mhpmcounter_rval[31]);
  printf("\tmcycleh       = 0x%0x\n", mcycleh_rval);
  printf("\tminstreth     = 0x%0x\n", minstreth_rval);
  printf("\tmhpmcounterh3 = 0x%0x\n", mhpmcounterh[3]);
  //printf("\tmhpmcounterh31= 0x%0x\n", mhpmcounterh[31]);
  printf("\tmvendorid     = 0x%0x\n", mvendorid_rval);
  printf("\tmmarchid      = 0x%0x\n", marchid_rval);
  printf("\tmimpid        = 0x%0x\n", mimpid_rval);
  printf("\tmhartid       = 0x%0x\n", mhartid_rval);
	printf("\n\n");

	if (!err_cnt) {
    return EXIT_SUCCESS;
	} else {
    return EXIT_FAILURE;
	}

}

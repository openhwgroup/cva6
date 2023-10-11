# Module: CSR EMBEDDED ACCESS VERIFICATION

## Feature: CVA6 CSRs reset value

### Sub-feature: 000_Read register value after reset

#### Item: 000

* **Requirement location:** https://docs.openhwgroup.org/projects/cva6-user-manual/01_cva6_user/CV32A6_Control_Status_Registers.html
* **Feature Description**
  
  Upon reset, RISC-V CVA6 CSRs registers must initialize to their respective reset value.
* **Verification Goals**
  
  Verify that the CSRs reset value must match with the value specified in the RISC-V CVA6 user manual.
* **Pass/Fail Criteria:** Self-Check
* **Test Type:** Directed SelfChk
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6_v0.1.0, CV32A6-step2, CV64A6-step3
* **Unique verification tag:** VP_csr-embedded-access_F000_S000_I000
* **Link to Coverage:** 
* **Comments**
  
  Applicable to all CSR registers
## Feature: CVA6 CSRs read after write

### Sub-feature: 000_Read after write RW registers

#### Item: 000

* **Requirement location:** https://docs.openhwgroup.org/projects/cva6-user-manual/01_cva6_user/CV32A6_Control_Status_Registers.html
* **Feature Description**
  
  Check the correctness of RISCV CVA6 Read-Write CSRs by writing values: Inverted reset value, 0xaaaaaaaa, 0x555555, random value. Then read back the CSR.
* **Verification Goals**
  
  1.Verify that CSR can be written using the appropriate CSR write instructions.  
  2.Ensure correct read operations using CSR read instructions.  
   3.Ensure that read values of the CSR should be as per CVA6 user manual
* **Pass/Fail Criteria:** Self-Check
* **Test Type:** Directed SelfChk
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6_v0.1.0, CV32A6-step2, CV64A6-step3
* **Unique verification tag:** VP_csr-embedded-access_F001_S000_I000
* **Link to Coverage:** 
* **Comments**
  
  Related RW Registers: mstatus, misa, mie, mtvec, mstatush, mhpmevent[3-31], mscratch, mepc, mcause, mtval, mip, pmpcfg[0-15], icache, mcycle, minstret, mcycleh, minstreth, mhpmcounter[3..31], mhpmcounterh[3..31]
#### Item: 001

* **Requirement location:** https://docs.openhwgroup.org/projects/cva6-user-manual/01_cva6_user/CV32A6_Control_Status_Registers.html
* **Feature Description**
  
  Check the correctness of RISCV CVA6 Read-Write CSRs by writing illegal values then read back the CSR.
* **Verification Goals**
  
  1.Verify that CSR can be written with it illegal values.  
  2.Ensure correct read operations using CSR read instructions.  
  3.Ensure that read values of the CSR should be inchanged
* **Pass/Fail Criteria:** Self-Check
* **Test Type:** Directed SelfChk
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6_v0.1.0, CV32A6-step2, CV64A6-step3
* **Unique verification tag:** VP_csr-embedded-access_F001_S000_I001
* **Link to Coverage:** 
* **Comments**
  
  Related RW Registers with legal values:   
  mstatus.SD : 0  
  mstatus.XS : 0  
  mstatus.FS : 0  
  mstatus.VS : 0  
  mstatus.UBE : 0  
  misa[31:30] : 1  
   misa[25:0] : 0x141104  
  mie.UEIE : 0  
  mie.UTIE : 0  
  mie.USIE : 0  
  mtvec.MODE: 0, 1  
  mstatush.SBE: 0  
  mstatush.MBE: 0  
  mip.UEIP:0  
  mip.UTIP:0  
  mip.USIP:0
### Sub-feature: 001_Read after write RO registers

#### Item: 000

* **Requirement location:** https://docs.openhwgroup.org/projects/cva6-user-manual/01_cva6_user/CV32A6_Control_Status_Registers.html
* **Feature Description**
  
  Check the correctness of RISCV CVA6 Read-Only CSR by writing values: Inverted reset, 0xaaaaaaaa, 0x555555, random value. Then confirm that write into RO CSRs generates illegal exception. Finaly read back the CSR.
* **Verification Goals**
  
  1.Attempt to write a RO CSR.  
  2.Check to see that an illegal instruction exception occurred.  
  3.Immediately after returning from the exception handler, read CSR to check that it value has not changed.
* **Pass/Fail Criteria:** Self-Check
* **Test Type:** Directed SelfChk
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6_v0.1.0, CV32A6-step2, CV64A6-step3
* **Unique verification tag:** VP_csr-embedded-access_F001_S001_I000
* **Link to Coverage:** 
* **Comments**
  
  Related RO registers: cycle, instret, cycleh, instreth, mvendorid, marchid, mimpid, mhartid

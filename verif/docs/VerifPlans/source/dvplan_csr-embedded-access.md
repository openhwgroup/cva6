# Module: CSR EMBEDDED ACCESS VERIFICATION

## Feature: CVA6 CSRs reset value

### Sub-feature: 000_Read register value after reset

#### Item: 000

* **Requirement location:** https://docs.openhwgroup.org/projects/cva6-user-manual/01_cva6_user/CV32A6_Control_Status_Registers.html
* **Feature Description**
  
  Upon reset, RISC-V CVA6 CSRs registers must initialize to their respective reset value.
* **Verification Goals**
  
  Verify that the CSRs reset value must match with the value specified in the RISC-V CVA6 user manual.
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Directed Non-SelfChk
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
  
  Check the correctness of RISCV CVA6 Read-Write CSRs by writing values: Inverted reset value, 0xaaaaaaaa, 0x555555, random value. Then read back the CSR. All registres fields should be stimulated including the reserved bits.
* **Verification Goals**
  
  1.Verify that CSR can be written using the appropriate CSR write instructions.  
  2.Ensure correct read operations using CSR read instructions.  
  3.Ensure that read values of the CSR should be as per CVA6 user manual.
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Directed Non-SelfChk
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
  3.Ensure that read values of the CSR should be inchanged.
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Directed Non-SelfChk
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
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Directed Non-SelfChk
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6_v0.1.0, CV32A6-step2, CV64A6-step3
* **Unique verification tag:** VP_csr-embedded-access_F001_S001_I000
* **Link to Coverage:** 
* **Comments**
  
  Related RO registers: cycle, instret, cycleh, instreth, mvendorid, marchid, mimpid, mhartid
### Sub-feature: 002_Write and Read unmapped registers

#### Item: 000

* **Requirement location:** https://docs.openhwgroup.org/projects/cva6-user-manual/01_cva6_user/CV32A6_Control_Status_Registers.html
* **Feature Description**
  
  Check the correctness of RISCV CVA6 unmapped CSR register addresses by writing random value. Then confirm that write into unmapped CSRs addresses generates illegal exception. Finaly read back the CSR.
* **Verification Goals**
  
  1.Attempt to write a unoccupied CSR address.  
  2.Check to see that an illegal instruction exception occurred.  
  3.Immediately after returning from the exception handler, read address to check that it value is 0.
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Directed Non-SelfChk
* **Coverage Method:** Testcase
* **Applicable Cores:** CV32A6_v0.1.0, CV32A6-step2, CV64A6-step3
* **Unique verification tag:** VP_csr-embedded-access_F001_S002_I000
* **Link to Coverage:** 
* **Comments**
  
  Related register addresses: all unoccupied addresses from 0x0 to 0xFFF
## Feature: CVA6 CSRs counters functionality checking

### Sub-feature: 000_Counter value

#### Item: 000

* **Requirement location:** https://docs.openhwgroup.org/projects/cva6-user-manual/01_cva6_user/CV32A6_Control_Status_Registers.html
* **Feature Description**
  
  Check that counter registers cycle/mcycle and cycleh/mcycleh increment at each clock.
* **Verification Goals**
  
  Performing two continuous reads to the same register and ensure that the value of the second read from counter CSR is greater than the value of the initial read.
* **Pass/Fail Criteria:** Self-Check
* **Test Type:** Directed SelfChk
* **Coverage Method:** NDY (Not Defined Yet)
* **Applicable Cores:** CV32A6_v0.1.0, CV32A6-step2, CV64A6-step3
* **Unique verification tag:** VP_csr-embedded-access_F002_S000_I000
* **Link to Coverage:** 
* **Comments**
  
  In a RISC-V 32bits architecture cycle/mcycle and cycleh/mcycleh holds low 32 bits and high 32 bits respectively of the count of clock cycles executed by the processor.
#### Item: 001

* **Requirement location:** https://docs.openhwgroup.org/projects/cva6-user-manual/01_cva6_user/CV32A6_Control_Status_Registers.html
* **Feature Description**
  
  Check that counter registers instret/instreth and minstret/minstreth increment after each instruction.
* **Verification Goals**
  
  Performing two continuous reads to the same register and ensure that the value of the second read from counter CSR is greater than the value of the initial read.
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Directed SelfChk
* **Coverage Method:** Testcase
* **Applicable Cores:** CV32A6_v0.1.0, CV32A6-step2, CV64A6-step3
* **Unique verification tag:** VP_csr-embedded-access_F002_S000_I001
* **Link to Coverage:** 
* **Comments**
  
  In a RISC-V 32bits architecture instret/minstret and instreth/minstreth holds low 32 bits and high 32 bits respectively of the count of executed instructions by the processor.
### Sub-feature: 001_Counter overflow

#### Item: 000

* **Requirement location:** https://docs.openhwgroup.org/projects/cva6-user-manual/01_cva6_user/CV32A6_Control_Status_Registers.html
* **Feature Description**
  
  Check the behaviour of counter CSRs cycle, cycleh, mcycle, mcycleh when reaching maximum value.
* **Verification Goals**
  
  1- Write mcycle/mcycleh to higher or maximum 32bit value.  
  2- Perform some random read/write CSR registers.  
  3- Ensure that counters reset to 0.
* **Pass/Fail Criteria:** Self-Check
* **Test Type:** Directed SelfChk
* **Coverage Method:** Testcase
* **Applicable Cores:** CV32A6_v0.1.0, CV32A6-step2, CV64A6-step3
* **Unique verification tag:** VP_csr-embedded-access_F002_S001_I000
* **Link to Coverage:** 
* **Comments**
  
  Related counter registers: cycle, cycleh, mcycle, mcycleh.
#### Item: 001

* **Requirement location:** https://docs.openhwgroup.org/projects/cva6-user-manual/01_cva6_user/CV32A6_Control_Status_Registers.html
* **Feature Description**
  
  Check the behaviour of counter CSRs instre, instreh, minstre, minstreh when reaching maximum value.
* **Verification Goals**
  
  1- Write minstret/minstreth to higher or maximum 32bit value.  
  2- Perform some random read/write CSR registers.  
  3- Ensure that counters reset to 0.
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Directed SelfChk
* **Coverage Method:** Testcase
* **Applicable Cores:** CV32A6_v0.1.0, CV32A6-step2, CV64A6-step3
* **Unique verification tag:** VP_csr-embedded-access_F002_S001_I001
* **Link to Coverage:** 
* **Comments**
  
  Related counter registers: instret, instreth, minstret, minstreth.

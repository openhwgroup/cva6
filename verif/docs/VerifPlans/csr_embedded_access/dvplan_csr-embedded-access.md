  CORE-V CV32A6-embedded Design Verification Plan documentation     

[CORE-V CV32A6-embedded Design Verification Plan ![Logo](_static/openhw-landscape.svg)](#) 

Contents:

*   [Introduction](index.html#document-dvplan_intro)
*   [Module: CSR ACCESS VERIFICATION](index.html#document-dvplan_csr-access)

[CORE-V CV32A6-embedded Design Verification Plan](#)

*   [](#)
*   CORE-V CV32A6-embedded Design Verification Plan documentation

* * *

CV32A6-embedded Design Verification Plan[?](#cv32a6-embedded-design-verification-plan "Permalink to this headline")
=============================================================================================================

Introduction[?](#introduction "Permalink to this headline")
-----------------------------------------------------------

The objective of this document is to describe what must be covered to verify CVA6 RISC-V processor.

### License[?](#license "Permalink to this headline")

Copyright 2022 Thales

SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1

Licensed under the Solderpad Hardware License v 2.1 (the ?License?); you may not use this file except in compliance with the License, or, at your option, the Apache License version 2.0. You may obtain a copy of the License at [https://solderpad.org/licenses/SHL-2.1/](https://solderpad.org/licenses/SHL-2.1/).

Unless required by applicable law or agreed to in writing, any work distributed under the License is distributed on an ?AS IS? BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.

### Standards Compliance[?](#standards-compliance "Permalink to this headline")

To ease the reading, the reference to these specifications can be implicit in the requirements below. For the sake of precision, the requirements identify the versions of RISC-V extensions from these specifications.

*   **\[CVA6req\]** ?CVA6 requirement specification?, [https://github.com/openhwgroup/cva6/blob/master/docs/specifications/cva6\_requirement\_specification.rst](https://github.com/openhwgroup/cva6/blob/master/docs/specifications/cva6_requirement_specification.rst), HASH#767c465.
    
*   **\[CVA6design\]** ?CVA6 design document?, TO BE COMPLETED
    
*   **\[RVunpriv\]** ?The RISC-V Instruction Set Manual, Volume I: User-Level ISA, Document Version 20191213?, Editors Andrew Waterman and Krste Asanovi?, RISC-V Foundation, December 13, 2019.
    
*   **\[RVpriv\]** ?The RISC-V Instruction Set Manual, Volume II: Privileged Architecture, Document Version 20211203?, Editors Andrew Waterman, Krste Asanovi? and John Hauser, RISC-V Foundation, December 4, 2021.
    
*   **\[RVdbg\]** ?RISC-V External Debug Support, Document Version 0.13.2?, Editors Tim Newsome and Megan Wachs, RISC-V Foundation, March 22, 2019.
    
*   **\[RVcompat\]** ?RISC-V Architectural Compatibility Test Framework?, [https://github.com/riscv-non-isa/riscv-arch-test](https://github.com/riscv-non-isa/riscv-arch-test).
    
*   **\[AXI\]** AXI Specification, [https://developer.arm.com/documentation/ihi0022/hc](https://developer.arm.com/documentation/ihi0022/hc).
    
*   **\[CV-X-IF\]** Placeholder for the CV-X-IF coprocessor interface currently prepared at OpenHW Group; current version in [https://docs.openhwgroup.org/projects/openhw-group-core-v-xif/](https://docs.openhwgroup.org/projects/openhw-group-core-v-xif/).
    
*   **\[OpenPiton\]** ?OpenPiton Microarchitecture Specification?, Princeton University, [https://parallel.princeton.edu/openpiton/docs/micro\_arch.pdf](https://parallel.princeton.edu/openpiton/docs/micro_arch.pdf).
    

CV32A6 is a 32-bit processor fully compliant with RISC-V specifications: \[RVunpriv\], \[RVpriv\] and \[RVdbg\] and passes \[RVcompat\] compatibility tests, as requested by \[GEN-10\] in \[CVA6req\].

### Getting start verification[?](#getting-start-verification "Permalink to this headline")

\[TO BE COMPLETED\]

### Documentation framework[?](#documentation-framework "Permalink to this headline")

The framework of this document is aligned with the CVA6 design document \[CVA6design\].

Description of the framework:

*   Processor is a subsystem
    
*   Processor subsystems are split into several modules
    
*   Modules are verified separately
    

### Contributors[?](#contributors "Permalink to this headline")

Jean-Roch Coulon - Thales

\[TO BE COMPLETED\]

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
  3.Ensure that read values of the CSR should be as per CVA6 user manual
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
  3.Ensure that read values of the CSR should be inchanged
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
### Sub-feature: 002_Read after write unmapped registers

#### Item: 000

* **Requirement location:** https://docs.openhwgroup.org/projects/cva6-user-manual/01_cva6_user/CV32A6_Control_Status_Registers.html
* **Feature Description**
  
  Check the correctness of RISCV CVA6 unmapped CSR register addresses by writing random value. Then confirm that write into unmapped CSRs addresses generates illegal exception. Finaly read back the CSR.
* **Verification Goals**
  
  1.Attempt to write a unoccupied CSR address.  
  2.Check to see that an illegal instruction exception occurred.  
  3.Immediately after returning from the exception handler, read address to check that it value is 0.
* **Pass/Fail Criteria:** NDY (Not Defined Yet)
* **Test Type:** NDY (Not Defined Yet)
* **Coverage Method:** NDY (Not Defined Yet)
* **Applicable Cores:** CV32E40P, CV32E40S, CV32E40X, CV32A6_v0.1.0, CV32A6-step2, CV64A6-step3
* **Unique verification tag:** VP_csr-embedded-access_F001_S002_I000
* **Link to Coverage:** 
* **Comments**
  
  Related register addresses: all unoccupied addresses from 0x0 to 0xFFF
## Feature: CVA6 CSRs counters functionality checking

### Sub-feature: 000_Counter value

#### Item: 000

* **Requirement location:** https://docs.openhwgroup.org/projects/cva6-user-manual/01_cva6_user/CV32A6_Control_Status_Registers.html
* **Feature Description**
  
  Check correct behavior of counter registers:  
  - Increment cycle/mcycle and cycleh/mcycleh at each clock  
  - Increment instret/minstreh and instreth/minstreh after each instruction
* **Verification Goals**
  
  Performing two continuous reads to the same register and ensure that the value of the second read from counter CSR is greater than the value of the initial read.
* **Pass/Fail Criteria:** Self-Check
* **Test Type:** Directed SelfChk
* **Coverage Method:** NDY (Not Defined Yet)
* **Applicable Cores:** CV32E40P, CV32E40S, CV32E40X, CV32A6_v0.1.0, CV32A6-step2, CV64A6-step3
* **Unique verification tag:** VP_csr-embedded-access_F002_S000_I000
* **Link to Coverage:** 
* **Comments**
  
  In a RISC-V 32bits architecture instret/minstre and instreth/minstret holds low 32 bits and high 32 bits respectively of the count of executed instructions by the processor. Same for cycle/mcycle and cycleh/mcycleh holds low 32 bits and high 32 bits respectively of the count of clock cycles executed by the processor.
### Sub-feature: 001_Counter overflow

#### Item: 000

* **Requirement location:** https://docs.openhwgroup.org/projects/cva6-user-manual/01_cva6_user/CV32A6_Control_Status_Registers.html
* **Feature Description**
  
  Check the behaviour of counter CSRs when reaching maximum value.
* **Verification Goals**
  
  1- Write mcycle/mcycleh/minstre/minstreh to higher or maximum 32bit value.  
  2- Perform some random read/write CSR registers.  
  3- Ensure that counters reset to 0.
* **Pass/Fail Criteria:** Self-Check
* **Test Type:** Directed SelfChk
* **Coverage Method:** Testcase
* **Applicable Cores:** CV32E40P, CV32E40S, CV32E40X, CV32A6_v0.1.0, CV32A6-step2, CV64A6-step3
* **Unique verification tag:** VP_csr-embedded-access_F002_S001_I000
* **Link to Coverage:** 
* **Comments**
  
  Related counter registers: cycle, cycleh, mcycle, mcycleh, instret, instreth, minstre, minstreh

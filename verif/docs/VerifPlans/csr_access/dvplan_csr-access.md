  CORE-V CV32A6-step1 Design Verification Plan documentation     

[CORE-V CV32A6-step1 Design Verification Plan ![Logo](_static/openhw-landscape.svg)](#) 

Contents:

*   [Introduction](index.html#document-dvplan_intro)
*   [Module: CSR ACCESS VERIFICATION](index.html#document-dvplan_csr-access)

[CORE-V CV32A6-step1 Design Verification Plan](#)

*   [](#)
*   CORE-V CV32A6-step1 Design Verification Plan documentation

* * *

CV32A6-step1 Design Verification Plan[](#cv32a6-step1-design-verification-plan "Permalink to this headline")
=============================================================================================================

Introduction[](#introduction "Permalink to this headline")
-----------------------------------------------------------

The objective of this document is to describe what must be covered to verify CVA6 RISC-V processor.

### License[](#license "Permalink to this headline")

Copyright 2022 Thales

SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1

Licensed under the Solderpad Hardware License v 2.1 (the “License”); you may not use this file except in compliance with the License, or, at your option, the Apache License version 2.0. You may obtain a copy of the License at [https://solderpad.org/licenses/SHL-2.1/](https://solderpad.org/licenses/SHL-2.1/).

Unless required by applicable law or agreed to in writing, any work distributed under the License is distributed on an “AS IS” BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.

### Standards Compliance[](#standards-compliance "Permalink to this headline")

To ease the reading, the reference to these specifications can be implicit in the requirements below. For the sake of precision, the requirements identify the versions of RISC-V extensions from these specifications.

*   **\[CVA6req\]** “CVA6 requirement specification”, [https://github.com/openhwgroup/cva6/blob/master/docs/specifications/cva6\_requirement\_specification.rst](https://github.com/openhwgroup/cva6/blob/master/docs/specifications/cva6_requirement_specification.rst), HASH#767c465.
    
*   **\[CVA6design\]** “CVA6 design document”, TO BE COMPLETED
    
*   **\[RVunpriv\]** “The RISC-V Instruction Set Manual, Volume I: User-Level ISA, Document Version 20191213”, Editors Andrew Waterman and Krste Asanović, RISC-V Foundation, December 13, 2019.
    
*   **\[RVpriv\]** “The RISC-V Instruction Set Manual, Volume II: Privileged Architecture, Document Version 20211203”, Editors Andrew Waterman, Krste Asanović and John Hauser, RISC-V Foundation, December 4, 2021.
    
*   **\[RVdbg\]** “RISC-V External Debug Support, Document Version 0.13.2”, Editors Tim Newsome and Megan Wachs, RISC-V Foundation, March 22, 2019.
    
*   **\[RVcompat\]** “RISC-V Architectural Compatibility Test Framework”, [https://github.com/riscv-non-isa/riscv-arch-test](https://github.com/riscv-non-isa/riscv-arch-test).
    
*   **\[AXI\]** AXI Specification, [https://developer.arm.com/documentation/ihi0022/hc](https://developer.arm.com/documentation/ihi0022/hc).
    
*   **\[CV-X-IF\]** Placeholder for the CV-X-IF coprocessor interface currently prepared at OpenHW Group; current version in [https://docs.openhwgroup.org/projects/openhw-group-core-v-xif/](https://docs.openhwgroup.org/projects/openhw-group-core-v-xif/).
    
*   **\[OpenPiton\]** “OpenPiton Microarchitecture Specification”, Princeton University, [https://parallel.princeton.edu/openpiton/docs/micro\_arch.pdf](https://parallel.princeton.edu/openpiton/docs/micro_arch.pdf).
    

CV32A6 is a 32-bit processor fully compliant with RISC-V specifications: \[RVunpriv\], \[RVpriv\] and \[RVdbg\] and passes \[RVcompat\] compatibility tests, as requested by \[GEN-10\] in \[CVA6req\].

### Getting start verification[](#getting-start-verification "Permalink to this headline")

\[TO BE COMPLETED\]

### Documentation framework[](#documentation-framework "Permalink to this headline")

The framework of this document is aligned with the CVA6 design document \[CVA6design\].

Description of the framework:

*   Processor is a subsystem
    
*   Processor subsystems are split into several modules
    
*   Modules are verified separately
    

### Contributors[](#contributors "Permalink to this headline")

Jean-Roch Coulon - Thales

\[TO BE COMPLETED\]

Module: CSR ACCESS VERIFICATION[](#module-csr-access-verification "Permalink to this headline")
------------------------------------------------------------------------------------------------

### Feature: CVA6\_Machine\_mode\_RW\_CSRs(mstatus, misa, mideleg, medeleg, mie, mtvec, mcounteren, mepc, mcause, mtval, mip,pmpaddr\[0..7\], pmpcfg\[0..1\])[](#feature-cva6-machine-mode-rw-csrs-mstatus-misa-mideleg-medeleg-mie-mtvec-mcounteren-mepc-mcause-mtval-mip-pmpaddr-0-7-pmpcfg-0-1 "Permalink to this headline")

#### Sub-feature: 000\_Power-on-reset (POR) values of CSR[](#sub-feature-000-power-on-reset-por-values-of-csr "Permalink to this headline")

##### Item: 000[](#item-000 "Permalink to this headline")

*   **Requirement location:** https://docs.openhwgroup.org/projects/cva6-user-manual/01\_cva6\_user/CV32A6\_Control\_Status\_Registers.html
    
*   **Feature Description**
    
    Upon reset, RISC-V CVA6 Machine mode RW CSRs must initialize to their respective POR value.
    
*   **Verification Goals**
    
    Verify that the Machine Mode RW CSR POR value must match with the value specified in the RISC-V CVA6 user manual.
    
*   **Pass/Fail Criteria:** Self-Check
    
*   **Test Type:** Directed SelfChk
    
*   **Coverage Method:** Functional Coverage
    
*   **Applicable Cores:** CV32A6\_v0.1.0
    
*   **Unique verification tag:** VP\_CSR\_VERIFICATION\_F000\_S000\_I000
    
*   **Link to Coverage:**
    
*   **Comments**
    
    _(none)_
    

#### Sub-feature: 001\_Testing CSR with inverted reset value[](#sub-feature-001-testing-csr-with-inverted-reset-value "Permalink to this headline")

##### Item: 000[](#id1 "Permalink to this headline")

*   **Requirement location:**
    
*   **Feature Description**
    
    Check the behaviour of the RISC-V Machine mode CVA6 CSRs,when reset inverted values are written to respective CSRs.
    
*   **Verification Goals**
    
    1.  Verify CSR reading post write operation.
        
    2.  Verify if the core correctly handles inverted reset values or not.
        
*   **Pass/Fail Criteria:** Self-Check
    
*   **Test Type:** Directed SelfChk
    
*   **Coverage Method:** Functional Coverage
    
*   **Applicable Cores:** CV32A6\_v0.1.0
    
*   **Unique verification tag:** VP\_csr-access\_F000\_S003\_I000
    
*   **Link to Coverage:**
    
*   **Comments**
    
    _(none)_
    

#### Sub-feature: 002\_CSR write and read operations[](#sub-feature-002-csr-write-and-read-operations "Permalink to this headline")

##### Item: 000[](#id2 "Permalink to this headline")

*   **Requirement location:** https://docs.openhwgroup.org/projects/cva6-user-manual/01\_cva6\_user/CV32A6\_Control\_Status\_Registers.html
    
*   **Feature Description**
    
    check the correctness of RISCV CVA6 Machine Mode RW CSRs by writing random values like 0xa5a5a5a5, 0x5a5a5a5a, 0xffa1ae40.. and read using the CSR instructions defined in the instruction set architecture (ISA).
    
*   **Verification Goals**
    
    1.Verify that CSR can be written using the appropriate CSR write instructions.
    
    2.Ensure correct read operations using CSR read instructions.
    
    3.Ensure that read values of the CSR should be as per CVA6 user manual
    
*   **Pass/Fail Criteria:** Self-Check
    
*   **Test Type:** Directed SelfChk
    
*   **Coverage Method:** Functional Coverage
    
*   **Applicable Cores:** CV32A6\_v0.1.0
    
*   **Unique verification tag:** VP\_CSR\_VERIFICATION\_F000\_S001\_I000
    
*   **Link to Coverage:**
    
*   **Comments**
    
    _(none)_
    

#### Sub-feature: 003\_CSR access in different privilege modes[](#sub-feature-003-csr-access-in-different-privilege-modes "Permalink to this headline")

##### Item: 000[](#id3 "Permalink to this headline")

*   **Requirement location:** https://docs.openhwgroup.org/projects/cva6-user-manual/01\_cva6\_user/CV32A6\_Control\_Status\_Registers.html
    
*   **Feature Description**
    
    Accessing RISC-V CVA6 Machine Mode CSRs in different privilege modes (User, Supervisor and Machine modes).
    
*   **Verification Goals**
    
    1.Ensure that Machine mode CSRs can only be accessed in the Machine mode according to the RISCV specification.
    
    2.Verify that trying to access Machine Mode CSRs in lower privilege mode raises an illegal instruction exception.
    
*   **Pass/Fail Criteria:** Self-Check
    
*   **Test Type:** Directed SelfChk
    
*   **Coverage Method:** Functional Coverage
    
*   **Applicable Cores:** CV32A6\_v0.1.0
    
*   **Unique verification tag:** VP\_CSR\_VERIFICATION\_F000\_S002\_I000
    
*   **Link to Coverage:**
    
*   **Comments**
    
    _(none)_
    

### Feature: CVA6\_Machine\_mode\_RO\_CSRs(mvendorid, marchid, mimpid, mhartid)[](#feature-cva6-machine-mode-ro-csrs-mvendorid-marchid-mimpid-mhartid "Permalink to this headline")

#### Sub-feature: 000\_Power-on-reset (POR) values of CSR[](#id4 "Permalink to this headline")

##### Item: 000[](#id5 "Permalink to this headline")

*   **Requirement location:** https://docs.openhwgroup.org/projects/cva6-user-manual/01\_cva6\_user/CV32A6\_Control\_Status\_Registers.html
    
*   **Feature Description**
    
    Upon reset,RISC-V CVA6 Machine RO(read only) CSR must initialize to their respective POR value.
    
*   **Verification Goals**
    
    Verify that the Machine RO(Read only) CSR POR value must match with the value specified in the RISC-V CVA6 User Manual.
    
*   **Pass/Fail Criteria:** Self-Check
    
*   **Test Type:** Directed SelfChk
    
*   **Coverage Method:** Functional Coverage
    
*   **Applicable Cores:** CV32A6\_v0.1.0
    
*   **Unique verification tag:** VP\_CSR\_VERIFICATION\_F001\_S000\_I000
    
*   **Link to Coverage:**
    
*   **Comments**
    
    _(none)_
    

#### Sub-feature: 001\_CSR write and read operations[](#sub-feature-001-csr-write-and-read-operations "Permalink to this headline")

##### Item: 000[](#id6 "Permalink to this headline")

*   **Requirement location:** https://docs.openhwgroup.org/projects/cva6-user-manual/01\_cva6\_user/CV32A6\_Control\_Status\_Registers.html
    
*   **Feature Description**
    
    Check the correctness of RISCV CVA6 read only CSR by writing random values like 0xa5a5a5a5, 0x5a5a5a5a, 0xffa1ae40.. and confirm whether write into RO CSRs is possible or not.
    
*   **Verification Goals**
    
    1.Attempt to write a RO CSR.  
    2.Check to see that an illegal instruction exception occurred.  
    3.Immediately after returning from the exception handler, check to see that the CSR value is not changed.
    
*   **Pass/Fail Criteria:** Self-Check
    
*   **Test Type:** Directed SelfChk
    
*   **Coverage Method:** Functional Coverage
    
*   **Applicable Cores:** CV32A6\_v0.1.0
    
*   **Unique verification tag:** VP\_CSR\_VERIFICATION\_F001\_S001\_I000
    
*   **Link to Coverage:**
    
*   **Comments**
    
    _(none)_
    

#### Sub-feature: 002\_CSR access in different privilege modes[](#sub-feature-002-csr-access-in-different-privilege-modes "Permalink to this headline")

##### Item: 000[](#id7 "Permalink to this headline")

*   **Requirement location:** https://docs.openhwgroup.org/projects/cva6-user-manual/01\_cva6\_user/CV32A6\_Control\_Status\_Registers.html
    
*   **Feature Description**
    
    Accessing RISC-V Machine read only CSRs in different privilege modes (User, Supervisor and Machine modes).
    
*   **Verification Goals**
    
    1.Ensure that Machine mode read only CSRs can only be accessed in Machine mode according to the RISC-V specification and does not alter the value of the CSR.
    
    2.Verify that trying to access a Machine read only CSRs in an lower privilege mode raises an illegal instruction exception.
    
*   **Pass/Fail Criteria:** Self-Check
    
*   **Test Type:** Directed SelfChk
    
*   **Coverage Method:** Functional Coverage
    
*   **Applicable Cores:** CV32A6\_v0.1.0
    
*   **Unique verification tag:** VP\_CSR\_VERIFICATION\_F001\_S002\_I000
    
*   **Link to Coverage:**
    
*   **Comments**
    
    _(none)_
    

### Feature: CVA6\_Supervisor\_mode\_RW\_CSRs(sstatus,stvec, sip, sie, scounteren, sscratch, sepc, scause, stval, satp)[](#feature-cva6-supervisor-mode-rw-csrs-sstatus-stvec-sip-sie-scounteren-sscratch-sepc-scause-stval-satp "Permalink to this headline")

#### Sub-feature: 000\_Power-on-reset (POR) values of CSR[](#id8 "Permalink to this headline")

##### Item: 000[](#id9 "Permalink to this headline")

*   **Requirement location:** https://docs.openhwgroup.org/projects/cva6-user-manual/01\_cva6\_user/CV32A6\_Control\_Status\_Registers.html
    
*   **Feature Description**
    
    Upon reset, RISC-V CVA6 Supervisor mode RW CSRs must initialize to their respective POR value.
    
*   **Verification Goals**
    
    Verify that the Supervisor Mode RW CSRs POR value must match with the value specified in the RISC-V CVA6 user manual.
    
*   **Pass/Fail Criteria:** Self-Check
    
*   **Test Type:** Directed SelfChk
    
*   **Coverage Method:** Functional Coverage
    
*   **Applicable Cores:** CV32A6\_v0.1.0
    
*   **Unique verification tag:** VP\_CSR\_VERIFICATION\_F004\_S000\_I000
    
*   **Link to Coverage:**
    
*   **Comments**
    
    _(none)_
    

#### Sub-feature: 001\_Testing CSR with inverted reset value[](#id10 "Permalink to this headline")

##### Item: 000[](#id11 "Permalink to this headline")

*   **Requirement location:**
    
*   **Feature Description**
    
    Check the behaviour of the RISC-V Supervisor mode CVA6 CSRs,when reset inverted values are written to respective CSRs.
    
*   **Verification Goals**
    
    Ensure that the written value can be read back (that is, the R/W CSR actually stored the value of ~PoR).
    
*   **Pass/Fail Criteria:** Check RM
    
*   **Test Type:** Directed SelfChk
    
*   **Coverage Method:** Functional Coverage
    
*   **Applicable Cores:** CV32A6\_v0.1.0
    
*   **Unique verification tag:** Inverted PoR value
    
*   **Link to Coverage:**
    
*   **Comments**
    
    _(none)_
    

#### Sub-feature: 002\_CSR write and read operations[](#id12 "Permalink to this headline")

##### Item: 000[](#id13 "Permalink to this headline")

*   **Requirement location:** https://docs.openhwgroup.org/projects/cva6-user-manual/01\_cva6\_user/CV32A6\_Control\_Status\_Registers.html
    
*   **Feature Description**
    
    Check the correctness of RISCV CVA6 Supervisor Mode RW CSR by writing random values like 0xa5a5a5a5, 0x5a5a5a5a, 0xffa1ae40.. and read using the CSR instructions defined in the instruction set architecture (ISA).
    
*   **Verification Goals**
    
    1.Verify that CSR can be written using the appropriate CSR write instructions.  
    2.Ensure correct read operations using CSR read instructions.  
    3.Ensure that read values of the CSR should be as per CVA6 user manual.
    
*   **Pass/Fail Criteria:** Self-Check
    
*   **Test Type:** Directed SelfChk
    
*   **Coverage Method:** Functional Coverage
    
*   **Applicable Cores:** CV32A6\_v0.1.0
    
*   **Unique verification tag:** VP\_CSR\_VERIFICATION\_F004\_S001\_I000
    
*   **Link to Coverage:**
    
*   **Comments**
    
    _(none)_
    

#### Sub-feature: 003\_CSR access in different privilege modes[](#id14 "Permalink to this headline")

##### Item: 000[](#id15 "Permalink to this headline")

*   **Requirement location:** https://docs.openhwgroup.org/projects/cva6-user-manual/01\_cva6\_user/CV32A6\_Control\_Status\_Registers.html
    
*   **Feature Description**
    
    Accessing RISC-V CVA6 Supervisor Mode CSRs in different privilege modes (User,Supervisor and Machine modes).
    
*   **Verification Goals**
    
    1.Ensure that Supervisor Mode CSRs can only be accessed in supervisor mode and in higher privilege mode according to the RISCV specification.  
    2.Verify that trying to access a Supervisor Mode CSR in an lower privilege mode raises an illegal instruction exception.
    
*   **Pass/Fail Criteria:** Self-Check
    
*   **Test Type:** Directed SelfChk
    
*   **Coverage Method:** Functional Coverage
    
*   **Applicable Cores:** CV32A6\_v0.1.0
    
*   **Unique verification tag:** VP\_CSR\_VERIFICATION\_F004\_S002\_I000
    
*   **Link to Coverage:**
    
*   **Comments**
    
    _(none)_
    

### Feature: CVA6\_User\_Mode\_Counter\_CSRs(cycle, instret, cycleh, instreth)[](#feature-cva6-user-mode-counter-csrs-cycle-instret-cycleh-instreth "Permalink to this headline")

#### Sub-feature: 000\_Power-on-reset (POR) values of CSR[](#id16 "Permalink to this headline")

##### Item: 000[](#id17 "Permalink to this headline")

*   **Requirement location:** https://docs.openhwgroup.org/projects/cva6-user-manual/01\_cva6\_user/CV32A6\_Control\_Status\_Registers.html
    
*   **Feature Description**
    
    Upon reset, RISC-V CVA6 User mode counter CSRs must initialize to their respective POR value.
    
*   **Verification Goals**
    
    Verify that the User Mode counter CSR POR value must match with the value specified in the RISC-V CVA6 user manual.  
    As cycle will increment on the posedge of each clock and instret will increment after every instruction is retired. For these CSRs, the best technique to check reset value is by “visual inspection”
    
*   **Pass/Fail Criteria:** Self-Check
    
*   **Test Type:** Directed SelfChk
    
*   **Coverage Method:** NDY (Not Defined Yet)
    
*   **Applicable Cores:** CV32A6\_v0.1.0
    
*   **Unique verification tag:** VP\_CSR\_VERIFICATION\_F003\_S000\_I000
    
*   **Link to Coverage:**
    
*   **Comments**
    
    _(none)_
    

#### Sub-feature: 001\_Counter \_CSRs\_functionality\_checking[](#sub-feature-001-counter-csrs-functionality-checking "Permalink to this headline")

##### Item: 000[](#id18 "Permalink to this headline")

*   **Requirement location:** https://docs.openhwgroup.org/projects/cva6-user-manual/01\_cva6\_user/CV32A6\_Control\_Status\_Registers.html
    
*   **Feature Description**
    
    This feature pertains to the verification of functionality of RISC-V cycle, cycleh, instret and instreth Control Status Register (CSR). In a RISC-V architecture
    
    1.’cycle’ and ‘cycleh’ are user-level CSR that hold low 32 bits and high 32 bits respectively of the count of clock cycles executed by the processor.  
    2.’instret’ and ‘instreth’ are also user-level CSR that count the total number of instructions executed by the processor.
    
    The functionality of user mode counter CSR is being tested by performing two continuous reads and checking whether the value in the second read is greater than the value in the first read.
    
*   **Verification Goals**
    
    1.Verify that these CSR are properly initialized.  
    2.Initiate a second read from the counter CSR immediately after the first read.  
    3.Ensure that the value of the second read from counter CSR is greater than the value of the initial read.  
    4.Confirm that user mode counter CSRs are incrementing.
    
    Note: This algorithm is only an “approximate test” of the functionality of these CSRs.
    
*   **Pass/Fail Criteria:** Self-Check
    
*   **Test Type:** Directed SelfChk
    
*   **Coverage Method:** NDY (Not Defined Yet)
    
*   **Applicable Cores:** CV32A6\_v0.1.0
    
*   **Unique verification tag:** VP\_CSR\_VERIFICATION\_F003\_S001\_I000
    
*   **Link to Coverage:**
    
*   **Comments**
    
    _(none)_
    

#### Sub-feature: 002\_CSR access in different privilege modes[](#id19 "Permalink to this headline")

##### Item: 000[](#id20 "Permalink to this headline")

*   **Requirement location:** https://docs.openhwgroup.org/projects/cva6-user-manual/01\_cva6\_user/CV32A6\_Control\_Status\_Registers.html
    
*   **Feature Description**
    
    Accessing RISC-V CVA6 user Mode counter CSR in different privilege modes (User, Supervisor and Machine modes).
    
*   **Verification Goals**
    
    Ensure that User mode counter CSRs can be accessed in user and Supervisor modes by configuring MCOUNTEREN CSR.
    
*   **Pass/Fail Criteria:** Self-Check
    
*   **Test Type:** Directed SelfChk
    
*   **Coverage Method:** Functional Coverage
    
*   **Applicable Cores:** CV32A6\_v0.1.0
    
*   **Unique verification tag:** VP\_CSR\_VERIFICATION\_F003\_S002\_I000
    
*   **Link to Coverage:**
    
*   **Comments**
    
    _(none)_
    

#### Sub-feature: 003\_Verify the user mode counter CSRs behaviour after reaching maximum values[](#sub-feature-003-verify-the-user-mode-counter-csrs-behaviour-after-reaching-maximum-values "Permalink to this headline")

##### Item: 000[](#id21 "Permalink to this headline")

*   **Requirement location:**
    
*   **Feature Description**
    
    check the behaviour of the RISC-V User mode counter CSRs when it reaches to maximum value.
    
*   **Verification Goals**
    
    Ensure that user mode counter CSRs is updated to reset value as mentioned in CVA6 user manual after reaching to maximum value.
    
*   **Pass/Fail Criteria:** Self-Check
    
*   **Test Type:** Directed SelfChk
    
*   **Coverage Method:** Functional Coverage
    
*   **Applicable Cores:** CV32A6\_v0.1.0
    
*   **Unique verification tag:** VP\_csr-access\_F003\_S003\_I000
    
*   **Link to Coverage:**
    
*   **Comments**
    
    _(none)_
    

### Feature: CVA6\_Machine\_mode\_counter\_csr(mcycle,mcycleh,minstret,minstreth)[](#feature-cva6-machine-mode-counter-csr-mcycle-mcycleh-minstret-minstreth "Permalink to this headline")

#### Sub-feature: 000\_Power-on-reset (POR) values of CSR[](#id22 "Permalink to this headline")

##### Item: 000[](#id23 "Permalink to this headline")

*   **Requirement location:** https://docs.openhwgroup.org/projects/cva6-user-manual/01\_cva6\_user/CV32A6\_Control\_Status\_Registers.html
    
*   **Feature Description**
    
    Upon reset, RISC-V CVA6 Machine mode counter CSRs must initialize to their respective POR value.
    
*   **Verification Goals**
    
    Verify that the Machine Mode counter CSR POR value must match with the value specified in the RISC-V CVA6 user manual.  
    As mcycle will increment on the posedge of each clock and minstret will increment after every instruction is retired. For these CSRs, the best technique to check reset value is by “visual inspection”
    
*   **Pass/Fail Criteria:** Self-Check
    
*   **Test Type:** Directed SelfChk
    
*   **Coverage Method:** Functional Coverage
    
*   **Applicable Cores:** CV32A6\_v0.1.0
    
*   **Unique verification tag:** VP\_csr-access\_F002\_S000\_I000
    
*   **Link to Coverage:**
    
*   **Comments**
    
    _(none)_
    

#### Sub-feature: 001\_Counter \_CSRs\_functionality\_checking[](#id24 "Permalink to this headline")

##### Item: 000[](#id25 "Permalink to this headline")

*   **Requirement location:** https://docs.openhwgroup.org/projects/cva6-user-manual/01\_cva6\_user/CV32A6\_Control\_Status\_Registers.html
    
*   **Feature Description**
    
    This feature pertains to the verification of functionality of RISC-V mcycle, mcycleh, minstret and minstreth Control Status Register (CSR). In a RISC-V architecture
    
    1.’mcycle’ and ‘mcycleh’ are machine-level CSRs that hold low 32 bits and high 32 bits respectively of the count of clock cycles executed by the processor.
    
    2.’minstret’ and ‘minstreth’ are also machine-level CSR that count the total number of instructions executed by the processor.
    
    The functionality of machine mode counter CSR is being tested by performing two continuous reads and checking whether the value in the second read is greater than the value in the first read.
    
*   **Verification Goals**
    
    1.Verify that these CSR are properly initialized.  
    2.Initiate a second read from the counter CSR immediately after the first read.  
    3.Ensure that the value of the second read from counter CSR is greater than the value of the initial read.  
    4.Confirm that Machine Mode counter CSRs are incrementing.
    
    Note: This algorithm is only an “approximate test” of the functionality of these CSRs.
    
*   **Pass/Fail Criteria:** Self-Check
    
*   **Test Type:** Directed SelfChk
    
*   **Coverage Method:** Functional Coverage
    
*   **Applicable Cores:** CV32A6\_v0.1.0
    
*   **Unique verification tag:** VP\_csr-access\_F002\_S001\_I000
    
*   **Link to Coverage:**
    
*   **Comments**
    
    _(none)_
    

#### Sub-feature: 002\_CSR access in different privilege modes[](#id26 "Permalink to this headline")

##### Item: 000[](#id27 "Permalink to this headline")

*   **Requirement location:** https://docs.openhwgroup.org/projects/cva6-user-manual/01\_cva6\_user/CV32A6\_Control\_Status\_Registers.html
    
*   **Feature Description**
    
    Accessing RISC-V CVA6 user Machine mode counter CSRs in different privilege modes (User, Supervisor and Machine modes).
    
*   **Verification Goals**
    
    1.Ensure that Machine mode CSRs can only be accessed in the Machine mode according to the RISC-V specification.  
    2.Verify that trying to access Machine Mode CSRs in lower privilege mode raises an illegal instruction exception.
    
*   **Pass/Fail Criteria:** Self-Check
    
*   **Test Type:** Directed SelfChk
    
*   **Coverage Method:** Functional Coverage
    
*   **Applicable Cores:** CV32A6\_v0.1.0
    
*   **Unique verification tag:** VP\_csr-access\_F002\_S002\_I000
    
*   **Link to Coverage:**
    
*   **Comments**
    
    _(none)_
    

#### Sub-feature: 003\_Verify the Machine mode counter CSRs behaviour after reaching maximum value[](#sub-feature-003-verify-the-machine-mode-counter-csrs-behaviour-after-reaching-maximum-value "Permalink to this headline")

##### Item: 000[](#id28 "Permalink to this headline")

*   **Requirement location:**
    
*   **Feature Description**
    
    check the behaviour of the RISC-V Machine mode counter CSRs when it reaches to maximum value.
    
*   **Verification Goals**
    
    Ensure that Machine mode counter CSRs is updated to reset value as mentioned in CVA6 user manual after reaching it to maximum value.
    
*   **Pass/Fail Criteria:** Self-Check
    
*   **Test Type:** Directed SelfChk
    
*   **Coverage Method:** Functional Coverage
    
*   **Applicable Cores:** CV32A6\_v0.1.0
    
*   **Unique verification tag:** VP\_csr-access\_F002\_S003\_I000
    
*   **Link to Coverage:**
    
*   **Comments**
    
    _(none)_
    

* * *

© Copyright 2022, Thales Group.

Built with [Sphinx](https://www.sphinx-doc.org/) using a [theme](https://github.com/readthedocs/sphinx_rtd_theme) provided by [Read the Docs](https://readthedocs.org).

jQuery(function () { SphinxRtdTheme.Navigation.enable(true); });
# Module: Traps

## Feature: Illegal Instruction

### Sub-feature: 000_illegal_instr

#### Item: 000

* **Requirement location:** Unprivileged ISA Version 20191213, Chapter 2.2
* **Feature Description**
  
  The behavior upon decoding a reserved instruction is unspecified. Opcodes that do not decode to a valid, supported instruction for the CVA6 core configuration shall raise an illegal instruction exception.
* **Verification Goals**
  
  Check that when executing any illegal instruction, an exception is raised with `mcause` set to 0x2.
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Code Coverage
* **Applicable Cores:** CV32A6_v0.1.0, CV32A6-step2, CV64A6-step3
* **Unique verification tag:** VP_traps_F000_S000_I000
* **Link to Coverage:** 
* **Comments**
  
  Covered by ISACOV tests, not yet in ISACOV DV plan
### Sub-feature: 001_mtval

#### Item: 000

* **Requirement location:** Privileged Architecture Version 20211203, Chapter 3.1.16
* **Feature Description**
  
  When an illegal instruction exception is raised, the corresponding instruction is stored into `mtval` CSR.
* **Verification Goals**
  
  Check that when any illegal instruction exception is raised, `mtval` CSR contains the faulting instruction.
* **Pass/Fail Criteria:** NDY (Not Defined Yet)
* **Test Type:** NDY (Not Defined Yet)
* **Coverage Method:** NDY (Not Defined Yet)
* **Applicable Cores:** CV32A6_v0.1.0, CV32A6-step2, CV64A6-step3
* **Unique verification tag:** VP_traps_F000_S001_I000
* **Link to Coverage:** 
* **Comments**
  
  ZERO_TVAL parameter value?
## Feature: CSR Access

### Sub-feature: 000_CSR_access

#### Item: 000

* **Requirement location:** Privileged Architecture Version 20211203, Chapter 2.1
* **Feature Description**
  
  Attempted access to non-existent CSRs will generate an illegal instruction exception.
* **Verification Goals**
  
  Check that when accessing any non-existent CSR, an exception is raised with `mcause` set to 0x2.
* **Pass/Fail Criteria:** NDY (Not Defined Yet)
* **Test Type:** NDY (Not Defined Yet)
* **Coverage Method:** NDY (Not Defined Yet)
* **Applicable Cores:** CV32A6_v0.1.0, CV32A6-step2, CV64A6-step3
* **Unique verification tag:** VP_traps_F002_S000_I000
* **Link to Coverage:** 
* **Comments**
  
  Covered by CSR DV plan.  
  VP_csr-embedded-access_F001_S002_I000  
   Verify if `mcause` value check is covered by CSR tests.
#### Item: 001

* **Requirement location:** Privileged Architecture Version 20211203, Chapter 2.1
* **Feature Description**
  
  Attempted store to read-only CSRs will generate an illegal instruction exception.
* **Verification Goals**
  
  Check that when storing to any read-only CSR, an exception is raised with `mcause` set to 0x2.
* **Pass/Fail Criteria:** NDY (Not Defined Yet)
* **Test Type:** NDY (Not Defined Yet)
* **Coverage Method:** NDY (Not Defined Yet)
* **Applicable Cores:** CV32A6_v0.1.0, CV32A6-step2, CV64A6-step3
* **Unique verification tag:** VP_traps_F002_S000_I001
* **Link to Coverage:** 
* **Comments**
  
  Covered by CSR DV plan.  
  VP_csr-embedded-access_F001_S001_I000  
   Verify if `mcause` value check is covered by CSR tests.
## Feature: Machine Trap Vector

### Sub-feature: 000_mtvec

#### Item: 000

* **Requirement location:** Privileged Architecture Version 20211203, Chapter 3.1.7
* **Feature Description**
  
  `mtvec` provides the starting value of the Interrupt Vector Table as well as the mode (Direct or Vectored) number at the time. Mode number is not relevant to exceptions as it only affects the value jumped to by interrupts.
* **Verification Goals**
  
  Check that exceptions jump to the base value defined in `mtvec` CSR.
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6_v0.1.0, CV32A6-step2, CV64A6-step3
* **Unique verification tag:** VP_traps_F003_S000_I000
* **Link to Coverage:** 
* **Comments**
  
  *(none)*  
  
## Feature: Machine Exception Program Counter

### Sub-feature: 000_mepc

#### Item: 000

* **Requirement location:** Privileged Architecture Version 20211203, Chapter 3.1.15
* **Feature Description**
  
  `mepc` is set to the `pc` value of the instruction that generates an exception.
* **Verification Goals**
  
  Check that when an exception is raised, `mepc` CSR contains the correct `pc`.
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6_v0.1.0, CV32A6-step2, CV64A6-step3
* **Unique verification tag:** VP_traps_F005_S000_I000
* **Link to Coverage:** 
* **Comments**
  
  *(none)*  
  
## Feature: Machine Trap Value

### Sub-feature: 000_mtval_illegal

#### Item: 000

* **Requirement location:** Privileged Architecture Version 20211203, Chapter 3.1.16
* **Feature Description**
  
  When an illegal instruction exception is raised, the corresponding instruction is stored into `mtval` CSR.
* **Verification Goals**
  
  Check that when any illegal instruction exception is raised, `mtval` CSR contains the faulting instruction.
* **Pass/Fail Criteria:** NDY (Not Defined Yet)
* **Test Type:** NDY (Not Defined Yet)
* **Coverage Method:** NDY (Not Defined Yet)
* **Applicable Cores:** CV32A6_v0.1.0, CV32A6-step2, CV64A6-step3
* **Unique verification tag:** VP_traps_F006_S000_I000
* **Link to Coverage:** 
* **Comments**
  
  ZERO_TVAL parameter value?
### Sub-feature: 001_mtval_misaligned

#### Item: 000

* **Requirement location:** Privileged Architecture Version 20211203, Chapter 3.1.16
* **Feature Description**
  
  When an address misaligned exception is raised, the corresponding address is stored into `mtval` CSR.
* **Verification Goals**
  
  Check that when any address misaligned exception is raised, `mtval` CSR contains the address of the portion of the access causing the fault.
* **Pass/Fail Criteria:** NDY (Not Defined Yet)
* **Test Type:** NDY (Not Defined Yet)
* **Coverage Method:** NDY (Not Defined Yet)
* **Applicable Cores:** CV32A6_v0.1.0, CV32A6-step2, CV64A6-step3
* **Unique verification tag:** VP_traps_F006_S001_I000
* **Link to Coverage:** 
* **Comments**
  
  ZERO_TVAL parameter value?
### Sub-feature: 002_mtval_access

#### Item: 000

* **Requirement location:** Privileged Architecture Version 20211203, Chapter 3.1.16
* **Feature Description**
  
  When an access fault exception is raised, the corresponding address is stored into `mtval` CSR.
* **Verification Goals**
  
  Check that when any access fault exception is raised, `mtval` CSR contains the address of the portion of the access causing the fault.
* **Pass/Fail Criteria:** NDY (Not Defined Yet)
* **Test Type:** NDY (Not Defined Yet)
* **Coverage Method:** NDY (Not Defined Yet)
* **Applicable Cores:** CV32A6_v0.1.0, CV32A6-step2, CV64A6-step3
* **Unique verification tag:** VP_traps_F006_S002_I000
* **Link to Coverage:** 
* **Comments**
  
  ZERO_TVAL parameter value?
### Sub-feature: 003_mtval_page

#### Item: 000

* **Requirement location:** Privileged Architecture Version 20211203, Chapter 3.1.16
* **Feature Description**
  
  When an page fault exception is raised, the corresponding address is stored into `mtval` CSR.
* **Verification Goals**
  
  Check that when any page fault exception is raised, `mtval` CSR contains the address of the portion of the access causing the fault.
* **Pass/Fail Criteria:** NDY (Not Defined Yet)
* **Test Type:** NDY (Not Defined Yet)
* **Coverage Method:** NDY (Not Defined Yet)
* **Applicable Cores:** CV32A6_v0.1.0, CV32A6-step2, CV64A6-step3
* **Unique verification tag:** VP_traps_F006_S003_I000
* **Link to Coverage:** 
* **Comments**
  
  ZERO_TVAL parameter value? Only with MMU support
## Feature: Exception Priority

### Sub-feature: 000_exception priority

#### Item: 000

* **Requirement location:** Privileged Architecture Version 20211203, Chapter 3.1.15
* **Feature Description**
  
  Exceptions are of lower priority than all interrupts.  
  Exception priority (high to low)  
  - code=0x3: Instruction address breakpoint  
  - code=0xC, 0x1: Instruction page fault, instruction access fault  
  - code=0x2: Illegal instruction  
  - code=0x8, 0x9, 0xB: Environment call from U-mode, from S-mode, from M-mode  
  - code=0x3: Environment break  
  - code=0x3: Load/store/AMO address breakpoint  
  - code=0xD, 0xF, 0x5, 0x7: Load page fault, store/AMO page fault, load access fault, store/AMO access fault  
  - code=0x4, 0x6: Load address misaligned, store/AMO address misaligned
* **Verification Goals**
  
  Check that when raising an exception together with a lower priority one the cause of the higher priority exception is written in `mcause` register.
* **Pass/Fail Criteria:** NDY (Not Defined Yet)
* **Test Type:** Directed Non-SelfChk
* **Coverage Method:** Testcase
* **Applicable Cores:** CV32A6_v0.1.0, CV64A6-step3
* **Unique verification tag:** VP_traps_F007_S000_I000
* **Link to Coverage:** 
* **Comments**
  
  *(none)*  
  
### Sub-feature: 001_exception priority embedded

## Feature: Address Misaligned

### Sub-feature: 000_instr_misaligned

#### Item: 000

* **Requirement location:** Privileged Architecture Version 20211203, Chapter 3.1.15
* **Feature Description**
  
  If not aligned address is computed by control-flow instruction, a instruction address misaligned exception is taken.
* **Verification Goals**
  
  Exception is entered with `mcause` set to 0x0.
* **Pass/Fail Criteria:** NDY (Not Defined Yet)
* **Test Type:** NDY (Not Defined Yet)
* **Coverage Method:** NDY (Not Defined Yet)
* **Applicable Cores:** CV32A6_v0.1.0, CV32A6-step2, CV64A6-step3
* **Unique verification tag:** VP_traps_F008_S000_I000
* **Link to Coverage:** 
* **Comments**
  
  Need to check if such exception is possible with instruction set
### Sub-feature: 001_load_misaligned

#### Item: 000

* **Requirement location:** Privileged Architecture Version 20211203, Chapter 3.6.3.3
* **Feature Description**
  
  If not aligned load is attempted, a load address misaligned exception is taken.
* **Verification Goals**
  
  Exception is entered with `mcause` set to 0x4.
* **Pass/Fail Criteria:** NDY (Not Defined Yet)
* **Test Type:** NDY (Not Defined Yet)
* **Coverage Method:** NDY (Not Defined Yet)
* **Applicable Cores:** CV32A6_v0.1.0, CV32A6-step2, CV64A6-step3
* **Unique verification tag:** VP_traps_F008_S001_I000
* **Link to Coverage:** 
* **Comments**
  
  *(none)*  
  
#### Item: 001

* **Requirement location:** Privileged Architecture Version 20211203, Chapter 3.6.3.3
* **Feature Description**
  
  If not aligned load-reserved is attempted, a load address misaligned exception is taken.
* **Verification Goals**
  
  Exception is entered with `mcause` set to 0x4.
* **Pass/Fail Criteria:** NDY (Not Defined Yet)
* **Test Type:** NDY (Not Defined Yet)
* **Coverage Method:** NDY (Not Defined Yet)
* **Applicable Cores:** CV32A6_v0.1.0, CV64A6-step3
* **Unique verification tag:** VP_traps_F008_S001_I001
* **Link to Coverage:** 
* **Comments**
  
  *(none)*  
  
### Sub-feature: 002_store_misaligned

#### Item: 000

* **Requirement location:** Privileged Architecture Version 20211203, Chapter 3.6.3.3
* **Feature Description**
  
  If not aligned store is attempted, a store/AMO access misaligned exception is taken.
* **Verification Goals**
  
  Exception is entered with `mcause` set to 0x6.
* **Pass/Fail Criteria:** NDY (Not Defined Yet)
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6_v0.1.0, CV32A6-step2, CV64A6-step3
* **Unique verification tag:** VP_traps_F008_S002_I000
* **Link to Coverage:** 
* **Comments**
  
  *(none)*  
  
#### Item: 001

* **Requirement location:** Privileged Architecture Version 20211203, Chapter 3.6.3.3
* **Feature Description**
  
  If not aligned store-conditional is attempted , a store/AMO access misaligned exception is taken.
* **Verification Goals**
  
  Exception is entered with `mcause` set to 0x6.
* **Pass/Fail Criteria:** NDY (Not Defined Yet)
* **Test Type:** NDY (Not Defined Yet)
* **Coverage Method:** NDY (Not Defined Yet)
* **Applicable Cores:** CV32A6_v0.1.0, CV64A6-step3
* **Unique verification tag:** VP_traps_F008_S002_I001
* **Link to Coverage:** 
* **Comments**
  
  *(none)*  
  
#### Item: 002

* **Requirement location:** Privileged Architecture Version 20211203, Chapter 3.6.3.3
* **Feature Description**
  
  If not aligned AMO is attempted, a store/AMO access misaligned exception is taken.
* **Verification Goals**
  
  Exception is entered with `mcause` set to 0x6.
* **Pass/Fail Criteria:** NDY (Not Defined Yet)
* **Test Type:** NDY (Not Defined Yet)
* **Coverage Method:** NDY (Not Defined Yet)
* **Applicable Cores:** CV32A6_v0.1.0, CV64A6-step3
* **Unique verification tag:** VP_traps_F008_S002_I002
* **Link to Coverage:** 
* **Comments**
  
  *(none)*  
  
### Sub-feature: 003_mtval

#### Item: 000

* **Requirement location:** Privileged Architecture Version 20211203, Chapter 3.1.16
* **Feature Description**
  
  When an address misaligned exception is raised, the corresponding address is stored into `mtval` CSR.
* **Verification Goals**
  
  Check that when any address misaligned exception is raised, `mtval` CSR contains the address of the portion of the access causing the fault.
* **Pass/Fail Criteria:** NDY (Not Defined Yet)
* **Test Type:** NDY (Not Defined Yet)
* **Coverage Method:** NDY (Not Defined Yet)
* **Applicable Cores:** CV32A6_v0.1.0, CV32A6-step2, CV64A6-step3
* **Unique verification tag:** VP_traps_F008_S003_I000
* **Link to Coverage:** 
* **Comments**
  
  ZERO_TVAL parameter value?
## Feature: Access Fault

### Sub-feature: 000_instr_access

#### Item: 000

* **Requirement location:** Privileged Architecture Version 20211203, Chapter 3.7.1
* **Feature Description**
  
  If execution is attempted in a PMP region without execute permission, an instruction access fault exception is taken.
* **Verification Goals**
  
  Exception is entered with `mcause` set to 0x1.
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6_v0.1.0, CV32A6-step2, CV64A6-step3
* **Unique verification tag:** VP_traps_F009_S000_I000
* **Link to Coverage:** 
* **Comments**
  
  *(none)*  
  
#### Item: 001

* **Requirement location:** Privileged Architecture Version 20211203, Chapter 3.6
* **Feature Description**
  
  If execution is attempted in a PMA region set to I/O, an instruction access fault exception is taken.
* **Verification Goals**
  
  Exception is entered with `mcause` set to 0x1.
* **Pass/Fail Criteria:** NDY (Not Defined Yet)
* **Test Type:** NDY (Not Defined Yet)
* **Coverage Method:** NDY (Not Defined Yet)
* **Applicable Cores:** CV32A6_v0.1.0, CV32A6-step2, CV64A6-step3
* **Unique verification tag:** VP_traps_F009_S000_I001
* **Link to Coverage:** 
* **Comments**
  
  CHECK IF RELEVANT ON CVA6
### Sub-feature: 001_load_access

#### Item: 000

* **Requirement location:** Privileged Architecture Version 20211203, Chapter 3.7.1
* **Feature Description**
  
  If aligned or not aligned load is attempted in a PMP region without write permission, a load access fault exception is taken.
* **Verification Goals**
  
  Exception is entered with `mcause` set to 0x5.
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6_v0.1.0, CV32A6-step2, CV64A6-step3
* **Unique verification tag:** VP_traps_F009_S001_I000
* **Link to Coverage:** 
* **Comments**
  
  *(none)*  
  
#### Item: 001

* **Requirement location:** Privileged Architecture Version 20211203, Chapter 3.7.1
* **Feature Description**
  
  If aligned or not aligned load-reserved is attempted in a PMP region without write permission, a load access fault exception is taken.
* **Verification Goals**
  
  Exception is entered with `mcause` set to 0x5
* **Pass/Fail Criteria:** NDY (Not Defined Yet)
* **Test Type:** NDY (Not Defined Yet)
* **Coverage Method:** NDY (Not Defined Yet)
* **Applicable Cores:** CV32A6_v0.1.0, CV64A6-step3
* **Unique verification tag:** VP_traps_F009_S001_I001
* **Link to Coverage:** 
* **Comments**
  
  *(none)*  
  
### Sub-feature: 002_store_amo_access

#### Item: 000

* **Requirement location:** Privileged Architecture Version 20211203, Chapter 3.7.1
* **Feature Description**
  
  If aligned or not aligned store is attempted in a PMP region without write permission, a store/AMO access fault exception is taken.
* **Verification Goals**
  
  Exception is entered with `mcause` set to 0x7
* **Pass/Fail Criteria:** NDY (Not Defined Yet)
* **Test Type:** NDY (Not Defined Yet)
* **Coverage Method:** NDY (Not Defined Yet)
* **Applicable Cores:** CV32A6_v0.1.0, CV32A6-step2, CV64A6-step3
* **Unique verification tag:** VP_traps_F009_S002_I000
* **Link to Coverage:** 
* **Comments**
  
  *(none)*  
  
#### Item: 001

* **Requirement location:** Privileged Architecture Version 20211203, Chapter 3.7.1
* **Feature Description**
  
  If aligned or not aligned store conditional is attempted in a PMP region without write permission, a store/AMO access fault exception is taken.
* **Verification Goals**
  
  Exception is entered with `mcause` set to 0x7
* **Pass/Fail Criteria:** NDY (Not Defined Yet)
* **Test Type:** NDY (Not Defined Yet)
* **Coverage Method:** NDY (Not Defined Yet)
* **Applicable Cores:** CV32A6_v0.1.0, CV64A6-step3
* **Unique verification tag:** VP_traps_F009_S002_I001
* **Link to Coverage:** 
* **Comments**
  
  *(none)*  
  
#### Item: 002

* **Requirement location:** Privileged Architecture Version 20211203, Chapter 3.7.1
* **Feature Description**
  
  If aligned or not aligned AMO is attempted in a PMP region without write permission, a store/AMO access fault exception is taken.
* **Verification Goals**
  
  Exception is entered with `mcause` set to 0x7
* **Pass/Fail Criteria:** NDY (Not Defined Yet)
* **Test Type:** NDY (Not Defined Yet)
* **Coverage Method:** NDY (Not Defined Yet)
* **Applicable Cores:** CV32A6_v0.1.0, CV64A6-step3
* **Unique verification tag:** VP_traps_F009_S002_I002
* **Link to Coverage:** 
* **Comments**
  
  *(none)*  
  
### Sub-feature: 003_mtval

#### Item: 000

* **Requirement location:** Privileged Architecture Version 20211203, Chapter 3.1.16
* **Feature Description**
  
  When an access fault exception is raised, the corresponding address is stored into `mtval` CSR.
* **Verification Goals**
  
  Check that when any access fault exception is raised, `mtval` CSR contains the address of the portion of the access causing the fault.
* **Pass/Fail Criteria:** NDY (Not Defined Yet)
* **Test Type:** NDY (Not Defined Yet)
* **Coverage Method:** NDY (Not Defined Yet)
* **Applicable Cores:** CV32A6_v0.1.0, CV32A6-step2, CV64A6-step3
* **Unique verification tag:** VP_traps_F009_S003_I000
* **Link to Coverage:** 
* **Comments**
  
  ZERO_TVAL parameter value?
## Feature: Environment Call

### Sub-feature: 000_ecall

#### Item: 000

* **Requirement location:** Privileged Architecture Version 20211203, Chapter 3.3.1
* **Feature Description**
  
  If an `ECALL` is executed from M-mode then an environment call exception is taken.
* **Verification Goals**
  
  Exception is entered with `mcause` set to 0xB.
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6_v0.1.0, CV32A6-step2, CV64A6-step3
* **Unique verification tag:** VP_traps_F010_S000_I000
* **Link to Coverage:** 
* **Comments**
  
  *(none)*  
  
#### Item: 001

* **Requirement location:** Privileged Architecture Version 20211203, Chapter 3.3.1
* **Feature Description**
  
  If an `ECALL` is executed from S-mode then an environment call exception is taken.
* **Verification Goals**
  
  Exception is entered with `mcause` set to 0x9.
* **Pass/Fail Criteria:** NDY (Not Defined Yet)
* **Test Type:** NDY (Not Defined Yet)
* **Coverage Method:** NDY (Not Defined Yet)
* **Applicable Cores:** CV32A6_v0.1.0, CV64A6-step3
* **Unique verification tag:** VP_traps_F010_S000_I001
* **Link to Coverage:** 
* **Comments**
  
  *(none)*  
  
#### Item: 002

* **Requirement location:** Privileged Architecture Version 20211203, Chapter 3.3.1
* **Feature Description**
  
  If an `ECALL` is executed from U-mode then an environment call exception is taken.
* **Verification Goals**
  
  Exception is entered with `mcause` set to 0x8.
* **Pass/Fail Criteria:** NDY (Not Defined Yet)
* **Test Type:** NDY (Not Defined Yet)
* **Coverage Method:** NDY (Not Defined Yet)
* **Applicable Cores:** CV32A6_v0.1.0, CV64A6-step3
* **Unique verification tag:** VP_traps_F010_S000_I002
* **Link to Coverage:** 
* **Comments**
  
  *(none)*  
  
## Feature: Page Fault

### Sub-feature: 000_instr_page

#### Item: 000

* **Requirement location:** Privileged Architecture Version 20211203, Chapter 4.3.1, 4.4.1, 4.5.1
* **Feature Description**
  
  TBD
* **Verification Goals**
  
  TBD
* **Pass/Fail Criteria:** NDY (Not Defined Yet)
* **Test Type:** NDY (Not Defined Yet)
* **Coverage Method:** NDY (Not Defined Yet)
* **Applicable Cores:** CV32A6_v0.1.0, CV64A6-step3
* **Unique verification tag:** VP_traps_F011_S000_I000
* **Link to Coverage:** 
* **Comments**
  
  MMU related
### Sub-feature: 001_load_page

#### Item: 000

* **Requirement location:** Privileged Architecture Version 20211203, Chapter 4.3.1, 4.4.1, 4.5.1
* **Feature Description**
  
  TBD
* **Verification Goals**
  
  TBD
* **Pass/Fail Criteria:** NDY (Not Defined Yet)
* **Test Type:** NDY (Not Defined Yet)
* **Coverage Method:** NDY (Not Defined Yet)
* **Applicable Cores:** CV32A6_v0.1.0, CV64A6-step3
* **Unique verification tag:** VP_traps_F011_S001_I000
* **Link to Coverage:** 
* **Comments**
  
  MMU related
### Sub-feature: 002_store_page

#### Item: 000

* **Requirement location:** Privileged Architecture Version 20211203, Chapter 4.3.1, 4.4.1, 4.5.1
* **Feature Description**
  
  TBD
* **Verification Goals**
  
  TBD
* **Pass/Fail Criteria:** NDY (Not Defined Yet)
* **Test Type:** NDY (Not Defined Yet)
* **Coverage Method:** NDY (Not Defined Yet)
* **Applicable Cores:** CV32A6_v0.1.0, CV64A6-step3
* **Unique verification tag:** VP_traps_F011_S002_I000
* **Link to Coverage:** 
* **Comments**
  
  MMU related
### Sub-feature: 003_mtval

#### Item: 000

* **Requirement location:** Privileged Architecture Version 20211203, Chapter 3.1.16
* **Feature Description**
  
  When an page fault exception is raised, the corresponding address is stored into `mtval` CSR.
* **Verification Goals**
  
  Check that when any page fault exception is raised, `mtval` CSR contains the address of the portion of the access causing the fault.
* **Pass/Fail Criteria:** NDY (Not Defined Yet)
* **Test Type:** NDY (Not Defined Yet)
* **Coverage Method:** NDY (Not Defined Yet)
* **Applicable Cores:** CV32A6_v0.1.0, CV64A6-step3
* **Unique verification tag:** VP_traps_F011_S003_I000
* **Link to Coverage:** 
* **Comments**
  
  MMU related  
  ZERO_TVAL parameter value?

# FRONTEND module

## PC generation stage feature

### 001_BTB sub-feature

#### 002 item

* **Requirement location:** FRONTEND sub-system/functionality/PC generation stage/Branch Predict
* **Feature Description:** If instruction is a JALR and BTB (Branch Target Buffer) returns a valid address, next PC is predicted by BTB. Else JALR is not considered as a control flow instruction, which will generate a mispredict.
* **Verification goals:** Execute test with JALR instructions. Functional cov: JALR is executed and BTB output is not valid.
* **Pass/Fail Criteria:** Check RM
* **Test Type:** RISC-V Arch-test
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1
* **Link to Coverage:** VP_IP003_P001_I002
* **Comments:** 

### 002_BHT sub-feature

#### 002 item

* **Requirement location:** FRONTEND sub-system/functionality/PC generation stage/Branch Predict
* **Feature Description:** If instruction is a branch and BTH (Branch History table) returns a valid address, next PC is predicted by BHT. Else branch is not considered as an control flow instruction, which will generate a mispredict when branch is taken.
* **Verification goals:** Execute test with BRANCH instructions. Functional cov: a BRANCH is executed, BTB output is not valid and the branch is taken.
* **Pass/Fail Criteria:** Check RM
* **Test Type:** RISC-V Arch-test
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1
* **Link to Coverage:** VP_IP003_P002_I002
* **Comments:** 

### 003_RAS sub-feature

#### 002 item

* **Requirement location:** FRONTEND sub-system/functionality/PC generation stage/Branch Predict
* **Feature Description:** If instruction is a RET and RAS (Return Address Stack) returns a valid address and RET has already been consummed by instruction queue. Else RET is considered as a control flow instruction but next PC is not predicted. A mispredict wil be generated.
* **Verification goals:** Execute test with RET instructions. Functional cov: RET is executed and RAS output is not valid.
* **Pass/Fail Criteria:** Check RM
* **Test Type:** RISC-V Arch-test
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1
* **Link to Coverage:** VP_IP003_P003_I002
* **Comments:** 

### 004_Return from environment call sub-feature

#### 000 item

* **Requirement location:** FRONTEND sub-system/functionality/PC generation stage/Return from env call
* **Feature Description:** When CSR asks a return from an environment call, the PC is assigned to the successive PC to the one stored in the CSR [m-s]epc register.
* **Verification goals:** Set two different addresses for mepc and sepc in CSR registers. Use a arc_test returning from machine env call. Check by assertion that when machine return occurs the mepc address is fetched. Functional cov: execute a machine return.
* **Pass/Fail Criteria:** Assertion
* **Test Type:** RISC-V Arch-test
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1
* **Link to Coverage:** VP_IP003_P004_I000
* **Comments:** 

### 005_Exception/Interrupt sub-feature

#### 000 item

* **Requirement location:** FRONTEND sub-system/functionality/PC generation stage/Exception
* **Feature Description:** If an exception (or interrupt, which is in the context of RISC-V systems quite similar) is triggered by the COMMIT, the next PC Gen is assigned to the CSR trap vector base address. The trap vector base address can be different depending on whether the exception traps to S-Mode or M-Mode (user mode exceptions are currently not supported)
* **Verification goals:** Set two different addresses for machine and supervisor handlers in CSR registers. Use a test which executes in machine mode and generates a machine exception by UVM. Check by assertion that when machine exception occurs the machine address is fetched. Functional cov: exception occurs in machine mode.
* **Pass/Fail Criteria:** Assertion
* **Test Type:** RISC-V Arch-test
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1
* **Link to Coverage:** VP_IP003_P005_I000
* **Comments:** 

### 006_Pipeline flush sub-feature

#### 000 item

* **Requirement location:** FRONTEND sub-system/functionality/PC generation stage/Pipeline flush
* **Feature Description:** FRONTEND starts fetching from the next instruction again in order to take the up-dated information into account
* **Verification goals:** [no need to verify this point]
* **Pass/Fail Criteria:** NDY (Not Defined Yet)
* **Test Type:** NDY (Not Defined Yet)
* **Coverage Method:** NDY (Not Defined Yet)
* **Applicable Cores:** CV32A6-step1
* **Link to Coverage:** VP_IP003_P006_I000
* **Comments:** 

### 007_Debug sub-feature

### 008_Address mapping change sub-feature

### 009_Pc gen priority sub-feature

#### 000 item

* **Requirement location:** FRONTEND sub-system/functionality/PC generation stage
* **Feature Description:** The next PC can originate from the following sources (listed in order of precedence)
* **Verification goals:** Use arc_test executing return from env call and generate Exceptions by UVM during reset, Branch predict, default, mispredict, replay and return from env call. Functional cov: monitor the 6 events
* **Pass/Fail Criteria:** Check RM
* **Test Type:** RISC-V Arch-test
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1
* **Link to Coverage:** VP_IP003_P009_I000
* **Comments:** 

#### 002 item

* **Requirement location:** FRONTEND sub-system/functionality/PC generation stage
* **Feature Description:** The next PC can originate from the following sources (listed in order of precedence)
* **Verification goals:** [other cases to be elaborated]
* **Pass/Fail Criteria:** NDY (Not Defined Yet)
* **Test Type:** NDY (Not Defined Yet)
* **Coverage Method:** NDY (Not Defined Yet)
* **Applicable Cores:** CV32A6-step1
* **Link to Coverage:** VP_IP003_P009_I002
* **Comments:** 

## BTB feature

### 000_flush sub-feature

### 001_table depth sub-feature

### 002_Table update sub-feature

### 003_debug is not intrusive sub-feature

## BHT feature

### 000_flush sub-feature

### 002_table update sub-feature

### 003_saturation sub-feature

#### 000 item

* **Requirement location:** FRONTEND sub-system/Architecture and Modules/BHT
* **Feature Description:** The Branch History table is a two-bit saturation counter that takes the virtual address of the current fetched instruction by the CACHE. It states whether the current branch request should be taken or not. The two bit counter is updated by the successive execution of the current instructions as shown in the following figure.
* **Verification goals:** Execute a serie of taken and not taken branch to check the saturation mechanism
* **Pass/Fail Criteria:** NDY (Not Defined Yet)
* **Test Type:** NDY (Not Defined Yet)
* **Coverage Method:** NDY (Not Defined Yet)
* **Applicable Cores:** CV32E40P, CV32E40S, CV32E40X, CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP005_P003_I000
* **Comments:** 

### 004_Table depth sub-feature

### 005_Debug is not intrusive sub-feature

## RAS feature

### 000_flush sub-feature

### 001_table depth sub-feature

### 002_Table update sub-feature

### 003_Debug is not intrusive sub-feature

## Instr_realign feature

### 000_C extension sub-feature

### 001_Flush sub-feature

## Instr_queue feature

### 000_FIFO depth sub-feature

#### 000 item

* **Requirement location:** FRONTEND sub-system/Architecture and Modules/Instr_queue
* **Feature Description:** The instruction queue contains max 4 instructions.
* **Verification goals:** Confirm that the best configuration for instruction queue entry number is 4 by monitoring the Coremark performance and silicon footprint
* **Pass/Fail Criteria:** Other
* **Test Type:** Other
* **Coverage Method:** N/A
* **Applicable Cores:** CV32A6-step1
* **Link to Coverage:** VP_IP008_P000_I000
* **Comments:** 

### 001_Page fault exception sub-feature

### 002_Flush sub-feature

## Instr_scan feature

## Fetch stage feature

### 001_MMU translation sub-feature

### 002_Exceptions sub-feature

#### 000 item

* **Requirement location:** FRONTEND sub-system/functionality/Fetch stage
* **Feature Description:** Memory and MMU (MMU is not enabled in CV32A6-step1) can feedback potential exceptions generated by the memory fetch request. They can be bus errors, invalid accesses or instruction page faults.
* **Verification goals:** Generate a bus error exception by UVM or by test (to be decided) and check that the exception address is fetched. Functional cov: a bus error exception occurs.
* **Pass/Fail Criteria:** NDY (Not Defined Yet)
* **Test Type:** NDY (Not Defined Yet)
* **Coverage Method:** NDY (Not Defined Yet)
* **Applicable Cores:** CV32A6-step1
* **Link to Coverage:** VP_IP010_P002_I000
* **Comments:** 

#### 002 item

* **Requirement location:** FRONTEND sub-system/functionality/Fetch stage
* **Feature Description:** Memory and MMU (MMU is not enabled in CV32A6-step1) can feedback potential exceptions generated by the memory fetch request. They can be bus errors, invalid accesses or instruction page faults.
* **Verification goals:** Generate an invalid access exception by UVM or by test (to be decided) and check that the exception address is fetched. Functional cov: an invalid access exception occurs.
* **Pass/Fail Criteria:** NDY (Not Defined Yet)
* **Test Type:** NDY (Not Defined Yet)
* **Coverage Method:** NDY (Not Defined Yet)
* **Applicable Cores:** CV32A6-step1
* **Link to Coverage:** VP_IP010_P002_I002
* **Comments:** 


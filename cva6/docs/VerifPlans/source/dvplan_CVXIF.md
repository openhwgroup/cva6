# Module: CVXIF

## Feature: Issue Interface

### Sub-feature: 000_issue_req signals stable

#### Item: 000

* **Requirement location:** 
* **Feature Description**
  
  The “instr” and “mode” signals remain stable during an Issue request transaction.
* **Verification Goals**
  
  Check that “mode” and “instr” are stable during an issue transaction (cannot be modified by an instruction when transaction issue is in process)
* **Pass/Fail Criteria:** Assertion
* **Test Type:** Constrained Random
* **Coverage Method:** Assertion Coverage
* **Applicable Cores:** CV32A6_v0.1.0, CV32A6-step2, CV64A6-step3
* **Unique verification tag:** VP_CVXIF_F000_S000_I000
* **Link to Coverage:** 
* **Comments**
  
  *(none)*  
  
### Sub-feature: 001_mode signal value

#### Item: 000

* **Requirement location:** 
* **Feature Description**
  
  When issue transaction starts, instruction and current CPU mode are provided
* **Verification Goals**
  
  Check that a mode modification coming from execution of a first instruction is well provided to the following offloaded instruction
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6_v0.1.0, CV32A6-step2, CV64A6-step3
* **Unique verification tag:** VP_CVXIF_F000_S001_I000
* **Link to Coverage:** 
* **Comments**
  
  *(none)*  
  
#### Item: 001

* **Requirement location:** 
* **Feature Description**
  
  Check “mode” signal values.
* **Verification Goals**
  
  Check that mode take a value that the CPU supports : Privilege level (2’b00 = User, 2’b01 = Supervisor, 2’b10 = Reserved,  
   2’b11 = Machine).
* **Pass/Fail Criteria:** NDY (Not Defined Yet)
* **Test Type:** NDY (Not Defined Yet)
* **Coverage Method:** NDY (Not Defined Yet)
* **Applicable Cores:** CV32A6_v0.1.0, CV32A6-step2, CV64A6-step3
* **Unique verification tag:** VP_CVXIF_F000_S001_I001
* **Link to Coverage:** 
* **Comments**
  
  *(none)*  
  
### Sub-feature: 002_rs_valid signal transition order

#### Item: 000

* **Requirement location:** 
* **Feature Description**
  
  During a transaction, each bit of “rs_valid” can transition from 0 to 1 but are not allowed to transition back to 0.
* **Verification Goals**
  
  For issue transaction which lasts more than one cycle, check that asserted “rs_valid” signals do not transition back to 0.(for i in [0;2] if rs_valid[i] = 1 then rs_valid[i] → 0 cannot happen)
* **Pass/Fail Criteria:** Assertion
* **Test Type:** Constrained Random
* **Coverage Method:** Assertion Coverage
* **Applicable Cores:** CV32A6_v0.1.0, CV32A6-step2, CV64A6-step3
* **Unique verification tag:** VP_CVXIF_F000_S002_I000
* **Link to Coverage:** 
* **Comments**
  
  *(none)*  
  
### Sub-feature: 003_rs signal value

#### Item: 000

* **Requirement location:** 
* **Feature Description**
  
  If XLEN = X_RFR_WIDTH, then rs[X_NUM_RS-1:0] correspond to  rs1 and rs2 CPU registers (and rs3 if X_NUM_RS = 3).
* **Verification Goals**
  
  For every issue transaction check that rs signal correspond to rs1,rs2(rs3) value in CPU register file.
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6_v0.1.0, CV32A6-step2, CV64A6-step3
* **Unique verification tag:** VP_CVXIF_F000_S003_I000
* **Link to Coverage:** 
* **Comments**
  
  *(none)*  
  
#### Item: 001

* **Requirement location:** 
* **Feature Description**
  
  rs signals are only required to be stable during the part of a transaction in which these signals are considered to be valid.
* **Verification Goals**
  
  Check that rs signals are stable when issue_valid==1 && the corresponding bit in rs_valid is 1.
* **Pass/Fail Criteria:** Assertion
* **Test Type:** NDY (Not Defined Yet)
* **Coverage Method:** Assertion Coverage
* **Applicable Cores:** CV32A6_v0.1.0, CV32A6-step2, CV64A6-step3
* **Unique verification tag:** VP_CVXIF_F000_S003_I001
* **Link to Coverage:** 
* **Comments**
  
  *(none)*  
  
#### Item: 002

* **Requirement location:** 
* **Feature Description**
  
  If XLEN != X_RFR_WIDTH , then rs[X_NUM_RS-1:0] correspond to even/odd register pair with rs1, rs2, (rs3) are even register and even register is provided in the 32 lower bits of rs signal.
* **Verification Goals**
  
  For every issue transaction check that rs signal correspond to the concatenation of rs1/rs1+1,rs2/rs2+1, (rs3/rs3+1) value in CPU register file and even register is in the 32 lower bits of rs.
* **Pass/Fail Criteria:** NDY (Not Defined Yet)
* **Test Type:** NDY (Not Defined Yet)
* **Coverage Method:** NDY (Not Defined Yet)
* **Applicable Cores:** CV32A6_v0.1.0, CV32A6-step2, CV64A6-step3
* **Unique verification tag:** VP_CVXIF_F000_S003_I002
* **Link to Coverage:** 
* **Comments**
  
  *(none)*  
  
### Sub-feature: 004_Default value for unaccepted instruction

#### Item: 000

* **Requirement location:** 
* **Feature Description**
  
  If accept == 0 :  
  Writeback == 0; dualwrite == 0; dualread == 0; loadstore == 0; exc = 0.
* **Verification Goals**
  
  Check that for writeback; dualwrite; dualread; loadstore; exc signals if accept == 0 then all those signals are 0.
* **Pass/Fail Criteria:** Assertion
* **Test Type:** Constrained Random
* **Coverage Method:** Assertion Coverage
* **Applicable Cores:** CV32A6_v0.1.0, CV32A6-step2, CV64A6-step3
* **Unique verification tag:** VP_CVXIF_F000_S004_I000
* **Link to Coverage:** 
* **Comments**
  
  *(none)*  
  
### Sub-feature: 005_Illegal Instruction causes

#### Item: 000

* **Requirement location:** 
* **Feature Description**
  
  The CPU shall cause an illegal instruction if:  
  - an instruction is considered to be valid by the CPU and accepted by the coprocessor (accept = 1)  
  - neither to be valid by the CPU nor accepted by the coprocessor (accept = 0)
* **Verification Goals**
  
  - CPU causes illegal instruction for instruction accepted by the core and the coprocessor.  
  - CPU causes illegal instruction exception for instruction that are not valid for coprocessor and CPU
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6_v0.1.0, CV32A6-step2, CV64A6-step3
* **Unique verification tag:** VP_CVXIF_F000_S005_I000
* **Link to Coverage:** 
* **Comments**
  
  *(none)*  
  
### Sub-feature: 006_issue uniquness

#### Item: 000

* **Requirement location:** 
* **Feature Description**
  
  Check for issue id validity.
* **Verification Goals**
  
  Check that the issue interface doesn't issue an "id" that isn't legal to be used (has not fully completed).
* **Pass/Fail Criteria:** Other
* **Test Type:** Constrained Random
* **Coverage Method:** N/A
* **Applicable Cores:** CV32A6_v0.1.0, CV32A6-step2, CV64A6-step3
* **Unique verification tag:** VP_CVXIF_F000_S006_I000
* **Link to Coverage:** 
* **Comments**
  
  *(none)*  
  
### Sub-feature: 007_coprocessor decoding

#### Item: 000

* **Requirement location:** 
* **Feature Description**
  
  Accept = 1 if:   
  - coprocessor can handle the instruction based on decoding “instr”and "mode".  
  - “issue_valid” == 1 and required bit(s) of “rs_valid” are 1.
* **Verification Goals**
  
  To be checked in coprocessor.
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6_v0.1.0, CV32A6-step2, CV64A6-step3
* **Unique verification tag:** VP_CVXIF_F000_S007_I000
* **Link to Coverage:** 
* **Comments**
  
  *(none)*  
  
### Sub-feature: 008_Transaction definition

#### Item: 000

* **Requirement location:** 
* **Feature Description**
  
  “issue_resp” signals and “issue_req” signals are accepted when “issue_valid” == “issue_ready” == 1  
  “issue_resp” is valid when "valid==ready==1".  
  “issue_req” is valid when "valid==1"
* **Verification Goals**
  
  The definition of a transaction.   
  Not to be verified.
* **Pass/Fail Criteria:** Other
* **Test Type:** Other
* **Coverage Method:** N/A
* **Applicable Cores:** CV32A6_v0.1.0, CV32A6-step2, CV64A6-step3
* **Unique verification tag:** VP_CVXIF_F000_S008_I000
* **Link to Coverage:** 
* **Comments**
  
  *(none)*  
  
## Feature: Commit Interface

### Sub-feature: 000_commit_valid pulse

#### Item: 000

* **Requirement location:** 
* **Feature Description**
  
  The “commit_valid” == 1 exactly one clk cycle for every offloaded  Instruction by the coprocessor (whether accepted or not).
* **Verification Goals**
  
  For every offloaded  instruction, check that commit_valid is asserted exactly one clk cycle ( is a pulse ).
* **Pass/Fail Criteria:** Assertion
* **Test Type:** Constrained Random
* **Coverage Method:** Assertion Coverage
* **Applicable Cores:** CV32A6_v0.1.0, CV32A6-step2, CV64A6-step3
* **Unique verification tag:** VP_CVXIF_F001_S000_I000
* **Link to Coverage:** 
* **Comments**
  
  *(none)*  
  
### Sub-feature: 001_commit transaction uniquness

#### Item: 000

* **Requirement location:** 
* **Feature Description**
  
  There is a unique commit transaction for every issue transaction (unique until an instruction has "fully completed" = its result has been submitted).
* **Verification Goals**
  
  Check that the commit interface doesn't commit an "id" that isn't legal to be used (hasn't been seen in earlier stages, or has not fully completed).
* **Pass/Fail Criteria:** Self-Check
* **Test Type:** Other
* **Coverage Method:** N/A
* **Applicable Cores:** CV32A6_v0.1.0, CV32A6-step2, CV64A6-step3
* **Unique verification tag:** VP_CVXIF_F001_S001_I000
* **Link to Coverage:** 
* **Comments**
  
  *(none)*  
  
### Sub-feature: 002_commit transaction for every issue transaction

#### Item: 000

* **Requirement location:** 
* **Feature Description**
  
  - The CPU shall perform a commit transaction for every issue transaction, independent of the accept value of the issue transaction.  
  - For each offloaded and accepted instruction the core is guaranteed to (eventually) signal that such an instruction is either no longer speculative and can be committed (commit_valid is 1 and commit_kill is 0) or that the instruction must be killed (commit_valid is 1 and commit_kill is 1).
* **Verification Goals**
  
  Check that for each issue transaction, the commit transaction is sent at the same clock cycle than the issue transaction, or at any clock cycle after the issue transaction.
* **Pass/Fail Criteria:** Assertion
* **Test Type:** Constrained Random
* **Coverage Method:** Assertion Coverage
* **Applicable Cores:** CV32A6_v0.1.0, CV32A6-step2, CV64A6-step3
* **Unique verification tag:** VP_CVXIF_F001_S002_I000
* **Link to Coverage:** 
* **Comments**
  
  *(none)*  
  
### Sub-feature: 003_Transaction definition

#### Item: 000

* **Requirement location:** 
* **Feature Description**
  
  The signals in commit are valid when commit_valid is 1.
* **Verification Goals**
  
  The definition of a transaction.  
  Not to be verified.
* **Pass/Fail Criteria:** Other
* **Test Type:** NDY (Not Defined Yet)
* **Coverage Method:** N/A
* **Applicable Cores:** CV32A6_v0.1.0, CV32A6-step2, CV64A6-step3
* **Unique verification tag:** VP_CVXIF_F001_S003_I000
* **Link to Coverage:** 
* **Comments**
  
  *(none)*  
  
## Feature: Result Interface

### Sub-feature: 000_no speculative result transaction

#### Item: 000

* **Requirement location:** 
* **Feature Description**
  
  A coprocessor is not allowed to perform speculative result transactions.
* **Verification Goals**
  
  There is no result transaction for instructions that haven't been committed. Check that Result valid is only asserted for instructions that were committed (commit_valid == 1 && commit_kill == 0).
* **Pass/Fail Criteria:** Other
* **Test Type:** Other
* **Coverage Method:** N/A
* **Applicable Cores:** CV32A6_v0.1.0, CV32A6-step2, CV64A6-step3
* **Unique verification tag:** VP_CVXIF_F002_S000_I000
* **Link to Coverage:** 
* **Comments**
  
  *(none)*  
  
### Sub-feature: 001_out of order result transaction

#### Item: 000

* **Requirement location:** 
* **Feature Description**
  
  A coprocessor is allowed to provide results to the core in an out of order fashion.
* **Verification Goals**
  
  Check that the CPU is able to receive the result in an out of order fashion.
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6_v0.1.0, CV32A6-step2, CV64A6-step3
* **Unique verification tag:** VP_CVXIF_F002_S001_I000
* **Link to Coverage:** 
* **Comments**
  
  *(none)*  
  
### Sub-feature: 002_result transaction uniquness

#### Item: 000

* **Requirement location:** 
* **Feature Description**
  
  Each accepted offloaded (committed and not killed) instruction shall have exactly one result group transaction (even if no data needs to be written back to the CPU’s register file).
* **Verification Goals**
  
  There is an unique result transaction for every accepted and commit instruction.
* **Pass/Fail Criteria:** Other
* **Test Type:** Other
* **Coverage Method:** N/A
* **Applicable Cores:** CV32A6_v0.1.0, CV32A6-step2, CV64A6-step3
* **Unique verification tag:** VP_CVXIF_F002_S002_I000
* **Link to Coverage:** 
* **Comments**
  
  *(none)*  
  
### Sub-feature: 003_result packet stability

#### Item: 000

* **Requirement location:** 
* **Feature Description**
  
  The signals in result shall remain stable during a result transaction (except data ...)
* **Verification Goals**
  
  Check that result signals (except data) are stable during result transaction (result_valid==1 jusqu'à valid==ready ==1)
* **Pass/Fail Criteria:** Assertion
* **Test Type:** Constrained Random
* **Coverage Method:** Assertion Coverage
* **Applicable Cores:** CV32A6_v0.1.0, CV32A6-step2, CV64A6-step3
* **Unique verification tag:** VP_CVXIF_F002_S003_I000
* **Link to Coverage:** 
* **Comments**
  
  *(none)*  
  
### Sub-feature: 004_data stability

#### Item: 000

* **Requirement location:** 
* **Feature Description**
  
  Data is only required to remain stable during result transactions in which "we" is not 0.
* **Verification Goals**
  
  Check that "data" remains stable when we==1.
* **Pass/Fail Criteria:** Assertion
* **Test Type:** Constrained Random
* **Coverage Method:** Assertion Coverage
* **Applicable Cores:** CV32A6_v0.1.0, CV32A6-step2, CV64A6-step3
* **Unique verification tag:** VP_CVXIF_F002_S004_I000
* **Link to Coverage:** 
* **Comments**
  
  *(none)*  
  
### Sub-feature: 005_synchronous exception

#### Item: 000

* **Requirement location:** 
* **Feature Description**
  
  The exc is used to signal synchronous exceptions. A synchronous exception will lead to a trap in CPU unless the corresponding instruction is killed.
* **Verification Goals**
  
  Check that synchronous exception (exc ==1) leads to a trap in the CPU if the instruction is committed.
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6_v0.1.0, CV32A6-step2, CV64A6-step3
* **Unique verification tag:** VP_CVXIF_F002_S005_I000
* **Link to Coverage:** 
* **Comments**
  
  *(none)*  
  
#### Item: 001

* **Requirement location:** 
* **Feature Description**
  
  exccode provides the least significant bits of the exception code bitfield of the mcause CSR.
* **Verification Goals**
  
  Check that exccode signal is the value of the mcause CSR when exc == 1.
* **Pass/Fail Criteria:** NDY (Not Defined Yet)
* **Test Type:** NDY (Not Defined Yet)
* **Coverage Method:** NDY (Not Defined Yet)
* **Applicable Cores:** CV32A6_v0.1.0, CV32A6-step2, CV64A6-step3
* **Unique verification tag:** VP_CVXIF_F002_S005_I001
* **Link to Coverage:** 
* **Comments**
  
  *(none)*  
  
#### Item: 002

* **Requirement location:** 
* **Feature Description**
  
   "we" shall be driven to 0 by the coprocessor for synchronous exceptions.
* **Verification Goals**
  
  Check that "we" signal == 0 when exc == 1.
* **Pass/Fail Criteria:** Assertion
* **Test Type:** NDY (Not Defined Yet)
* **Coverage Method:** Assertion Coverage
* **Applicable Cores:** CV32A6_v0.1.0, CV32A6-step2, CV64A6-step3
* **Unique verification tag:** VP_CVXIF_F002_S005_I002
* **Link to Coverage:** 
* **Comments**
  
  *(none)*  
  
### Sub-feature: 006_"we" value when dualwrite

#### Item: 000

* **Requirement location:** 
* **Feature Description**
  
  we is 2 bits wide when XLEN` = 32 and X_RFW_WIDTH = 64, and 1 bit wide otherwise. If "we" is 2 bits wide, then we[1] is only allowed to be 1 if we[0] is 1 as well (i.e. for dual writeback).
* **Verification Goals**
  
  For dualwrite instruction, check that we[1]==1 is only allowed if we[0] == 1.
* **Pass/Fail Criteria:** Assertion
* **Test Type:** Constrained Random
* **Coverage Method:** Assertion Coverage
* **Applicable Cores:** CV32A6_v0.1.0, CV32A6-step2, CV64A6-step3
* **Unique verification tag:** VP_CVXIF_F002_S006_I000
* **Link to Coverage:** 
* **Comments**
  
  *(none)*  
  
### Sub-feature: 007_proper result transaction

#### Item: 000

* **Requirement location:** 
* **Feature Description**
  
  Result transaction starts in the cycle that result_valid = 1 and ends in the cycle that both result_valid == result_ready == 1.
* **Verification Goals**
  
  Check that result transaction ends properly.
* **Pass/Fail Criteria:** Assertion
* **Test Type:** Constrained Random
* **Coverage Method:** Assertion Coverage
* **Applicable Cores:** CV32A6_v0.1.0, CV32A6-step2, CV64A6-step3
* **Unique verification tag:** VP_CVXIF_F002_S007_I000
* **Link to Coverage:** 
* **Comments**
  
  *(none)*  
  

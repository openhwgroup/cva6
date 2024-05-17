# Module: AXI

## Feature: Burst

### Sub-feature: 000_Control_Signals

#### Item: 000

* **Requirement location:** AXI Design doc - Address structure
* **Feature Description**
  
  All transaction performed by CVA6 are of type INCR. AxBURST = 0b01
* **Verification Goals**
  
  Ensure that AxBURST == 0b01 is always true while AxVALID is asserted.
* **Pass/Fail Criteria:** Assertion
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6_v0.1.0, CV32A6-step2, CV64A6-step3
* **Unique verification tag:** VP_1_F005_S000_I000
* **Link to Coverage:** 
* **Comments**
  
  *(none)*  
  
#### Item: 001

* **Requirement location:** AXI Design doc - Address structure
* **Feature Description**
  
  All Read transaction performed by CVA6 are of burst length less or equal to ICACHE_LINE_WIDTH/64. ARLEN = 0b01 or 0b00
* **Verification Goals**
  
  Ensure that ARLEN == 0b01 || ARLEN == 0b00 is always true while ARVALID is asserted.
* **Pass/Fail Criteria:** Assertion
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6_v0.1.0, CV32A6-step2, CV64A6-step3
* **Unique verification tag:** VP_1_F005_S000_I001
* **Link to Coverage:** 
* **Comments**
  
  *(none)*  
  
#### Item: 002

* **Requirement location:** AXI Design doc - Address structure
* **Feature Description**
  
  All write transaction performed by CVA6 are of burst lenght equal to 1. AWLEN = 0b00
* **Verification Goals**
  
  Ensure that AWLEN == 0b00 is always true while AWVALID is asserted.
* **Pass/Fail Criteria:** Assertion
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6_v0.1.0, CV32A6-step2, CV64A6-step3
* **Unique verification tag:** VP_1_F005_S000_I002
* **Link to Coverage:** 
* **Comments**
  
  *(none)*  
  
#### Item: 003

* **Requirement location:** https://developer.arm.com/documentation/ihi0022/hc - (Section A3.4.1)
* **Feature Description**
  
  The size of a read transfer does not exceed the width of the data interface. The maximum value can be taking by AxSIZE is 3.
* **Verification Goals**
  
  Ensure that AxSIZE <= log2(AXI_DATA_WIDTH/8) is always true while ARVALID is asserted.
* **Pass/Fail Criteria:** Assertion
* **Test Type:** Constrained Random
* **Coverage Method:** Assertion Coverage
* **Applicable Cores:** CV32A6_v0.1.0, CV32A6-step2, CV64A6-step3
* **Unique verification tag:** VP_1_F005_S000_I003
* **Link to Coverage:** 
* **Comments**
  
  *(none)*  
  
#### Item: 013

* **Requirement location:** 
* **Feature Description**
  
  The maximum value can be taken by AxSIZE is XLEN/8
* **Verification Goals**
  
  Ensure that AxSIZE <= clog2(XLEN/8)
* **Pass/Fail Criteria:** NDY (Not Defined Yet)
* **Test Type:** Directed SelfChk
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6_v0.1.0, CV32A6-step2, CV64A6-step3
* **Unique verification tag:** VP_AXI_F005_S000_I013
* **Link to Coverage:** 
* **Comments**
  
  *(none)*  
  
#### Item: 014

* **Requirement location:** 
* **Feature Description**
  
  if(RV32) ARSIZE != 3 && ARLEN = 0 && ARID = 1, the maximum load instruction size is 4 bytes  
  ARSIZE can not be equal to 0, 1 or 2 if ARLOCK = 1
* **Verification Goals**
  
  Ensure that ARSIZE != 3 when ARID = 1 and ARLEN = 0  
  Ensure that ARSIZE != 0, 1 or 2 when ARID = 0  
  Ensure that ARSIZE != 0, 1 or 2 when ARLOCK = 1
* **Pass/Fail Criteria:** NDY (Not Defined Yet)
* **Test Type:** NDY (Not Defined Yet)
* **Coverage Method:** NDY (Not Defined Yet)
* **Applicable Cores:** CV32A6_v0.1.0, CV32A6-step2, CV64A6-step3
* **Unique verification tag:** VP_AXI_F005_S000_I014
* **Link to Coverage:** 
* **Comments**
  
  *(none)*  
  
#### Item: 015

* **Requirement location:** 
* **Feature Description**
  
  if(RVA) AxLOCK = 1 => AxSIZE > 1, CVA6 doesn't perform exclusive transaction with size lower than 4 bytes
* **Verification Goals**
  
  Ensure that AWSIZE > 1 when AWLOCK = 1
* **Pass/Fail Criteria:** NDY (Not Defined Yet)
* **Test Type:** NDY (Not Defined Yet)
* **Coverage Method:** NDY (Not Defined Yet)
* **Applicable Cores:** CV32A6_v0.1.0, CV32A6-step2, CV64A6-step3
* **Unique verification tag:** VP_AXI_F005_S000_I015
* **Link to Coverage:** 
* **Comments**
  
  *(none)*  
  
## Feature: Signals

### Sub-feature: 000_ID

#### Item: 000

* **Requirement location:** AXI Design doc - Transaction Identifiers
* **Feature Description**
  
  The CVA6 identify read transaction with an ID equal to 0 or 1 for normal transaction, and 3 for exclusive transaction
* **Verification Goals**
  
  Ensure that ARID == 0b01 || ARID == 0b00 || (ARID == 0b11 && (Exclusive_Access || Atomic_transaction)) is always true while ARVALID is asserted.
* **Pass/Fail Criteria:** Assertion
* **Test Type:** Constrained Random
* **Coverage Method:** Assertion Coverage
* **Applicable Cores:** CV32A6_v0.1.0, CV32A6-step2, CV64A6-step3
* **Unique verification tag:** VP_1_F006_S000_I000
* **Link to Coverage:** 
* **Comments**
  
  *(none)*  
  
#### Item: 001

* **Requirement location:** AXI Design doc - Transaction Identifiers
* **Feature Description**
  
  The CVA6 identify write transaction with an ID equal to 1 for normal transaction, and 3 for exclusive transaction or atomic operations
* **Verification Goals**
  
  Ensure that AWID == 0b01 || AWID == 0b11 && (Exclusive_Access || Atomic_transaction) is always true while AWVALID is asserted.
* **Pass/Fail Criteria:** Assertion
* **Test Type:** Constrained Random
* **Coverage Method:** Assertion Coverage
* **Applicable Cores:** CV32A6_v0.1.0, CV32A6-step2, CV64A6-step3
* **Unique verification tag:** VP_1_F006_S000_I001
* **Link to Coverage:** 
* **Comments**
  
  *(none)*  
  
### Sub-feature: 001_User

#### Item: 000

* **Requirement location:** AXI Design doc - (table 2.2 and 2.5)
* **Feature Description**
  
  User-defined extension for the write and read address channel is not supported. AxUSER = 0b00
* **Verification Goals**
  
  Ensure that AxUSER = 0b00 is always true while AxVALID is asserted.
* **Pass/Fail Criteria:** Assertion
* **Test Type:** Constrained Random
* **Coverage Method:** Assertion Coverage
* **Applicable Cores:** CV32A6_v0.1.0, CV32A6-step2, CV64A6-step3
* **Unique verification tag:** VP_1_F006_S001_I000
* **Link to Coverage:** 
* **Comments**
  
  *(none)*  
  
#### Item: 001

* **Requirement location:** AXI Design doc - (table 2.4)
* **Feature Description**
  
  User-defined extension for the write response channel is not supported.
* **Verification Goals**
  
  Ensure that BUSER = 0b00 is always true while BVALID is asserted.
* **Pass/Fail Criteria:** Assertion
* **Test Type:** Constrained Random
* **Coverage Method:** Assertion Coverage
* **Applicable Cores:** CV32A6_v0.1.0, CV32A6-step2, CV64A6-step3
* **Unique verification tag:** VP_1_F006_S001_I001
* **Link to Coverage:** 
* **Comments**
  
  *(none)*  
  
### Sub-feature: 002_Quality_of_Service

#### Item: 000

* **Requirement location:** AXI Design doc - (table 2.2 and 2.5)
* **Feature Description**
  
  Quality of Service identifier is not supported. AxQOS = 0b0000
* **Verification Goals**
  
  Ensure that AxQOS = 0b0000 is always true while AxVALID is asserted.
* **Pass/Fail Criteria:** Assertion
* **Test Type:** Constrained Random
* **Coverage Method:** Assertion Coverage
* **Applicable Cores:** CV32A6_v0.1.0, CV32A6-step2, CV64A6-step3
* **Unique verification tag:** VP_1_F006_S002_I000
* **Link to Coverage:** 
* **Comments**
  
  *(none)*  
  
### Sub-feature: 003_Cache

#### Item: 000

* **Requirement location:** AXI Design Doc - Transaction Attributes: Memory types
* **Feature Description**
  
  AxCACHE always take 0b0010.
* **Verification Goals**
  
  Ensure that AxCACHE = 0b0010 is always true while AxVALID is asserted.
* **Pass/Fail Criteria:** Assertion
* **Test Type:** Constrained Random
* **Coverage Method:** Assertion Coverage
* **Applicable Cores:** CV32A6_v0.1.0, CV32A6-step2, CV64A6-step3
* **Unique verification tag:** VP_1_F006_S003_I000
* **Link to Coverage:** 
* **Comments**
  
  *(none)*  
  
### Sub-feature: 004_Protection

#### Item: 000

* **Requirement location:** AXI Design Doc - (Table 2.2 and 2.5)
* **Feature Description**
  
  Protection attributes always take the 0b000
* **Verification Goals**
  
  Ensure that AxPROT = 0b000 is always true while AxVALID is asserted.
* **Pass/Fail Criteria:** Assertion
* **Test Type:** Constrained Random
* **Coverage Method:** Assertion Coverage
* **Applicable Cores:** CV32A6_v0.1.0, CV32A6-step2, CV64A6-step3
* **Unique verification tag:** VP_1_F006_S004_I000
* **Link to Coverage:** 
* **Comments**
  
  *(none)*  
  
### Sub-feature: 008_Region

#### Item: 000

* **Requirement location:** AXI Design doc - (table 2.2 and 2.5)
* **Feature Description**
  
  Region indicator is not supported. AxREGION = 0b0000
* **Verification Goals**
  
  Ensure that AxREGION = 0b0000 is always true while AxVALID is asserted.
* **Pass/Fail Criteria:** Assertion
* **Test Type:** Constrained Random
* **Coverage Method:** Assertion Coverage
* **Applicable Cores:** CV32A6_v0.1.0, CV32A6-step2, CV64A6-step3
* **Unique verification tag:** VP_1_F006_S008_I000
* **Link to Coverage:** 
* **Comments**
  
  *(none)*  
  
### Sub-feature: 009_Strob

#### Item: 000

* **Requirement location:** 
* **Feature Description**
  
  CVA6 does not performe unaligned memory accesses, therefore WSTRB takes only combinations for aligned accesses
* **Verification Goals**
  
  Ensure that WSTRB does not take value different than 1, 2, 3, 4, 8, 12, 15, 16, 32, 48, 64, 128, 192, 240 and 255
* **Pass/Fail Criteria:** Assertion
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6_v0.1.0, CV32A6-step2, CV64A6-step3
* **Unique verification tag:** VP_AXI_F006_S009_I000
* **Link to Coverage:** 
* **Comments**
  
  *(none)*  
  
#### Item: 001

* **Requirement location:** 
* **Feature Description**
  
  If(RV32) WSTRB < 255, Since AWSIZE lower than 3, so the data bus cannot have more than 4 valid byte lanes
* **Verification Goals**
  
  Ensure that WSTRB does not take 255
* **Pass/Fail Criteria:** NDY (Not Defined Yet)
* **Test Type:** NDY (Not Defined Yet)
* **Coverage Method:** NDY (Not Defined Yet)
* **Applicable Cores:** CV32A6_v0.1.0, CV32A6-step2
* **Unique verification tag:** VP_AXI_F006_S009_I001
* **Link to Coverage:** 
* **Comments**
  
  *(none)*  
  
## Feature: Clock and Reset

### Sub-feature: 000_Signals_Value

#### Item: 000

* **Requirement location:** https://developer.arm.com/documentation/ihi0022/hc - (Section A3.1.2)
* **Feature Description**
  
  A value of X on [Ax | x]VALID is not permitted when not in reset
* **Verification Goals**
  
  Ensure that reset && [Ax | x]VALID != X is always true
* **Pass/Fail Criteria:** Assertion
* **Test Type:** ENV Capability
* **Coverage Method:** Assertion Coverage
* **Applicable Cores:** CV32A6_v0.1.0, CV32A6-step2, CV64A6-step3
* **Unique verification tag:** VP_1_F007_S000_I000
* **Link to Coverage:** 
* **Comments**
  
  *(none)*  
  
#### Item: 001

* **Requirement location:** https://developer.arm.com/documentation/ihi0022/hc - (Section A3.1.2)
* **Feature Description**
  
  A value of X on [Ax | x]READY is not permitted when not in reset
* **Verification Goals**
  
  Ensure that reset && [Ax | x]READY != X is always true
* **Pass/Fail Criteria:** Assertion
* **Test Type:** ENV Capability
* **Coverage Method:** Assertion Coverage
* **Applicable Cores:** CV32A6_v0.1.0, CV32A6-step2, CV64A6-step3
* **Unique verification tag:** VP_1_F007_S000_I001
* **Link to Coverage:** 
* **Comments**
  
  *(none)*  
  
#### Item: 002

* **Requirement location:** https://developer.arm.com/documentation/ihi0022/hc - (Figure A3-1)
* **Feature Description**
  
  [Ax | x]VALID is LOW for the first cycle after RESET goes HIGH
* **Verification Goals**
  
  Ensure that [Ax | x]VALID is low the first cycle after RESET
* **Pass/Fail Criteria:** Assertion
* **Test Type:** ENV Capability
* **Coverage Method:** Assertion Coverage
* **Applicable Cores:** CV32A6_v0.1.0, CV32A6-step2, CV64A6-step3
* **Unique verification tag:** VP_1_F007_S000_I002
* **Link to Coverage:** 
* **Comments**
  
  *(none)*  
  
### Sub-feature: 001_Hard_Reset

#### Item: 000

* **Requirement location:** 
* **Feature Description**
  
  Random hard reset during simulation.
* **Verification Goals**
  
  Ensure that the CVA6 restarts the test from the start address and does not crash after disabling the reset.
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6_v0.1.0, CV32A6-step2, CV64A6-step3
* **Unique verification tag:** VP_AXI_F007_S001_I000
* **Link to Coverage:** 
* **Comments**
  
  *(none)*  
  
## Feature: Handshake_Process

### Sub-feature: 000_Stability 

#### Item: 000

* **Requirement location:** https://developer.arm.com/documentation/ihi0022/hc - (Section A3.2.2)
* **Feature Description**
  
  All signals must remain stable when [Ax | x]VALID is asserted and [Ax | x]READY is LOW
* **Verification Goals**
  
  Ensure that all the signals does not change while [Ax | x]VALID is asserted and [Ax | x]READY not yet asserted.
* **Pass/Fail Criteria:** Assertion
* **Test Type:** ENV Capability
* **Coverage Method:** Assertion Coverage
* **Applicable Cores:** CV32A6_v0.1.0, CV32A6-step2, CV64A6-step3
* **Unique verification tag:** VP_1_F008_S000_I000
* **Link to Coverage:** 
* **Comments**
  
  *(none)*  
  
#### Item: 001

* **Requirement location:** https://developer.arm.com/documentation/ihi0022/hc - (Section A3.2.1)
* **Feature Description**
  
  [Ax | x]VALID must remain asserted until [Ax | x]READY is HIGH
* **Verification Goals**
  
  Ensure that [Ax | x]VALID does not change while [Ax | x]READY is low.
* **Pass/Fail Criteria:** Assertion
* **Test Type:** ENV Capability
* **Coverage Method:** Assertion Coverage
* **Applicable Cores:** CV32A6_v0.1.0, CV32A6-step2, CV64A6-step3
* **Unique verification tag:** VP_1_F008_S000_I001
* **Link to Coverage:** 
* **Comments**
  
  *(none)*  
  
### Sub-feature: 001_Timing

#### Item: 000

* **Requirement location:** https://developer.arm.com/documentation/ihi0022/hc - (Section A3.3.1)
* **Feature Description**
  
  The Manager must not wait for the Subordinate to assert ARREADY before asserting ARVALID
* **Verification Goals**
  
  Ensure that no errors are encountered as the testbench injects random Ready-to-Valid delays.  There are two cases to consider:  
    
  ARREADY is asserted on or after same cycle as ARVALID  
  ARREADY is asserted and deasserted during an interval when ARVALID is de-asserted
* **Pass/Fail Criteria:** Any/All
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6_v0.1.0, CV32A6-step2, CV64A6-step3
* **Unique verification tag:** VP_1_F008_S001_I000
* **Link to Coverage:** 
* **Comments**
  
  *(none)*  
  
#### Item: 002

* **Requirement location:** https://developer.arm.com/documentation/ihi0022/hc - (Section A3.3.1)
* **Feature Description**
  
  The Manager must not wait for the Subordinate to assert AWREADY before asserting AWVALID or WVALID.
* **Verification Goals**
  
  Ensure that no errors are encountered as the testbench injects random Ready-to-Valid delays. There are four cases to consider:    
                                            
  AWREADY is asserted on or after same cycle as AWVALID and WVALID is de-asserted  
  AWREADY is asserted on or after same cycle as WVALID  and AWVALID is de-asserted  
  AWREADY is asserted on or after same cycle as AWVALID and WVALID  
  AWREADY is asserted and deasserted during an interval when AWVALID and WVALID is de-asserted
* **Pass/Fail Criteria:** Any/All
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6_v0.1.0, CV32A6-step2, CV64A6-step3
* **Unique verification tag:** VP_1_F008_S001_I002
* **Link to Coverage:** 
* **Comments**
  
  *(none)*  
  
#### Item: 003

* **Requirement location:** https://developer.arm.com/documentation/ihi0022/hc - (Section A3.3.1)
* **Feature Description**
  
  The Manager must not wait for the Subordinate to assert WREADY before asserting AWVALID or WVALID.
* **Verification Goals**
  
  Ensure that no errors are encountered as the testbench injects random Ready-to-Valid delays. There are four cases to consider:    
                                                    
  WREADY is asserted on or after same cycle as AWVALID and WVALID is de-asserted  
  WREADY is asserted on or after same cycle as WVALID  and AWVALID is de-asserted  
  WREADY is asserted on or after same cycle as AWVALID and WVALID  
  WREADY is asserted and deasserted during an interval when AWVALID and WVALID is de-asserted
* **Pass/Fail Criteria:** Any/All
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6_v0.1.0, CV32A6-step2, CV64A6-step3
* **Unique verification tag:** VP_1_F008_S001_I003
* **Link to Coverage:** 
* **Comments**
  
  *(none)*  
  
#### Item: 005

* **Requirement location:** https://developer.arm.com/documentation/ihi0022/hc - (Section A3.3.1)
* **Feature Description**
  
  The Subordinate must not wait for the Manager to assert [B | R]READY before asserting [B | R]VALID
* **Verification Goals**
  
  No specific “observable checks” to be made in simulation. Testbench will always provide response data independently of [B | R]READY.
* **Pass/Fail Criteria:** Any/All
* **Test Type:** Other
* **Coverage Method:** N/A
* **Applicable Cores:** CV32A6_v0.1.0, CV32A6-step2, CV64A6-step3
* **Unique verification tag:** VP_1_F008_S001_I005
* **Link to Coverage:** 
* **Comments**
  
  *(none)*  
  
## Feature: Error Injection

### Sub-feature: 000_Protocol errors

#### Item: 003

* **Requirement location:** 
* **Feature Description**
  
  Injection error by randomizing resp signal.
* **Verification Goals**
  
  Randomize xRESP signals. The CVA6 shouldn’t crash if RESP signal indicate an error in a transaction.
* **Pass/Fail Criteria:** NDY (Not Defined Yet)
* **Test Type:** NDY (Not Defined Yet)
* **Coverage Method:** NDY (Not Defined Yet)
* **Applicable Cores:** CV32A6_v0.1.0, CV32A6-step2, CV64A6-step3
* **Unique verification tag:** VP_AXI_F009_S000_I003
* **Link to Coverage:** 
* **Comments**
  
  *(none)*  
  

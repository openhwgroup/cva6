# Module: CSR ACCESS VERIFICATION

## Feature: machineScratch(MSCRATCH)

### Sub-feature: 000_MSCRATCH

#### Item: 000

* **Requirement location:** riscv-privileged-20211203
* **Feature Description**
  
  To verify the Power-on Reset value for MSCRATCH CSR.  
     
  Address Offset : 0x340  
  Width (bits) : 32  
  Access Type : RW  
  Reset Value : 0x00000000  
  priviliged mode : Machine
* **Verification Goals**
  
  Read MSCRATCH CSR to check default POR value that should be equal to 0x00000000.
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Directed SelfChk
* **Coverage Method:** N/A
* **Applicable Cores:** CV32A6_v0.1.0
* **Unique verification tag:** VP_csr-test-ident_F000_S000_I000
* **Link to Coverage:** 
* **Comments**
  
  *(none)*  
  
#### Item: 001

* **Requirement location:** riscv-privileged-20211203
* **Feature Description**
  
  Verifying R/W access of a MSCRATCH CSR by writing random valid data and Read back CSR values to check correctness.
* **Verification Goals**
  
  The read values of MSCRATCH CSR should matches with written random data values.
* **Pass/Fail Criteria:** NDY (Not Defined Yet)
* **Test Type:** NDY (Not Defined Yet)
* **Coverage Method:** NDY (Not Defined Yet)
* **Applicable Cores:** CV32A6_v0.1.0
* **Unique verification tag:** VP_csr-test-ident_F000_S000_I001
* **Link to Coverage:** 
* **Comments**
  
  *(none)*  
  

- The agent is developed referring to the Spec in the link below:
  - https://github.com/openhwgroup/core-v-xif/blob/43dc03563e0c79cc55922f653406a9f122f61e80/docs/source/x_ext.rst

- cvxif_pkg.sv is a package, in the core directory, where the cvxif interface signals are described.
  So, to be able to use the cvxif agent you need to have this package.

- Instructions supported by the agent:
  - CUS-ADD     : does rs1 + rs2, and writeback the result.
  - CUS-ADD-RS3 : if X_NUM_RS==3, it does rs1 + rs2 + rs3 else it does rs1 + rs2, and writeback the result.
  - CUS-NOP     : does nothing on CPU side, cus-nop doesn't require a writeback.
  - CUS-M-ADD   : does RISC-V ADD if CPU is in Machine mode else illegal instruction.
  - CUS-S-ADD   : does RISC-V ADD if CPU is in Supervisor or Machine mode else illegal instruction.
  - CUS-ADD-MULT: does a multi-cycle RISCV ADD.
  - CUS-EXC     : does nothing but raises an exception in the coprocessor (result.exc=1).
  - CUS-NOP-EXC : does nothing but informe that the copro can have an exception (issue_resp.exc=1).
  - CUS-ISS-EXC : does nothing but raises an exception in the coprocessor, after signaling via issue_resp the possibility to have the exception.
Note: This custom XIF Instructions are used to test different functionalities of the interface itself (used just for test; they are not specific for a coprocessor).

- Issue response:
  - the issue response of each instruction is generated in the sequence (uvma_cvxif_seq.sv).
  - issue response is driven at the same clk cycle as the issue request

- Result response:
  - the agent drives the result response one clk cycle after the issue request
  - the result response is generated in uvma_cvxif_seq.sv

- Test example for CVA6:
  - in cva6/tests/custom/cv_xif example of tests that offload the different custom xif instructions described above.
  - to execute a test, use testlist_cvxif.yaml

- Functional coverage is supported, the coverage of some scenarios are measured with assertion coverage,
  and the toggle of some signals are measured in covergroups (at uvma_cvxif_cov_model_c component).

- Compressed Interface, Memory Interface and Memory Result Interface are not supported.

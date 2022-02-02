- The agent is developed referring to the Spec in the link below:
  - https://github.com/openhwgroup/core-v-xif/blob/43dc03563e0c79cc55922f653406a9f122f61e80/docs/source/x_ext.rst

- cvxif_pkg.sv is a package, in the core directory, where the cvxif interface signals are described.
  So, to be able to use the cvxif agent you need to have this package.

- Instructions supported by the agent:
  - CUS-ADD: does rs1 + rs2, and writeback the result
  - CUS-ADD-RS3: if X_NUM_RS==3, it does rs1 + rs2 + rs3 else it does rs1 + rs2, and writeback the result

- Issue response:
  - agent's issue response of each instruction is described in instr_pkg.sv
  - issue response is driven at the same clk cycle as the issue request

- Result response:
  - the agent drives the result response one clk cycle after the issue request
  - the result response is generated in uvma_cvxif_seq.sv
  - synchronous exception is not generated

- Test example for CVA6:
  - cvxif.S offloads CUS-ADD, CUS-ADD-RS3 and an illegal instruction in a row
  - to execute the test, use testlist_cvxif.yaml

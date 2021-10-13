# OpenHW Group Phyiscal Memory Attribution agent for OpenHW Group CORE-V verification testbenches


# About
This package contains the OpenHW Group Physical Memory Attribution (PMA)() agent for OpenHW Group CORE-V verification testbenches

This is a passive-only agent that provides common functionality for all CORE-V cores that implement a Physical Memory Attribution
functionality in the core.  The agent will read the PMA configuration from the common CORE Control Configuration agent (lib/uvm_agents/uvma_core_cntrl).
Note that this agent does not implement a signal-based interface although the context class is still defined to satisfy base clasess in the CORE-V environment.
This agent is fed by OBI and RVFI analysis ports to report the transactions emitted by the core.

The Agent provides these components:
* `Monitor` - Decodes incoming OBI data and instruction transactions to map to PMA regions
* `Coverage Model` - Multiple classes provide a full functional coverage model for all possible PMA regions, including default and deconfigured mapping
* `Scoreboard` - Implements checking of PMA policies against OBI transactions and attributes

# Block Diagram
![alt text](./docs/agent_block_diagram.png "Memory attribution agent for OpenHW Group CORE-V verification testbenches UVM Agent Block Diagram")

TBD

# Directory Structure
* `bin` - Scripts, metadata and other miscellaneous files
* `docs` - Documents describing the OpenHW Group Memory attribution agent for OpenHW Group CORE-V verification testbenches UVM Agent
* `examples` - Samples for users
* `src` - Source code for this package


# Dependencies
It is dependent on the following packages:

* `uvm_pkg`
* `uvml_hrtbt_pkg`
* `uvml_trn_pkg`
* `uvml_logs_pkg`
* `uvma_core_cntrl_pkg`
* `uvma_obi_memory_pkg`
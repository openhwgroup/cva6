// Author: Florian Zaruba, ETH Zurich
// Date: 12/20/2016
// Description: Contains the environment for pure alu verification (functional unit interface)

package instr_cache_env_pkg;
    // Standard UVM import & include:
    import uvm_pkg::*;
    `include "uvm_macros.svh"
    // Testbench related imports
    import fu_if_agent_pkg::*;
    // Includes for the config for the environment
    `include "alu_env_config.svh"
    // Includes the environment
    `include "alu_env.svh"
endpackage
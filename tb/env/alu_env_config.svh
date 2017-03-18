// Author: Florian Zaruba, ETH Zurich
// Date: 12/20/2016
// Description: Configuration file for the pure instruction cache environment

class alu_env_config extends uvm_object;

    // UVM Factory Registration Macro
    `uvm_object_utils(alu_env_config)

    // Instruction cache master interface can currently either be

    // a functional unit master interface
    fu_if_agent_config m_fu_if;

endclass : alu_env_config
// Author: Florian Zaruba, ETH Zurich
// Date: 12/21/2016
// Description: Instruction cache main verification environment

class alu_env extends uvm_env;

    // UVM Factory Registration Macro
    `uvm_component_utils(alu_env)

    //------------------------------------------
    // Data Members
    //------------------------------------------
    fu_if_agent m_fu_if_agent;
    fu_if_sequencer m_fu_if_sequencer;
    alu_env_config m_cfg;

    //------------------------------------------
    // Methods
    //------------------------------------------

    // Standard UVM Methods:
    extern function new(string name = "alu_env", uvm_component parent = null);
    extern function void build_phase(uvm_phase phase);
    extern function void connect_phase(uvm_phase phase);

endclass : alu_env

function alu_env::new(string name = "alu_env", uvm_component parent = null);
  super.new(name, parent);
endfunction

function void alu_env::build_phase(uvm_phase phase);
    if (!uvm_config_db #(alu_env_config)::get(this, "", "alu_env_config", m_cfg))
        `uvm_fatal("CONFIG_LOAD", "Cannot get() configuration alu_env_config from uvm_config_db. Have you set() it?")
    // Conditional instantiation goes here

    // Create agent configuratio
    uvm_config_db #(fu_if_agent_config)::set(this, "m_fu_if_agent*",
                                           "fu_if_agent_config",
                                           m_cfg.m_fu_if_agent_config);
    m_fu_if_agent = fu_if_agent::type_id::create("m_fu_if_agent", this);

    // Get sequencer
    m_fu_if_sequencer = fu_if_sequencer::type_id::create("m_fu_if_sequencer", this);

endfunction:build_phase

function void alu_env::connect_phase(uvm_phase phase);
   m_fu_if_sequencer = m_fu_if_agent.m_sequencer;

endfunction: connect_phase

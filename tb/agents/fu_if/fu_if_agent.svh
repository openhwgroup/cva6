// Author: Florian Zaruba, ETH Zurich
// Date: 12/20/2016
// Description: This is the main memory interface agent.
class fu_if_agent extends uvm_component;
    // UVM Factory Registration Macro
    `uvm_component_utils(fu_if_agent)
    //------------------------------------------
    // Data Members
    //------------------------------------------
    fu_if_agent_config m_cfg;
    //------------------------------------------
    // Component Members
    //------------------------------------------
    //------------------------------------------
    // Methods
    //------------------------------------------
    // Standard UVM Methods:
    extern function new(string name = "fu_if_agent", uvm_component parent = null);
    extern function void build_phase(uvm_phase phase);
    extern function void connect_phase(uvm_phase phase);
endclass : fu_if_agent
function fu_if_agent::new(string name = "fu_if_agent", uvm_component parent = null);
    super.new(name, parent);
endfunction : new
function void fu_if_agent::build_phase(uvm_phase phase);
    if (!uvm_config_db #(fu_if_agent_config)::get(this, "", "fu_if_agent_config", m_cfg) )
     `uvm_fatal("CONFIG_LOAD", "Cannot get() configuration apb_agent_config from uvm_config_db. Have you set() it?")
    if (m_cfg.is_master)
        `uvm_info("CONFIG_LOAD", "Created master memory interface", UVM_LOW)
    else
        `uvm_info("CONFIG_LOAD", "Created slave memory interface", UVM_LOW)
endfunction : build_phase
function void fu_if_agent::connect_phase(uvm_phase phase);
    super.connect_phase(phase);
endfunction: connect_phase
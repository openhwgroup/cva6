// Author: Florian Zaruba, ETH Zurich
// Date: 12/21/2016
// Description: Driver of the memory interface

class fu_if_driver extends uvm_driver #(sequence_item);

    // UVM Factory Registration Macro
    `uvm_component_utils(fu_if_driver)

    // Virtual Interface
    virtual fu_if fu;

    //---------------------
    // Data Members
    //---------------------
    fu_if_agent_config m_cfg;

    // Standard UVM Methods:
    extern function new(string name = "fu_if_driver", uvm_component parent = null);
    extern task run_phase(uvm_phase phase);
    extern function void build_phase(uvm_phase phase);


endclass : fu_if_driver

function fu_if_driver::new(string name = "fu_if_driver", uvm_component parent = null);
  super.new(name, parent);
endfunction

task fu_if_driver::run_phase(uvm_phase phase);
    sequence_item cmd;

    forever begin : cmd_loop
        shortint unsigned result;
        seq_item_port.get_next_item(cmd);

        // using clocking blocks this is possible
        @(fu.mck)
        fu.mclk.operandA <= cmd.operandA;
        fu.mclk.operandB <= cmd.operandB;
        fu.mclk.operandC <= cmd.operandC;
        fu.mclk.operator <= cmd.operator;

        cmd.result <= fu.mclk.result;
        cmd.compare_result <= fu.mclk.compare_result;

        seq_item_port.item_done();

    end : cmd_loop
endtask : run_phase

function void fu_if_driver::build_phase(uvm_phase phase);
  if (!uvm_config_db #(fu_if_agent_config)::get(this, "", "fu_if_agent_config", m_cfg) )
     `uvm_fatal("CONFIG_LOAD", "Cannot get() configuration fu_if_agent_config from uvm_config_db. Have you set() it?")
endfunction: build_phase
// Author: Florian Zaruba, ETH Zurich
// Date: 12/21/2016
// Description: Driver of the memory interface
//
// Copyright (C) 2017 ETH Zurich, University of Bologna
// All rights reserved.

class fu_if_monitor extends uvm_component;

    // UVM Factory Registration Macro
    `uvm_component_utils(fu_if_monitor)

    // analysis port
    uvm_analysis_port #(fu_if_seq_item) ap;

    // Virtual Interface
    virtual fu_if fu;

    //---------------------
    // Data Members
    //---------------------
    fu_if_agent_config m_cfg;

    // Standard UVM Methods:
    function new(string name = "fu_if_driver", uvm_component parent = null);
      super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
      if (!uvm_config_db #(fu_if_agent_config)::get(this, "", "fu_if_agent_config", m_cfg) )
         `uvm_fatal("CONFIG_LOAD", "Cannot get() configuration fu_if_agent_config from uvm_config_db. Have you set() it?")

        ap = new("ap", this);

    endfunction: build_phase

    function void connect_phase(uvm_phase phase);
        // connect virtual interface
        fu = m_cfg.fu;
    endfunction

    task run_phase(uvm_phase phase);

	fu_if_seq_item cmd =  fu_if_seq_item::type_id::create("cmd");
	fu_if_seq_item cloned_item;

        forever begin : cmd_loop
            longint result;

            cmd.operator  = fu.pck.operator;
            cmd.operand_a = fu.pck.operand_a;
            cmd.operand_b = fu.pck.operand_b;
            cmd.operand_c = fu.pck.operand_c;
            cmd.result    = fu.pck.result;

            @(fu.pck)

            $cast(cloned_item, cmd.clone());
            ap.write(cloned_item);

        end : cmd_loop
    endtask : run_phase
endclass : fu_if_monitor

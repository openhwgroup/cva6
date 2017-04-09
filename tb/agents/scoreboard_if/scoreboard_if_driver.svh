// Author: Florian Zaruba, ETH Zurich
// Date: 12/21/2016
// Description: Driver of the memory interface
//
// Copyright (C) 2017 ETH Zurich, University of Bologna
// All rights reserved.

class scoreboard_if_driver extends uvm_driver #(scoreboard_if_seq_item);

    // UVM Factory Registration Macro
    `uvm_component_utils(scoreboard_if_driver)

    // Virtual Interface
    virtual scoreboard_if scoreboard;

    //---------------------
    // Data Members
    //---------------------
    scoreboard_if_agent_config m_cfg;

    // Standard UVM Methods:
    function new(string name = "scoreboard_if_driver", uvm_component parent = null);
      super.new(name, parent);
    endfunction

    task run_phase(uvm_phase phase);
        scoreboard_if_seq_item cmd;

    endtask : run_phase

    function void build_phase(uvm_phase phase);
      if (!uvm_config_db #(scoreboard_if_agent_config)::get(this, "", "scoreboard_if_agent_config", m_cfg) )
         `uvm_fatal("CONFIG_LOAD", "Cannot get() configuration scoreboard_if_agent_config from uvm_config_db. Have you set() it?")

      scoreboard = m_cfg.scoreboard;
    endfunction: build_phase
endclass : scoreboard_if_driver
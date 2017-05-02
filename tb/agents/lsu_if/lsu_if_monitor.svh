// Author: Florian Zaruba, ETH Zurich
// Date: 02.05.2017
// Description: lsu_if Monitor, monitors the DUT's pins and writes out
//              appropriate sequence items as defined for this particular dut
//
// Copyright (C) 2017 ETH Zurich, University of Bologna
// All rights reserved.
// This code is under development and not yet released to the public.
// Until it is released, the code is under the copyright of ETH Zurich and
// the University of Bologna, and may contain confidential and/or unpublished
// work. Any reuse/redistribution is strictly forbidden without written
// permission from ETH Zurich.
// Bug fixes and contributions will eventually be released under the
// SolderPad open hardware license in the context of the PULP platform
// (http://www.pulp-platform.org), under the copyright of ETH Zurich and the
// University of Bologna.

class lsu_if_monitor extends uvm_component;

    // UVM Factory Registration Macro
    `uvm_component_utils(lsu_if_monitor)

    // analysis port
    uvm_analysis_port #(lsu_if_seq_item) m_ap;

    // Virtual Interface
    virtual lsu_if fu;

    //---------------------
    // Data Members
    //---------------------
    lsu_if_agent_config m_cfg;

    // Standard UVM Methods:
    function new(string name = "lsu_if_driver", uvm_component parent = null);
      super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
      if (!uvm_config_db #(lsu_if_agent_config)::get(this, "", "lsu_if_agent_config", m_cfg) )
         `uvm_fatal("CONFIG_LOAD", "Cannot get() configuration lsu_if_agent_config from uvm_config_db. Have you set() it?")

        m_ap = new("m_ap", this);

    endfunction: build_phase

    function void connect_phase(uvm_phase phase);
        // connect virtual interface
        fu = m_cfg.fu;
    endfunction

    task run_phase(uvm_phase phase);

    	lsu_if_seq_item cmd =  lsu_if_seq_item::type_id::create("cmd");
    	lsu_if_seq_item cloned_item;


        $cast(cloned_item, cmd.clone());
        m_ap.write(cloned_item);

    endtask : run_phase
endclass : lsu_if_monitor

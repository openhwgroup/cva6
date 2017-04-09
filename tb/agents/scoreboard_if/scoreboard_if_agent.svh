// Author: Florian Zaruba, ETH Zurich
// Date: 12/20/2016
// Description: This is the main memory interface agent.
//
// Copyright (C) 2017 ETH Zurich, University of Bologna
// All rights reserved.
class scoreboard_if_agent extends uvm_component;
    // UVM Factory Registration Macro
    `uvm_component_utils(scoreboard_if_agent)
    //------------------------------------------
    // Data Members
    //------------------------------------------
    scoreboard_if_agent_config m_cfg;
    //------------------------------------------
    // Component Members
    //------------------------------------------
    uvm_analysis_port #(scoreboard_if_seq_item) ap;
    scoreboard_if_driver m_driver;
    scoreboard_if_monitor m_monitor;
    scoreboard_if_sequencer m_sequencer;
    //------------------------------------------
    // Methods
    //------------------------------------------
    // Standard UVM Methods:
    function new(string name = "scoreboard_if_agent", uvm_component parent = null);
        super.new(name, parent);
    endfunction : new

    function void build_phase(uvm_phase phase);
        if (!uvm_config_db #(scoreboard_if_agent_config)::get(this, "", "scoreboard_if_agent_config", m_cfg) )
         `uvm_fatal("CONFIG_LOAD", "Cannot get() configuration scoreboard_agent_config from uvm_config_db. Have you set() it?")

        m_driver = scoreboard_if_driver::type_id::create("m_driver", this);
        m_sequencer = scoreboard_if_sequencer::type_id::create("m_sequencer", this);
        m_monitor = scoreboard_if_monitor::type_id::create("m_monitor", this);
    endfunction : build_phase

    function void connect_phase(uvm_phase phase);

        m_driver.seq_item_port.connect(m_sequencer.seq_item_export);
        // m_monitor.ap.connect(m_cov_monitor.analysis_port)
        m_driver.m_cfg = m_cfg;
        m_monitor.m_cfg = m_cfg;

    endfunction: connect_phase
endclass : scoreboard_if_agent

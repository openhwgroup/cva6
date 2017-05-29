// Author: Florian Zaruba, ETH Zurich
// Date: 29.05.2017
// Description: Main agent object dcache_if. Builds and instantiates the appropriate
//              subcomponents like the monitor, driver etc. all based on the
//              agent configuration object.
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

class dcache_if_agent extends uvm_component;
    // UVM Factory Registration Macro
    `uvm_component_utils(dcache_if_agent)
    //------------------------------------------
    // Data Members
    //------------------------------------------
    dcache_if_agent_config m_cfg;
    //------------------------------------------
    // Component Members
    //------------------------------------------
    uvm_analysis_port #(dcache_if_seq_item) ap;
    dcache_if_driver m_driver;
    dcache_if_monitor m_monitor;
    dcache_if_sequencer m_sequencer;
    //------------------------------------------
    // Methods
    //------------------------------------------
    // Standard UVM Methods:
    function new(string name = "dcache_if_agent", uvm_component parent = null);
        super.new(name, parent);
    endfunction : new

    function void build_phase(uvm_phase phase);

        if (!uvm_config_db #(dcache_if_agent_config)::get(this, "", "dcache_if_agent_config", m_cfg) )
         `uvm_fatal("CONFIG_LOAD", "Cannot get() configuration dcache_if_agent_config from uvm_config_db. Have you set() it?")

        m_driver = dcache_if_driver::type_id::create("m_driver", this);
        m_sequencer = dcache_if_sequencer::type_id::create("m_sequencer", this);
        m_monitor = dcache_if_monitor::type_id::create("m_monitor", this);
    endfunction : build_phase

    function void connect_phase(uvm_phase phase);

        m_driver.seq_item_port.connect(m_sequencer.seq_item_export);
        // m_monitor.ap.connect(m_cov_monitor.analysis_port)
        m_driver.m_cfg = m_cfg;
        m_monitor.m_cfg = m_cfg;

    endfunction: connect_phase
endclass : dcache_if_agent

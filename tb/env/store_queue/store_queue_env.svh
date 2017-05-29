// Author: Florian Zaruba, ETH Zurich
// Date: 29.05.2017
// Description: Environment which instantiates the agent and all environment
//              related components such as a scoreboard etc.
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

class store_queue_env extends uvm_env;

    // UVM Factory Registration Macro
    `uvm_component_utils(store_queue_env)

    //------------------------------------------
    // Data Members
    //------------------------------------------
    store_queue_if_agent m_store_queue_if_agent;
    store_queue_if_sequencer m_store_queue_if_sequencer;
    store_queue_env_config m_cfg;
    //------------------------------------------
    // Methods
    //------------------------------------------

    // Standard UVM Methods:
    function new(string name = "store_queue_env", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        if (!uvm_config_db #(store_queue_env_config)::get(this, "", "store_queue_env_config", m_cfg))
            `uvm_fatal("CONFIG_LOAD", "Cannot get() configuration store_queue_env_config from uvm_config_db. Have you set() it?")
        // Conditional instantiation goes here

        // Create agent configuration
        uvm_config_db #(store_queue_if_agent_config)::set(this, "m_store_queue_if_agent*",
                                               "store_queue_if_agent_config",
                                               m_cfg.m_store_queue_if_agent_config);
        m_store_queue_if_agent = store_queue_if_agent::type_id::create("m_store_queue_if_agent", this);

        // Get sequencer
        m_store_queue_if_sequencer = store_queue_if_sequencer::type_id::create("m_store_queue_if_sequencer", this);

    endfunction:build_phase

    function void connect_phase(uvm_phase phase);
        m_store_queue_if_sequencer = m_store_queue_if_agent.m_sequencer;
    endfunction: connect_phase
endclass : store_queue_env

// Author: Florian Zaruba, ETH Zurich
// Date: 29.05.2017
// Description: store_queue base test class
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

class store_queue_test_base extends uvm_test;

    // UVM Factory Registration Macro
    `uvm_component_utils(store_queue_test_base)

    //------------------------------------------
    // Data Members
    //------------------------------------------

    //------------------------------------------
    // Component Members
    //------------------------------------------
    // environment configuration
    store_queue_env_config m_env_cfg;
    // environment
    store_queue_env m_env;
    store_queue_if_sequencer sequencer_h;

    // reset_sequence reset;
    // ---------------------
    // Agent configuration
    // ---------------------
    // functional unit interface
    store_queue_if_agent_config m_store_queue_if_cfg;
    dcache_if_agent_config m_dcache_if_cfg;

    //------------------------------------------
    // Methods
    //------------------------------------------
    // standard UVM methods:
    function new(string name = "store_queue_test_base", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    // build the environment, get all configurations
    // use the factory pattern in order to facilitate UVM functionality
    function void build_phase(uvm_phase phase);
        // create environment
        m_env_cfg = store_queue_env_config::type_id::create("m_env_cfg");

        // create agent configurations and assign interfaces
        // create agent store_queue_if configuration
        m_store_queue_if_cfg = store_queue_if_agent_config::type_id::create("m_store_queue_if_cfg");
        m_env_cfg.m_store_queue_if_agent_config = m_store_queue_if_cfg;

        m_dcache_if_cfg = dcache_if_agent_config::type_id::create("m_dcache_if_cfg");
        m_env_cfg.m_dcache_if_agent_config = m_dcache_if_cfg;

        // get store_queue_if virtual interfaces
        // get master interface DB
        if (!uvm_config_db #(virtual store_queue_if)::get(this, "", "store_queue_if", m_store_queue_if_cfg.m_vif))
            `uvm_fatal("VIF CONFIG", "Cannot get() interface store_queue_if from uvm_config_db. Have you set() it?")
        m_env_cfg.m_store_queue_if = m_store_queue_if_cfg.m_vif;

        if (!uvm_config_db #(virtual dcache_if)::get(this, "", "dcache_if", m_dcache_if_cfg.m_vif))
            `uvm_fatal("VIF CONFIG", "Cannot get() interface dcache_if from uvm_config_db. Have you set() it?")
        m_env_cfg.m_dcache_if = m_dcache_if_cfg.m_vif;
        // configure as SLAVE in replay mode
        m_env_cfg.m_dcache_if_agent_config.dcache_if_config = SLAVE_REPLAY;

        // create environment
        uvm_config_db #(store_queue_env_config)::set(this, "*", "store_queue_env_config", m_env_cfg);
        m_env = store_queue_env::type_id::create("m_env", this);

    endfunction

    function void end_of_elaboration_phase(uvm_phase phase);
        sequencer_h = m_env.m_store_queue_if_sequencer;
    endfunction

    task run_phase(uvm_phase phase);
        // reset = new("reset");
        // reset.start(sequencer_h);
    endtask

endclass : store_queue_test_base
// Author: Florian Zaruba, ETH Zurich
// Date: 30.04.2017
// Description: mem_arbiter base test class
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

class mem_arbiter_test_base extends uvm_test;

    // UVM Factory Registration Macro
    `uvm_component_utils(mem_arbiter_test_base)

    //------------------------------------------
    // Data Members
    //------------------------------------------

    //------------------------------------------
    // Component Members
    //------------------------------------------
    // environment configuration
    mem_arbiter_env_config m_env_cfg;
    // environment
    mem_arbiter_env m_env;
    dcache_if_sequencer sequencer_h[3];

    // reset_sequence reset;
    // ---------------------
    // Agent configuration
    // ---------------------
    // functional unit interface
    dcache_if_agent_config m_cfg_slave;
    dcache_if_agent_config m_cfg_masters[3];

    //------------------------------------------
    // Methods
    //------------------------------------------
    // Standard UVM Methods:
    function new(string name = "mem_arbiter_test_base", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    // Build the environment, get all configurations
    // Use the factory pattern in order to facilitate UVM functionality
    function void build_phase(uvm_phase phase);
        // create environment
        m_env_cfg = mem_arbiter_env_config::type_id::create("m_env_cfg");
        // create agent configurations and assign interfaces
        // create a slave configuration
        m_cfg_slave = dcache_if_agent_config::type_id::create("m_cfg_slave");
        m_env_cfg.m_dcache_if_slave_agent = m_cfg_slave;
        m_env_cfg.m_dcache_if_slave_agent.dcache_if_config = SLAVE_REPLAY;

        // create agent memory master configuration
        m_cfg_masters[0] = dcache_if_agent_config::type_id::create("m_cfg_master0");
        m_env_cfg.m_dcache_if_master_agents[0] = m_cfg_masters[0];
        m_env_cfg.m_dcache_if_master_agents[0].dcache_if_config = MASTER;

        m_cfg_masters[1] = dcache_if_agent_config::type_id::create("m_cfg_master1");
        m_env_cfg.m_dcache_if_master_agents[1] = m_cfg_masters[1];
        m_env_cfg.m_dcache_if_master_agents[1].dcache_if_config = MASTER;

        m_cfg_masters[2] = dcache_if_agent_config::type_id::create("m_cfg_master2");
        m_env_cfg.m_dcache_if_master_agents[2] = m_cfg_masters[2];
        m_env_cfg.m_dcache_if_master_agents[2].dcache_if_config = MASTER;
        // Get Virtual Interfaces
        // get master interface DB
        if (!uvm_config_db #(virtual dcache_if)::get(this, "", "dcache_if_slave", m_cfg_slave.m_vif))
            `uvm_fatal("VIF CONFIG", "Cannot get() interface dcache_if from uvm_config_db. Have you set() it?")
        m_env_cfg.m_dcache_if_slave = m_cfg_slave.m_vif;

        if (!uvm_config_db #(virtual dcache_if)::get(this, "", "dcache_if_master0", m_cfg_masters[0].m_vif))
            `uvm_fatal("VIF CONFIG", "Cannot get() interface dcache_if from uvm_config_db. Have you set() it?")
        m_env_cfg.m_dcache_if_masters[0] = m_cfg_slave.m_vif;

        if (!uvm_config_db #(virtual dcache_if)::get(this, "", "dcache_if_master1", m_cfg_masters[1].m_vif))
            `uvm_fatal("VIF CONFIG", "Cannot get() interface dcache_if from uvm_config_db. Have you set() it?")
        m_env_cfg.m_dcache_if_masters[1] = m_cfg_slave.m_vif;

        if (!uvm_config_db #(virtual dcache_if)::get(this, "", "dcache_if_master2", m_cfg_masters[2].m_vif))
            `uvm_fatal("VIF CONFIG", "Cannot get() interface dcache_if from uvm_config_db. Have you set() it?")
        m_env_cfg.m_dcache_if_masters[2] = m_cfg_slave.m_vif;

        // create environment
        uvm_config_db #(mem_arbiter_env_config)::set(this, "*", "mem_arbiter_env_config", m_env_cfg);
        m_env = mem_arbiter_env::type_id::create("m_env", this);

    endfunction

    function void end_of_elaboration_phase(uvm_phase phase);
        sequencer_h[0] = m_env.m_dcache_if_sequencers[0];
        sequencer_h[1] = m_env.m_dcache_if_sequencers[1];
        sequencer_h[2] = m_env.m_dcache_if_sequencers[2];
    endfunction

    task run_phase(uvm_phase phase);
        // reset = new("reset");
        // reset.start(sequencer_h);
    endtask

endclass : mem_arbiter_test_base
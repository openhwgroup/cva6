// Author: Florian Zaruba, ETH Zurich
// Date: 30.04.2017
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

class mem_arbiter_env extends uvm_env;

    // UVM Factory Registration Macro
    `uvm_component_utils(mem_arbiter_env)

    //------------------------------------------
    // Data Members
    //------------------------------------------
    mem_if_agent m_mem_if_slave_agent;
    mem_if_agent m_mem_if_master_agents[3];

    mem_if_sequencer m_mem_if_sequencers[3];
    mem_arbiter_env_config m_cfg;
    //------------------------------------------
    // Methods
    //------------------------------------------

    // Standard UVM Methods:
    function new(string name = "mem_arbiter_env", uvm_component parent = null);
      super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        if (!uvm_config_db #(mem_arbiter_env_config)::get(this, "", "mem_arbiter_env_config", m_cfg))
            `uvm_fatal("CONFIG_LOAD", "Cannot get() configuration mem_arbiter_env_config from uvm_config_db. Have you set() it?")
        // Conditional instantiation goes here

        // Create agent configurations
        uvm_config_db #(mem_if_agent_config)::set(this, "m_mem_if_slave*",
                                               "mem_if_agent_config",
                                               m_cfg.m_mem_if_slave_agent);

        uvm_config_db #(mem_if_agent_config)::set(this, "m_mem_if_master0*",
                                               "mem_if_agent_config",
                                               m_cfg.m_mem_if_master_agents[0]);

        uvm_config_db #(mem_if_agent_config)::set(this, "m_mem_if_master1*",
                                               "mem_if_agent_config",
                                               m_cfg.m_mem_if_master_agents[1]);

        uvm_config_db #(mem_if_agent_config)::set(this, "m_mem_if_master2*",
                                               "mem_if_agent_config",
                                               m_cfg.m_mem_if_master_agents[2]);

        m_mem_if_slave_agent = mem_if_agent::type_id::create("m_mem_if_slave_agent", this);

        // create 3 master memory interfaces
        m_mem_if_master_agents[0] = mem_if_agent::type_id::create("m_mem_if_master0_agent", this);
        m_mem_if_master_agents[1] = mem_if_agent::type_id::create("m_mem_if_master1_agent", this);
        m_mem_if_master_agents[2] = mem_if_agent::type_id::create("m_mem_if_master2_agent", this);

        // Get 3 sequencers
        m_mem_if_sequencers[0] = mem_if_sequencer::type_id::create("m_mem_if_sequencer0", this);
        m_mem_if_sequencers[1] = mem_if_sequencer::type_id::create("m_mem_if_sequencer1", this);
        m_mem_if_sequencers[2] = mem_if_sequencer::type_id::create("m_mem_if_sequencer2", this);

    endfunction:build_phase

    function void connect_phase(uvm_phase phase);
       m_mem_if_sequencers[0] = m_mem_if_master_agents[0].m_sequencer;
       m_mem_if_sequencers[1] = m_mem_if_master_agents[1].m_sequencer;
       m_mem_if_sequencers[2] = m_mem_if_master_agents[2].m_sequencer;
    endfunction: connect_phase
endclass : mem_arbiter_env

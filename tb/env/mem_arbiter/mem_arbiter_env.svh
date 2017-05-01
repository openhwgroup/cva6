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

    mem_arbiter_scoreboard m_scoreboard;
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


        m_mem_if_slave_agent = mem_if_agent::type_id::create("m_mem_if_slave_agent", this);

        // create 3 master memory interfaces
        for (int i = 0; i < 3; i++) begin
            uvm_config_db #(mem_if_agent_config)::set(this, {"m_mem_if_master", i, "*"},
                                       "mem_if_agent_config",
                                       m_cfg.m_mem_if_master_agents[i]);

            m_mem_if_master_agents[i] = mem_if_agent::type_id::create({"m_mem_if_master", i, "_agent"}, this);
            // Get 3 sequencers
            m_mem_if_sequencers[i] = mem_if_sequencer::type_id::create({"m_mem_if_sequencer", i}, this);
        end
        // instantiate the scoreboard
        m_scoreboard = mem_arbiter_scoreboard::type_id::create("m_scoreboard", this);
    endfunction:build_phase

    function void connect_phase(uvm_phase phase);
        // connect the sequencers and monitor to the master agents
        for (int i = 0; i < 3; i++) begin
            m_mem_if_sequencers[i] = m_mem_if_master_agents[i].m_sequencer;
            m_mem_if_master_agents[i].m_monitor.m_ap.connect(m_scoreboard.item_export);
        end
        // connect the slave monitor to the scoreboard
        m_mem_if_slave_agent.m_monitor.m_ap.connect(m_scoreboard.item_export);
    endfunction: connect_phase
endclass : mem_arbiter_env

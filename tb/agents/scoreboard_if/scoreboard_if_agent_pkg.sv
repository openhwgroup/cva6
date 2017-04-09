// Author: Florian Zaruba, ETH Zurich
// Date: 12/20/2016
// Description: Encapsulates the whole memory agent into one package by including
//              all the necessary files.
//
// Copyright (C) 2017 ETH Zurich, University of Bologna
// All rights reserved.

package scoreboard_if_agent_pkg;
    // UVM Import
    import uvm_pkg::*;
    import ariane_pkg::*;
    `include "uvm_macros.svh"

    // Sequence item to model transactions
    `include "scoreboard_if_seq_item.svh"
    // Agent configuration object
    `include "scoreboard_if_agent_config.svh"
    // Driver
    `include "scoreboard_if_driver.svh"
    // Coverage monitor
    // `include "scoreboard_if_coverage_monitor.svh"
    // Monitor that includes analysis port
    `include "scoreboard_if_monitor.svh"
    // Sequencer
    `include "scoreboard_if_sequencer.svh"
    // Main agent
    `include "scoreboard_if_agent.svh"
    // Sequence
    `include "scoreboard_if_seq.svh"
endpackage: scoreboard_if_agent_pkg

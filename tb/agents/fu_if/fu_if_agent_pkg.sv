// Author: Florian Zaruba, ETH Zurich
// Date: 12/20/2016
// Description: Encapsulates the whole memory agent into one package by including
//              all the necessary files.
//
// Copyright (C) 2017 ETH Zurich, University of Bologna
// All rights reserved.

package fu_if_agent_pkg;
    // UVM Import
    import uvm_pkg::*;
    `include "uvm_macros.svh"

    // Sequence item to model transactions
    `include "fu_if_seq_item.svh"
    // Agent configuration object
    `include "fu_if_agent_config.svh"
    // Driver
    `include "fu_if_driver.svh"
    // Coverage monitor
    // `include "fu_if_coverage_monitor.svh"
    // Monitor that includes analysis port
    `include "fu_if_monitor.svh"
    // Sequencer
    `include "fu_if_sequencer.svh"
    // Main agent
    `include "fu_if_agent.svh"
    // Sequence
    `include "fu_if_seq.svh"
endpackage: fu_if_agent_pkg
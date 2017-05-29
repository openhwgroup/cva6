// Author: Florian Zaruba, ETH Zurich
// Date: 29.05.2017
// Description: store_queue_if_agent package - compile unit
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

package store_queue_if_agent_pkg;
    // UVM Import
    import uvm_pkg::*;
    `include "uvm_macros.svh"

    // Sequence item to model transactions
    `include "store_queue_if_seq_item.svh"
    // Agent configuration object
    `include "store_queue_if_agent_config.svh"
    // Driver
    `include "store_queue_if_driver.svh"
    // Coverage monitor
    // `include "store_queue_if_coverage_monitor.svh"
    // Monitor that includes analysis port
    `include "store_queue_if_monitor.svh"
    // Sequencer
    `include "store_queue_if_sequencer.svh"
    // Main agent
    `include "store_queue_if_agent.svh"
    // Sequence
    `include "store_queue_if_sequence.svh"
endpackage: store_queue_if_agent_pkg
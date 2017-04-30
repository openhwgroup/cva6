// Author: Florian Zaruba, ETH Zurich
// Date: 30.04.2017
// Description: mem_if_agent package - compile unit
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

package mem_if_agent_pkg;
    typedef enum {
        SLAVE, MASTER
    } mem_if_config;
    // Mode of request either read or write
    typedef enum {
        READ, WRITE
    } mode_t;

    // UVM Import
    import uvm_pkg::*;
    `include "uvm_macros.svh"

    // Sequence item to model transactions
    `include "mem_if_seq_item.svh"
    // Agent configuration object
    `include "mem_if_agent_config.svh"
    // Driver
    `include "mem_if_driver.svh"
    // Coverage monitor
    // `include "mem_if_coverage_monitor.svh"
    // Monitor that includes analysis port
    `include "mem_if_monitor.svh"
    // Sequencer
    `include "mem_if_sequencer.svh"
    // Main agent
    `include "mem_if_agent.svh"
    // Sequence
    `include "mem_if_sequence.svh"
endpackage: mem_if_agent_pkg
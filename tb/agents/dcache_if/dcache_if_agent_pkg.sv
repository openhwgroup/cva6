// Author: Florian Zaruba, ETH Zurich
// Date: 29.05.2017
// Description: dcache_if_agent package - compile unit
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

package dcache_if_agent_pkg;
    // configure the slave memory interface
    // 1. either as a slave with random grant response
    // 2. as a master interface making random data requests
    // 3. as a slave with no grant randomization
    // 4. replay data
    typedef enum {
        SLAVE, SLAVE_REPLAY, SLAVE_NO_RANDOM, MASTER
    } dcache_if_config_t;

    // Mode of request either read or write
    typedef enum {
        READ, WRITE
    } mode_t;

    // UVM Import
    import uvm_pkg::*;
    `include "uvm_macros.svh"

    // Sequence item to model transactions
    `include "dcache_if_seq_item.svh"
    // Agent configuration object
    `include "dcache_if_agent_config.svh"
    // Driver
    `include "dcache_if_driver.svh"
    // Coverage monitor
    // `include "dcache_if_coverage_monitor.svh"
    // Monitor that includes analysis port
    `include "dcache_if_monitor.svh"
    // Sequencer
    `include "dcache_if_sequencer.svh"
    // Main agent
    `include "dcache_if_agent.svh"
    // Sequence
    `include "dcache_if_sequence.svh"
endpackage: dcache_if_agent_pkg
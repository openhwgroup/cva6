// Author: Florian Zaruba, ETH Zurich
// Date: 02.05.2017
// Description: lsu_if_agent package - compile unit
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

package lsu_if_agent_pkg;
    // UVM Import
    import uvm_pkg::*;
    // import the ariane package for the various data-types
    import ariane_pkg::*;

    `include "uvm_macros.svh"

    // Sequence item to model transactions
    `include "lsu_if_seq_item.svh"
    // Agent configuration object
    `include "lsu_if_agent_config.svh"
    // Driver
    `include "lsu_if_driver.svh"
    // Coverage monitor
    // `include "lsu_if_coverage_monitor.svh"
    // Monitor that includes analysis port
    `include "lsu_if_monitor.svh"
    // Sequencer
    `include "lsu_if_sequencer.svh"
    // Main agent
    `include "lsu_if_agent.svh"
    // Sequence
    `include "lsu_if_sequence.svh"
endpackage: lsu_if_agent_pkg
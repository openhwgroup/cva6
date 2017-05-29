// Author: Florian Zaruba, ETH Zurich
// Date: 29.05.2017
// Description: store_queue_if Sequencer for store_queue_if_sequence_item
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

class store_queue_if_sequencer extends uvm_sequencer #(store_queue_if_seq_item);

    // UVM Factory Registration Macro
    `uvm_component_utils(store_queue_if_sequencer)

    // Standard UVM Methods:
    function new(string name="store_queue_if_sequencer", uvm_component parent = null);
        super.new(name, parent);
    endfunction

endclass: store_queue_if_sequencer



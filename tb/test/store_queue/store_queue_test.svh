// Author: Florian Zaruba, ETH Zurich
// Date: 29.05.2017
// Description: store_queue main test class
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

class store_queue_test extends store_queue_test_base;
    // UVM Factory Registration Macro
    `uvm_component_utils(store_queue_test)
    store_queue_sequence store_queue;
    //------------------------------------------
    // Methods
    //------------------------------------------

    // Standard UVM Methods:
    function new(string name = "store_queue_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
    endfunction

    task run_phase(uvm_phase phase);
        phase.raise_objection(this, "store_queue_test");
        super.run_phase(phase);

        store_queue = new("store_queue");
        // Start sequence here
        store_queue.start(sequencer_h);
        #100ns;

        phase.drop_objection(this, "store_queue_test");
    endtask


endclass : store_queue_test

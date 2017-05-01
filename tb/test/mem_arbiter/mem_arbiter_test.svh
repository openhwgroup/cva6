// Author: Florian Zaruba, ETH Zurich
// Date: 30.04.2017
// Description: mem_arbiter main test class
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

class mem_arbiter_test extends mem_arbiter_test_base;
    // UVM Factory Registration Macro
    `uvm_component_utils(mem_arbiter_test)
    mem_arbiter_sequence mem_arbiter_sequences[3];
    //------------------------------------------
    // Methods
    //------------------------------------------

    // Standard UVM Methods:
    function new(string name = "mem_arbiter_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
    endfunction

    // start the sequencer with number sequencer
    task start_sequence(int sequencer);
        mem_arbiter_sequences[sequencer] = new({"mem_arbiter_sequences", sequencer});
        mem_arbiter_sequences[sequencer].start(sequencer_h[sequencer]);
    endtask

    task run_phase(uvm_phase phase);
        uvm_objection objection;
        phase.raise_objection(this, "mem_arbiter_test");
        #200ns;
        super.run_phase(phase);
        // fork three sequencers and wait for all of them to finish
        // until dropping the objection again
        fork
            start_sequence(0);
            start_sequence(1);
            start_sequence(2);
        join
        // Testlogic goes here
        // drain time until the objection gets dropped
        objection = phase.get_objection();
        objection.set_drain_time(this, 100ns );
        phase.drop_objection(this, "mem_arbiter_test");
    endtask


endclass : mem_arbiter_test

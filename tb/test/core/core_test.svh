// Author: Florian Zaruba, ETH Zurich
// Date: 08.05.2017
// Description: core main test class
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

class core_test extends core_test_base;
    // UVM Factory Registration Macro
    `uvm_component_utils(core_test)
    // TODO: declare sequence here
    // core_sequence core;
    //------------------------------------------
    // Methods
    //------------------------------------------

    // Standard UVM Methods:
    function new(string name = "core_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
    endfunction

    task run_phase(uvm_phase phase);
        phase.raise_objection(this, "core_test");
        //fibonacci_sequence fibonacci;
        super.run_phase(phase);

        // core = new("core");
        // TODO: Start sequence here
        // core.start(sequencer_h);
        // Testlogic goes here
        #100ns;

        phase.drop_objection(this, "core_test");
    endtask


endclass : core_test

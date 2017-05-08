// Author: Florian Zaruba, ETH Zurich
// Date: 08.05.2017
// Description: Core test sequence - simply waits for now
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

class core_sequence extends core_if_sequence;

    `uvm_object_utils(core_sequence);

    function new(string name = "core_sequence");
       super.new(name);
    endfunction : new

    task body();
        core_if_seq_item command;

        command = core_if_seq_item::type_id::create("command");
        `uvm_info("Core Sequence", "Starting Core Test", UVM_LOW)

        for(int i = 0; i <= 100; i++) begin
            start_item(command);

            void'(command.randomize());

            finish_item(command);
        end
        `uvm_info("Core Sequence", "Finished Core Test", UVM_LOW)
    endtask : body
endclass : core_sequence

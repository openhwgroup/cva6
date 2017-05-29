// Author: Florian Zaruba, ETH Zurich
// Date: 01.05.2017
// Description: Randomized test sequence
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

class mem_arbiter_sequence extends dcache_if_sequence;

   `uvm_object_utils(mem_arbiter_sequence);

   function new(string name = "mem_arbiter_sequence");
      super.new(name);
   endfunction : new

   task body();
      dcache_if_seq_item command;

      command = dcache_if_seq_item::type_id::create("command");
      `uvm_info("DCache Arbiter Sequence", "Starting mem_arbiter sequence", UVM_LOW)

      for(int i = 0; i <= 100; i++) begin
          start_item(command);

          void'(command.randomize());

          finish_item(command);
      end
      `uvm_info("DCache Arbiter Sequence", "Finished mem_arbiter sequence", UVM_LOW)
   endtask : body
endclass : mem_arbiter_sequence

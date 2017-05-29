// Author: Florian Zaruba, ETH Zurich
// Date: 29.05.2017
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

class store_queue_sequence  extends store_queue_if_sequence;

   `uvm_object_utils(store_queue_sequence);

   function new(string name = "store_queue_sequence");
      super.new(name);
   endfunction : new

   task body();
      store_queue_if_seq_item command;

      command = store_queue_if_seq_item::type_id::create("command");
      `uvm_info("Store Queue Sequence", "Starting store_queue sequence", UVM_LOW)

      for(int i = 0; i <= 100; i++) begin
          start_item(command);

          void'(command.randomize());

          finish_item(command);
      end
      `uvm_info("Store Queue Sequence", "Finished store_queue sequence", UVM_LOW)
   endtask : body

endclass : store_queue_sequence
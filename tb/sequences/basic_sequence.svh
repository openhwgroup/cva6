// Author: Florian Zaruba, ETH Zurich
// Date: 09/04/2017
// Description: Basic sequence, all other ALU sequences extend this abstract class
//
// Copyright (C) 2017 ETH Zurich, University of Bologna
// All rights reserved.

virtual class basic_sequence extends fu_if_seq;

   `uvm_object_utils(basic_sequence);

   function new(string name = "basic");
      super.new(name);
   endfunction : new

   pure virtual function fu_op get_operator();

   task body();
      fu_if_seq_item command;

      command = fu_if_seq_item::type_id::create("command");
      `uvm_info("ALU Sequence", $sformatf("Starting %s sequence", get_operator().name), UVM_LOW)

      for(int i = 0; i <= 100; i++) begin
          start_item(command);

          void'(command.randomize());
          command.operator = get_operator();

          finish_item(command);
      end
      `uvm_info("ALU Sequence", $sformatf("Finished %s sequence", get_operator().name), UVM_LOW)
   endtask : body
endclass : basic_sequence

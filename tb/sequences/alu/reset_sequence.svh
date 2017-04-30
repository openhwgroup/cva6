// Author: Florian Zaruba, ETH Zurich
// Date: 09/04/2017
// Description: Reset sequence, drives the circuit with a couple of inputs
//              before actual payload is expected
//
// Copyright (C) 2017 ETH Zurich, University of Bologna
// All rights reserved.

class reset_sequence extends fu_if_seq;

   `uvm_object_utils(reset_sequence);

   function new(string name = "reset");
      super.new(name);
   endfunction : new


   task body();

      fu_if_seq_item command;

      command = fu_if_seq_item::type_id::create("command");
      `uvm_info("RESET", "Starting reset phase", UVM_MEDIUM);
      // reset
      for (int i = 0; i < 20; i++) begin
      start_item(command);
      command.operand_a = 0;
      command.operand_b = 0;
      command.operand_c = 0;
      command.operator = 7'b00;
      finish_item(command);
      end

   endtask : body
endclass : reset_sequence

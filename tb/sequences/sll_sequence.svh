// Author: Florian Zaruba, ETH Zurich
// Date: 09/04/2017
// Description: Sequence specialization, extends basic sequence
//
// Copyright (C) 2017 ETH Zurich, University of Bologna
// All rights reserved.
class sll_sequence extends basic_sequence;

   `uvm_object_utils(sll_sequence);

   function new(string name = "sll");
      super.new(name);
   endfunction : new

   function fu_op get_operator();
	return SLL;
   endfunction : get_operator

   task body();
      super.body();
   endtask : body
endclass : sll_sequence

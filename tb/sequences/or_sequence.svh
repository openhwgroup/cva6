// Author: Florian Zaruba, ETH Zurich
// Date: 09/04/2017
// Description: Sequence specialization, extends basic sequence
//
// Copyright (C) 2017 ETH Zurich, University of Bologna
// All rights reserved.
class or_sequence extends basic_sequence;

   `uvm_object_utils(xor_sequence);

   function new(string name = "or");
      super.new(name);
   endfunction : new

   function fu_op get_operator();
	return ORL;
   endfunction : get_operator

   task body();
      super.body();
   endtask : body
endclass : or_sequence

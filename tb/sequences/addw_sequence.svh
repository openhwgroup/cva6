// Author: Florian Zaruba, ETH Zurich
// Date: 09/04/2017
// Description: Sequence specialization, extends basic sequence
//
// Copyright (C) 2017 ETH Zurich, University of Bologna
// All rights reserved.
class addw_sequence extends basic_sequence;

   `uvm_object_utils(addw_sequence);

   function new(string name = "addw");
      super.new(name);
   endfunction : new

   function fu_op get_operator();
	return ADDW;
   endfunction : get_operator

   task body();
      super.body();
   endtask : body
endclass : addw_sequence

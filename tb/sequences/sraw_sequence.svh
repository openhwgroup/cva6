// Author: Florian Zaruba, ETH Zurich
// Date: 09/04/2017
// Description: Sequence specialization, extends basic sequence
//
// Copyright (C) 2017 ETH Zurich, University of Bologna
// All rights reserved.

class sraw_sequence extends basic_sequence;

   `uvm_object_utils(sraw_sequence);

   function new(string name = "sraw");
      super.new(name);
   endfunction : new

   function fu_op get_operator();
	return SRAW;
   endfunction : get_operator

   task body();
      super.body();
   endtask : body
endclass : sraw_sequence

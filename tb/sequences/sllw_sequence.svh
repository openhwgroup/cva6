class sllw_sequence extends basic_sequence;

   `uvm_object_utils(sllw_sequence);

   function new(string name = "sllw");
      super.new(name);
   endfunction : new

   function alu_op get_operator();
	return SLLW;
   endfunction : get_operator

   task body();
      super.body();
   endtask : body
endclass : sllw_sequence

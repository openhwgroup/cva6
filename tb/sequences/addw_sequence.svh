class addw_sequence extends basic_sequence;

   `uvm_object_utils(addw_sequence);

   function new(string name = "addw");
      super.new(name);
   endfunction : new

   function alu_op get_operator();
	return ADDW;
   endfunction : get_operator

   task body();
      super.body();
   endtask : body
endclass : addw_sequence

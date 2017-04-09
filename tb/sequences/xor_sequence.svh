class xor_sequence extends basic_sequence;

   `uvm_object_utils(xor_sequence);

   function new(string name = "xor");
      super.new(name);
   endfunction : new

   function alu_op get_operator();
	return XORL;
   endfunction : get_operator

   task body();
      super.body();
   endtask : body
endclass : xor_sequence

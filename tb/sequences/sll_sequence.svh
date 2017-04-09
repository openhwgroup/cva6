class sll_sequence extends basic_sequence;

   `uvm_object_utils(sll_sequence);

   function new(string name = "sll");
      super.new(name);
   endfunction : new

   function alu_op get_operator();
	return SLL;
   endfunction : get_operator

   task body();
      super.body();
   endtask : body
endclass : sll_sequence

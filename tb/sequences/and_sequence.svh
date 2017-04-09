class and_sequence extends basic_sequence;

   `uvm_object_utils(and_sequence);

   function new(string name = "and");
      super.new(name);
   endfunction : new

   function alu_op get_operator();
	return ANDL;
   endfunction : get_operator

   task body();
      super.body();
   endtask : body
endclass : and_sequence

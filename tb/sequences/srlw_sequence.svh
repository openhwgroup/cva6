class srlw_sequence extends basic_sequence;

   `uvm_object_utils(srlw_sequence);

   function new(string name = "srlw");
      super.new(name);
   endfunction : new

   function alu_op get_operator();
	return SRLW;
   endfunction : get_operator

   task body();
      super.body();
   endtask : body
endclass : srlw_sequence

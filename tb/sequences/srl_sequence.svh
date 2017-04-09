class srl_sequence extends basic_sequence;

   `uvm_object_utils(srl_sequence);

   function new(string name = "srl");
      super.new(name);
   endfunction : new

   function alu_op get_operator();
	return SRL;
   endfunction : get_operator

   task body();
      super.body();
   endtask : body
endclass : srl_sequence

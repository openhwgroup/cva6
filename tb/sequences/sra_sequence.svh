class sra_sequence extends basic_sequence;

   `uvm_object_utils(sra_sequence);

   function new(string name = "sra");
      super.new(name);
   endfunction : new

   function alu_op get_operator();
	return SRA;
   endfunction : get_operator

   task body();
      super.body();
   endtask : body
endclass : sra_sequence

class or_sequence extends basic_sequence;

   `uvm_object_utils(xor_sequence);

   function new(string name = "or");
      super.new(name);
   endfunction : new

   function alu_op get_operator();
	return ORL;
   endfunction : get_operator

   task body();
      super.body();
   endtask : body
endclass : or_sequence

class sraw_sequence extends basic_sequence;

   `uvm_object_utils(sraw_sequence);

   function new(string name = "sraw");
      super.new(name);
   endfunction : new

   function alu_op get_operator();
	return SRAW;
   endfunction : get_operator

   task body();
      super.body();
   endtask : body
endclass : sraw_sequence

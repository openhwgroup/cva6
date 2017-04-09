class add_sequence extends basic_sequence;

   `uvm_object_utils(basic_sequence);

   function new(string name = "add");
      super.new(name);
   endfunction : new

   function alu_op get_operator();
	return ADD;
   endfunction : get_operator

   task body();
      super.body();
   endtask : body
endclass : add_sequence

class sub_sequence extends basic_sequence;

   `uvm_object_utils(sub_sequence);

   function new(string name = "sub");
      super.new(name);
   endfunction : new

   function alu_op get_operator();
	  return SUB;
   endfunction : get_operator

   task body();
      super.body();
   endtask : body
endclass : sub_sequence

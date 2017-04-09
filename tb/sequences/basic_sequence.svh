virtual class basic_sequence extends fu_if_seq;

   `uvm_object_utils(basic_sequence);

   function new(string name = "basic");
      super.new(name);
   endfunction : new

   pure virtual function alu_op get_operator();

   task body();
      fu_if_seq_item command;

      command = fu_if_seq_item::type_id::create("command");

      for(int i = 0; i <= 100; i++) begin
          start_item(command);
          if(~command.randomize())
		`uvm_warning("ALU Basic Sequence", "Randomization constraints can not be met.")
          command.operator = get_operator();

          finish_item(command);
      end
   endtask : body
endclass : basic_sequence

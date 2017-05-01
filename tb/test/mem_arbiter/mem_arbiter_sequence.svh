class mem_arbiter_sequence extends mem_if_sequence;

   `uvm_object_utils(mem_arbiter_sequence);

   function new(string name = "mem_arbiter_sequence");
      super.new(name);
   endfunction : new

   task body();
      mem_if_seq_item command;

      command = mem_if_seq_item::type_id::create("command");
      `uvm_info("Mem Arbiter Sequence", "Starting mem_arbiter sequence", UVM_LOW)

      for(int i = 0; i <= 100; i++) begin
          start_item(command);

          void'(command.randomize());

          finish_item(command);
      end
      `uvm_info("Mem Arbiter Sequence", "Finished mem_arbiter sequence", UVM_LOW)
   endtask : body
endclass : mem_arbiter_sequence

// Author: Florian Zaruba, ETH Zurich
// Date: 12/21/2016
// Description: Scoreboard interface sequence
//
// Copyright (C) 2017 ETH Zurich, University of Bologna
// All rights reserved.
class scoreboard_if_seq extends uvm_sequence #(scoreboard_if_seq_item);

    // UVM Factory Registration Macro
    `uvm_object_utils(scoreboard_if_seq)

    //-----------------------------------------------
    // Data Members (Outputs rand, inputs non-rand)
    //-----------------------------------------------


    //------------------------------------------
    // Constraints
    //------------------------------------------



    //------------------------------------------
    // Methods
    //------------------------------------------

    // Standard UVM Methods:
    function new(string name = "scoreboard_if_seq");
      super.new(name);
    endfunction

    task body;
      scoreboard_if_seq_item req;

      begin
        req = scoreboard_if_seq_item::type_id::create("req");
        start_item(req);
        assert(req.randomize());
        finish_item(req);
      end
    endtask : body

endclass : scoreboard_if_seq
// Author: Florian Zaruba, ETH Zurich
// Date: 12/21/2016
// Description: Sequencer
//
// Copyright (C) 2017 ETH Zurich, University of Bologna
// All rights reserved.

class scoreboard_if_sequencer extends uvm_sequencer #(scoreboard_if_seq_item);

    // UVM Factory Registration Macro
    `uvm_component_utils(scoreboard_if_sequencer)

    // Standard UVM Methods:
    function new(string name="scoreboard_if_sequencer", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    endclass: scoreboard_if_sequencer



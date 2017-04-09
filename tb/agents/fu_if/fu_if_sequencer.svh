// Author: Florian Zaruba, ETH Zurich
// Date: 12/21/2016
// Description: Sequencer


class fu_if_sequencer extends uvm_sequencer #(fu_if_seq_item);

    // UVM Factory Registration Macro
    `uvm_component_utils(fu_if_sequencer)

    // Standard UVM Methods:
    function new(string name="fu_if_sequencer", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    endclass: fu_if_sequencer



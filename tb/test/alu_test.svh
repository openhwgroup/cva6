// Author: Florian Zaruba, ETH Zurich
// Date: 12/20/2016
// Description: This is the main implementation of the test class.
//              Randomized testing should take place here.

class alu_test extends alu_test_base;
    // UVM Factory Registration Macro
    `uvm_component_utils(alu_test)

    fibonacci_sequence fibonacci;
    add_sequence add_sequence;

    //------------------------------------------
    // Methods
    //------------------------------------------

    // Standard UVM Methods:
    function new(string name = "alu_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
    endfunction

    task run_phase(uvm_phase phase);
        phase.raise_objection(this, "alu_test");
        //fibonacci_sequence fibonacci;
        super.run_phase(phase);
	add_sequence = new("add");
	add_sequence.start(sequencer_h);
        fibonacci = new("fibonacci");
        fibonacci.start(sequencer_h);
        // Testlogic goes here
        #100ns;

        phase.drop_objection(this, "alu_test");
    endtask


endclass : alu_test

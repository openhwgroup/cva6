// Author: Florian Zaruba, ETH Zurich
// Date: 12/20/2016
// Description: This is the main implementation of the test class.
//              Randomized testing should take place here.

class alu_test extends alu_test_base;
    // UVM Factory Registration Macro
    `uvm_component_utils(alu_test)

    fibonacci_sequence fibonacci;

    //------------------------------------------
    // Methods
    //------------------------------------------

    // Standard UVM Methods:
    extern function new(string name = "alu_test", uvm_component parent = null);
    extern function void build_phase(uvm_phase phase);
    extern task run_phase(uvm_phase phase);

endclass : alu_test

function alu_test::new(string name = "alu_test", uvm_component parent = null);
    super.new(name, parent);
endfunction

function void alu_test::build_phase(uvm_phase phase);
    super.build_phase(phase);
endfunction

task alu_test::run_phase(uvm_phase phase);
    phase.raise_objection(this, "alu_test");
    //fibonacci_sequence fibonacci;
    super.run_phase(phase);
    fibonacci = new("fibonacci");
    fibonacci.start(sequencer_h);    
    // Testlogic goes here
    #100ns;
    
    phase.drop_objection(this, "alu_test");
endtask

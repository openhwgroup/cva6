// Author: Florian Zaruba, ETH Zurich
// Date: 12/20/2016
// Description: Agent configuration object.
//              This object is used by the agent to modularize the build and connect process.

class fu_if_agent_config extends uvm_object;

    // UVM Factory Registration Macro
    `uvm_object_utils(fu_if_agent_config)

    // Virtual Interface
    virtual fu_if fu;
    //------------------------------------------
    // Data Members
    //------------------------------------------
    // Is the agent active or passive
    uvm_active_passive_enum active = UVM_ACTIVE;

    // Standard UVM Methods:
    function new(string name = "fu_if_agent_config");
        super.new(name);
    endfunction : new

endclass : fu_if_agent_config




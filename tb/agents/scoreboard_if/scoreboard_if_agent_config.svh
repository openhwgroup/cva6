// Author: Florian Zaruba, ETH Zurich
// Date: 09/04/2017
// Description: Agent configuration object.
//              This object is used by the agent to modularize the build and connect process.
//
// Copyright (C) 2017 ETH Zurich, University of Bologna
// All rights reserved.

class scoreboard_if_agent_config extends uvm_object;

    // UVM Factory Registration Macro
    `uvm_object_utils(scoreboard_if_agent_config)

    // Virtual Interface
    virtual scoreboard_if scoreboard;
    //------------------------------------------
    // Data Members
    //------------------------------------------
    // Is the agent active or passive
    uvm_active_passive_enum active = UVM_ACTIVE;

    // Standard UVM Methods:
    function new(string name = "scoreboard_if_agent_config");
        super.new(name);
    endfunction : new

endclass : scoreboard_if_agent_config




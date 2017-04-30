// Author: Florian Zaruba, ETH Zurich
// Date: 30.04.2017
// Description: Agent configuration object mem_if
// Copyright (C) 2017 ETH Zurich, University of Bologna
// All rights reserved.
// This code is under development and not yet released to the public.
// Until it is released, the code is under the copyright of ETH Zurich and
// the University of Bologna, and may contain confidential and/or unpublished
// work. Any reuse/redistribution is strictly forbidden without written
// permission from ETH Zurich.
// Bug fixes and contributions will eventually be released under the
// SolderPad open hardware license in the context of the PULP platform
// (http://www.pulp-platform.org), under the copyright of ETH Zurich and the
// University of Bologna.

class mem_if_agent_config extends uvm_object;

    // UVM Factory Registration Macro
    `uvm_object_utils(mem_if_agent_config)

    //------------------------------------------
    // Data Members
    //------------------------------------------
    // Virtual Interface
    virtual mem_if fu;
    // Is this a master or a slave interface
    mem_if_config mem_if_config;
    // configure the path to the memory file from which to serve all read requests
    string mem_file;
    // Is the agent active or passive
    uvm_active_passive_enum active = UVM_ACTIVE;

    // Standard UVM Methods:
    function new(string name = "mem_if_agent_config");
        super.new(name);
    endfunction : new

endclass : mem_if_agent_config




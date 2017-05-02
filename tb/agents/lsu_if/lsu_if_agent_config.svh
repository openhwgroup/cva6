// Author: Florian Zaruba, ETH Zurich
// Date: 02.05.2017
// Description: Agent configuration object lsu_if
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

class lsu_if_agent_config extends uvm_object;

    // UVM Factory Registration Macro
    `uvm_object_utils(lsu_if_agent_config)

    // Virtual Interface
    virtual lsu_if m_vif;
    //------------------------------------------
    // Data Members
    //------------------------------------------
    // Is the agent active or passive
    uvm_active_passive_enum active = UVM_ACTIVE;

    // Standard UVM Methods:
    function new(string name = "lsu_if_agent_config");
        super.new(name);
    endfunction : new

endclass : lsu_if_agent_config




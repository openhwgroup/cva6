// Author: Florian Zaruba, ETH Zurich
// Date: 17.06.2017
// Description: Instruction tracer single exception item
//
// Copyright (C) 2017 ETH Zurich, University of Bologna
// All rights reserved.
//
// This code is under development and not yet released to the public.
// Until it is released, the code is under the copyright of ETH Zurich and
// the University of Bologna, and may contain confidential and/or unpublished
// work. Any reuse/redistribution is strictly forbidden without written
// permission from ETH Zurich.
//
// Bug fixes and contributions will eventually be released under the
// SolderPad open hardware license in the context of the PULP platform
// (http://www.pulp-platform.org), under the copyright of ETH Zurich and the
// University of Bologna.
//
class exception_trace_item;
    // contains a human readable form of the cause value
    string       cause_s;
    logic [63:0] cause;
    logic [63:0] tval;
    logic [63:0] pc;

    function new (logic [63:0] pc, logic [63:0] cause, logic [63:0] tval);

        this.cause = cause;

        case (cause)
            INSTR_ADDR_MISALIGNED: this.cause_s = "Instruction Address Misaligned";
            INSTR_ACCESS_FAULT:    this.cause_s = "Instruction Access Fault";
            ILLEGAL_INSTR:         this.cause_s = "Illegal Instruction";
            BREAKPOINT:            this.cause_s = "Breakpoint";
            LD_ADDR_MISALIGNED:    this.cause_s = "Load Address Misaligned";
            LD_ACCESS_FAULT:       this.cause_s = "Load Access Fault";
            ST_ADDR_MISALIGNED:    this.cause_s = "Store Address Misaligned";
            ST_ACCESS_FAULT:       this.cause_s = "Store Access Fault";
            ENV_CALL_UMODE:        this.cause_s = "Environment Call User Mode";
            ENV_CALL_SMODE:        this.cause_s = "Environment Call Supervisor Mode";
            ENV_CALL_MMODE:        this.cause_s = "Environment Call Machine Mode";
            INSTR_PAGE_FAULT:      this.cause_s = "Instruction Page Fault";
            LOAD_PAGE_FAULT:       this.cause_s = "Load Page Fault";
            STORE_PAGE_FAULT:      this.cause_s = "Store Page Fault";
            default: this.cause = "Interrupt";
        endcase

        this.tval = tval;
        this.pc = pc;
    endfunction : new

    function string printException();
        string s;
        s = $sformatf("Exception @%10t, PC: %h, Cause: %s", $time, this.pc, this.cause_s);
        // write out tval if it wasn't an environment call, in that case the tval field has no meaning
        if (!(this.cause inside {ENV_CALL_MMODE, ENV_CALL_SMODE, ENV_CALL_UMODE}))
            s = $sformatf("%s, \n\t\t\t\ttval: %h", s, this.tval);
        return s;
    endfunction

endclass : exception_trace_item

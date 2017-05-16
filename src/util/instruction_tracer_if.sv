// Author: Florian Zaruba, ETH Zurich
// Date: 16.05.2017
// Description: Instruction Tracer Interface
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
import ariane_pkg::*;
`ifndef INSTR_TRACER_IF_SV
`define INSTR_TRACER_IF_SV
interface instruction_tracer_if (
        input clk
    );
    logic            rstn;
    logic            flush_issue;
    logic            flush;
    // decode
    fetch_entry      fetch;
    logic            fetch_valid;
    logic            fetch_ack;

    // WB stage
    logic [4:0]      waddr;
    logic [63:0]     wdata;
    logic            we;

    // commit stage
    scoreboard_entry commit_instr; // commit instruction
    logic            commit_ack;

    // the tracer just has a passive interface we do not drive anything with it
    clocking pck @(posedge clk);
        input rstn, flush, fetch, fetch_valid, fetch_ack, waddr, wdata, we, commit_instr, commit_ack;
    endclocking

endinterface
`endif
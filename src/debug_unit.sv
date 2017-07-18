// Author: Florian Zaruba, ETH Zurich
// Date: 29.06.2017
// Description: Memory Mapped Debug Unit
//
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

module debug_unit (
    input  logic                clk_i,          // Clock
    input  logic                rst_ni,         // Asynchronous reset active low

    input  scoreboard_entry     commit_instr_i,
    input  logic                commit_ack_i,
    input  exception            ex_i,           // instruction caused an exception
    output logic                halt_o,         // halt the hart
    // External Debug Interface
    input  logic                debug_req_i,
    output logic                debug_gnt_o,
    output logic                debug_rvalid_o,
    input  logic [14:0]         debug_addr_i,
    input  logic                debug_we_i,
    input  logic [63:0]         debug_wdata_i,
    output logic [63:0]         debug_rdata_o,
    output logic                debug_halted_o,
    input  logic                debug_halt_i,
    input  logic                debug_resume_i

);
    // select debug register source/destination
    enum logic [2:0] {RD_NONE, RD_CSR, RD_GPR, RD_DBGA, RD_DBGS} rdata_sel_q, rdata_sel_n;

    enum logic [1:0] {RUNNING, HALT_REQ, SINGLE_STEP, HALTED} CS, NS;

    // debug interface registers, we need to give the read data back one cycle later along with the rvalid flag
    logic rvalid_n, rvalid_q;
    logic rdata_n,  rdata_q;
    // save previous PC
    logic ppc_n, ppc_q;
    // ---------------
    // Debug Register
    // ---------------
    // enable exceptions which will cause a transfer to the debug mode
    logic [63:0] dbg_ie_n, dbg_ie_q;
    // cause register which caused transfer to debug mode
    logic [63:0] dbg_cause_n, dbg_cause_q;

    // change debug mode
    logic halt_req, resume_req;
    logic ss_req, ss_resume_req; // request single step and resume execution from single step

    assign debug_rvalid_o = rvalid_q;
    assign debug_rdata_o  = rdata_q;


    // |    Address    |       Name      |                             Description                             |
    // |---------------|-----------------|---------------------------------------------------------------------|
    // | 0x0000-0x007F | Debug Registers | Always accessible, even when the core is running                    |
    // | 0x0400-0x047F | GPR (x0-x31)    | General Purpose Registers. Only accessible if the core is halted.   |
    // | 0x0500-0x05FF | FPR (f0-f31)    | Reserved. Not used in the Ariane.                                   |
    // | 0x2000-0x20FF | Debug Registers | Only accessible if the core is halted                               |
    // | 0x4000-0x7FFF | CSR             | Control and Status Registers. Only accessible if the core is halted |

    always_comb begin : debug_ctrl
        rdata_sel_n   = RD_NONE;

        debug_gnt_o   = 1'b0;
        rdata_n       = 'b0;
        rvalid_n      = 1'b0;

        halt_req      = 1'b0;
        ss_req        = 1'b0;
        ss_resume_req = 1'b0;
        // update the previous PC if got a valid commit
        ppc_n         = (commit_ack_i) ? commit_instr_i.pc : ppc_q;
        // debug registers
        dbg_ie_n      = dbg_ie_q;
        dbg_cause_n   = dbg_cause_q;

        // ----------
        // Read
        // ----------
        // we've got a new read request
        if (debug_req_i && !debug_we_i) begin
            // we can immediately grant the request
            debug_gnt_o = 1'b1;
            // decode debug address
            casex (debug_addr_i)
                DBG_CTRL:  rdata_n = {32'b0, 15'b0, (CS == HALTED), 15'b0, (CS == SINGLE_STEP)};
                DBG_HIT:   rdata_n = {64'b0};
                DBG_IE:    rdata_n = dbg_ie_q;
                DBG_CAUSE: rdata_n = dbg_cause_q;
                DBG_NPC:   rdata_n = commit_instr_i.pc;
                DBG_PPC:   rdata_n = ppc_q;
                DBG_GPR: begin

                end

                DBG_CSR: begin

                end
            endcase

        // ----------
        // Write
        // ----------
        end else if (debug_req_i) begin
            // we can also immediately grant
            debug_gnt_o = 1'b1;
            // decode debug address
            case (debug_addr_i)
                DBG_CTRL: begin
                    // check if requested a halt
                    halt_req = debug_wdata_i[16];
                    resume_req = ~debug_wdata_i[16];
                    // enable/disable single step
                    ss_req = debug_wdata_i[0];
                    ss_resume_req = ~debug_wdata_i[0];
                end
                DBG_HIT:
                DBG_IE:     dbg_ie_n = debug_wdata_i;
                DBG_CAUSE:  dbg_cause_n = debug_wdata_i;
                DBG_GPR: begin

                end

                DBG_CSR: begin

                end
            endcase
        end

        // if an exception occurred and it is enabled to trigger debug mode, halt the processor
        if (ex_i.valid && (|(ex_i.cause & dbg_ie_q)) == 1'b1) begin
            halt_req = 1'b1;
            // save the cause why we entered the exception
            dbg_cause_n = ex_i.cause;
        end
    end

    // --------------------
    // HW Breakpoints
    // --------------------

    // --------------------
    // Stall Control
    // --------------------
    always_comb begin
        NS = CS;
        // do not halt by default
        halt_o = 1'b0;
        case (CS)
            // CPU is running normally
            RUNNING: begin
                // external debugger requested to halt the CPU
                if (halt_req) begin
                    NS = HALT_REQ;
                end

            end
            // a halt was requested, we wait here until we get the next valid instruction
            // in order to properly populate the npc and ppc counters
            HALT_REQ: begin
                // we've got a valid instruction in the commit stage so we can proceed to the halted state
                if (commit_instr_i.valid) begin
                    NS = HALTED;
                end
            end
            // we are in single step mode
            SINGLE_STEP: begin
                // resume from single steps
                if (ss_resume_req) begin
                    NS = RUNNING;
                end
            end

            // CPU is halted, we are in debug mode
            HALTED: begin
                halt_o = 1'b1;
                if (resume_req)
                    NS = RUNNING;
            end

        endcase
    end

    // --------------------
    // Registers
    // --------------------
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (~rst_ni) begin
            CS          <= RUNNING;
            rdata_q     <= '0;
            rvalid_q    <= 1'b0;
            ppc_q       <= 64'b0;
            dbg_ie_q    <= 64'b0;
            dbg_cause_q <= 64'b0;
        end else begin
            CS          <= NS;
            rdata_q     <= rdata_n;
            rvalid_q    <= rvalid_n;
            ppc_q       <= ppc_n;
            dbg_ie_q    <= dbg_ie_n;
            dbg_cause_q <= dbg_cause_n;
        end
    end
endmodule

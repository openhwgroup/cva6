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
    // GPR interface
    output logic                debug_gpr_req_o,
    output logic [4:0]          debug_gpr_addr_o,
    output logic                debug_gpr_we_o,
    output logic [63:0]         debug_gpr_wdata_o,
    input  logic [63:0]         debug_gpr_rdata_i,
    // CSR interface
    output logic                debug_csr_req_o,
    output logic [11:0]         debug_csr_addr_o,
    output logic                debug_csr_we_o,
    output logic [63:0]         debug_csr_wdata_o,
    input  logic [63:0]         debug_csr_rdata_i,
    // CPU Control
    output logic [63:0]         debug_pc_o,
    output logic                debug_set_pc_o,
    // HWPB
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
    // Debugger State
    enum logic [1:0] {RUNNING, HALT_REQ, SINGLE_STEP, HALTED} CS, NS;

    // debug interface registers, we need to give the read data back one cycle later along with the rvalid flag
    logic rvalid_n, rvalid_q;
    logic rdata_n,  rdata_q;
    // save previous PC
    logic dbg_ppc_n, dbg_ppc_q;
    // ---------------
    // Debug Register
    // ---------------
    // enable exceptions which will cause a transfer to the debug mode
    logic [63:0] dbg_ie_n, dbg_ie_q;
    // cause register which caused transfer to debug mode
    logic [63:0] dbg_cause_n, dbg_cause_q;
    // single step mode
    logic dbg_ss_n, dbg_ss_q;
    logic [63:0] dbg_hit_n, dbg_hit_q;
    // hardware breakpoints
    logic [7:0][3:0]  dbg_hwbp_ctrl_n, dbg_hwbp_ctrl_q;
    logic [7:0][63:0] dbg_hwbp_data_n, dbg_hwbp_data_q;
    // ----------------------
    // Debug Control Signals
    // ----------------------
    // change debug mode
    logic halt_req, resume_req;
    logic stepped_single;
    // assigns, we can output a couple of signals directly
    assign debug_rvalid_o = rvalid_q;
    assign debug_rdata_o  = rdata_q;
    assign debug_halted_o = (CS == HALTED);

    // |    Address    |       Name      |                             Description                             |
    // |---------------|-----------------|---------------------------------------------------------------------|
    // | 0x0000-0x007F | Debug Registers | Always accessible, even when the core is running                    |
    // | 0x0400-0x047F | GPR (x0-x31)    | General Purpose Registers. Only accessible if the core is halted.   |
    // | 0x0500-0x05FF | FPR (f0-f31)    | Reserved. Not used in the Ariane.                                   |
    // | 0x2000-0x20FF | Debug Registers | Only accessible if the core is halted                               |
    // | 0x4000-0x7FFF | CSR             | Control and Status Registers. Only accessible if the core is halted |
    always_comb begin : debug_ctrl
        debug_gnt_o     = 1'b0;
        rdata_n         = 'b0;
        rvalid_n        = 1'b0;

        halt_req        = 1'b0;
        // update the previous PC if got a valid commit
        dbg_ppc_n           = (commit_ack_i) ? commit_instr_i.pc : dbg_ppc_q;
        // debug registers
        dbg_ie_n        = dbg_ie_q;
        dbg_cause_n     = dbg_cause_q;
        dbg_ss_n        = dbg_ss_q;
        dbg_hit_n       = dbg_hit_q;
        dbg_hwbp_ctrl_n = dbg_hwbp_ctrl_q;
        dbg_hwbp_data_n = dbg_hwbp_data_q;
        // GPR defaults
        debug_gpr_req_o     = 1'b0;
        debug_gpr_addr_o    = debug_addr_i[6:2];
        debug_gpr_we_o      = 1'b0;
        debug_gpr_wdata_o   = 64'b0;
        // CSR defaults
        debug_csr_req_o     = 1'b0;
        debug_csr_addr_o    = debug_addr_i[13:2];
        debug_csr_we_o      = 1'b0;
        debug_csr_wdata_o   = 64'b0;
        // change ctrl flow
        debug_pc_o          = 64'b0;
        debug_set_pc_o      = 1'b0;

        // we did one single step, set the sticky bit
        if (stepped_single)
            dbg_hit_n = 1'b1;

        // ----------
        // Read
        // ----------
        // we've got a new read request
        if (debug_req_i && !debug_we_i) begin
            // we can immediately grant the request
            debug_gnt_o = 1'b1;
            // decode debug address
            casez (debug_addr_i)
                DBG_CTRL:   rdata_n = {32'b0, 15'b0, debug_halted_o, 15'b0, dbg_ss_q};
                DBG_HIT:    rdata_n = {63'b0, dbg_hit_q};
                DBG_IE:     rdata_n = dbg_ie_q;
                DBG_CAUSE:  rdata_n = dbg_cause_q;
                // all breakpoints are implemented
                DBG_BPCTRL: rdata_n = {57'b0, dbg_hwbp_ctrl_q[debug_addr_i[5:3]], 2'b0, 1'b1};
                DBG_BPDATA: rdata_n = dbg_hwbp_data_q[debug_addr_i[5:3]];

                DBG_NPC: begin
                    if (debug_halted_o)
                        rdata_n = commit_instr_i.pc;
                end

                DBG_PPC: begin
                    if (debug_halted_o)
                        rdata_n = dbg_ppc_q;
                end

                DBG_GPR: begin
                    if (debug_halted_o) begin
                        debug_gpr_req_o = 1'b1;
                        rdata_n = debug_gpr_rdata_i;
                    end
                end

                DBG_CSR: begin
                    if (debug_halted_o) begin
                        debug_csr_req_o = 1'b1;
                        rdata_n = debug_csr_rdata_i;
                    end
                end
            endcase

        // ----------
        // Write
        // ----------
        end else if (debug_req_i) begin
            // we can also immediately grant
            debug_gnt_o = 1'b1;
            // decode debug address
            casez (debug_addr_i)
                DBG_CTRL: begin
                    // check if requested a halt
                    halt_req = debug_wdata_i[16];
                    resume_req = ~debug_wdata_i[16];
                    // enable/disable single step
                    dbg_ss_n = debug_wdata_i[0];
                end
                DBG_HIT:    dbg_hit_n   = {debug_wdata_i[15:8], debug_wdata_i[0]};
                DBG_IE:     dbg_ie_n    = debug_wdata_i;
                DBG_CAUSE:  dbg_cause_n = debug_wdata_i;

                // Only triggering on instruction fetch is allowed at the moment
                DBG_BPCTRL: dbg_hwbp_ctrl_n[debug_addr_i[5:3]] = {3'b0, debug_wdata_i[1]};
                DBG_BPDATA: dbg_hwbp_data_n[debug_addr_i[5:3]] = debug_wdata_i;

                DBG_NPC: begin
                    // Change CTRL Flow to debug PC
                    debug_pc_o = debug_wdata_i;
                    debug_set_pc_o = 1'b1;
                end
                // PPC is read-only
                DBG_PPC:;

                DBG_GPR: begin
                    if (debug_halted_o) begin
                        debug_gpr_req_o = 1'b1;
                        debug_gpr_we_o = 1'b1;
                        debug_gpr_wdata_o = debug_wdata_i;
                    end
                end

                DBG_CSR: begin
                    if (debug_halted_o) begin
                        debug_csr_req_o = 1'b1;
                        debug_csr_we_o = 1'b1;
                        debug_csr_wdata_o = debug_wdata_i;
                    end
                end
            endcase
        end

        // if an exception occurred and it is enabled to trigger debug mode, halt the processor and enter debug mode
        if (ex_i.valid && (|(ex_i.cause & dbg_ie_q)) == 1'b1) begin
            halt_req = 1'b1;
            // save the cause why we entered the exception
            dbg_cause_n = ex_i.cause;
        end
        // --------------------
        // HW Breakpoints
        // --------------------
        // check all possible breakpoints
        for (logic [7:0] i = 0; i < 8; i++) begin
            // check if a breakpoint is triggering, therefore check if it is enabled
            if (dbg_hwbp_ctrl_q[i][0]) begin
                // check if the PC is matching and the processor is currently retiring the instruction
                if (commit_instr_i.pc == dbg_hwbp_data_q[i] && commit_ack_i) begin
                    halt_req = 1'b1;
                    dbg_hit_n[15:8] = i;
                end
            end
        end
    end

    // --------------------
    // Stall Control
    // --------------------
    always_comb begin
        NS = CS;
        // do not halt by default
        halt_o = 1'b0;
        stepped_single = 1'b0;
        case (CS)
            // CPU is running normally
            RUNNING: begin
                // 1. external debugger requested to halt the CPU
                // 2. cross-trigger requested a halt
                // 3. a break-point hit
                if (halt_req || debug_halt_i) begin
                    NS = HALT_REQ;
                end

            end
            // a halt was requested, we wait here until we get the next valid instruction
            // in order to properly populate the NPC and PPC registers
            HALT_REQ: begin
                // we've got a valid instruction in the commit stage so we can proceed to the halted state
                if (commit_instr_i.valid) begin
                    NS = HALTED;
                    halt_o = 1'b1;
                end
            end
            // we are in single step mode
            SINGLE_STEP: begin
                // wait until the processor has acknowledge the instruction in the commit stage
                if (commit_ack_i) begin
                    // then halt again
                    NS = HALT_REQ;
                    // we did one single step assert the flag so that we can set the sticky bit
                    stepped_single = 1'b1;
                end
            end
            // CPU is halted, we are in debug mode
            HALTED: begin
                halt_o = 1'b1;
                if (resume_req || debug_resume_i)
                    NS = RUNNING;

                // resume from single step, check if single stepping is enabled and if the sticky bit is cleared
                if (dbg_ss_q && !dbg_hit_q) begin
                    NS = SINGLE_STEP;
                end
            end

        endcase
    end

    // --------------------
    // Registers
    // --------------------
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (~rst_ni) begin
            CS              <= RUNNING;
            rdata_q         <= '0;
            rvalid_q        <= 1'b0;
            dbg_ppc_q       <= 64'b0;
            dbg_ie_q        <= 64'b0;
            dbg_cause_q     <= 64'b0;
            dbg_hwbp_ctrl_q <= '0;
            dbg_hwbp_data_q <= '0;
            dbg_ss_q        <= 1'b0;
            dbg_hit_q       <= 1'b0;
        end else begin
            CS              <= NS;
            rdata_q         <= rdata_n;
            rvalid_q        <= rvalid_n;
            dbg_ppc_q       <= dbg_ppc_n;
            dbg_ie_q        <= dbg_ie_n;
            dbg_cause_q     <= dbg_cause_n;
            dbg_ss_q        <= dbg_ss_n;
            dbg_hit_q       <= dbg_hit_n;
            dbg_hwbp_ctrl_q <= dbg_hwbp_ctrl_n;
            dbg_hwbp_data_q <= dbg_hwbp_data_n;
        end
    end

    //--------------
    // Assertions
    //--------------

    // check that no registers are accessed when we are not in debug mode
    assert property (
      @(posedge clk_i) (debug_req_i) |-> ((debug_halted_o == 1'b1) ||
                                        ((debug_addr_i[14] != 1'b1) &&
                                         (debug_addr_i[13:7] != 5'b0_1001)  &&
                                         (debug_addr_i[13:7] != 5'b0_1000)) ) )
      else $warning("Trying to access internal debug registers while core is not stalled");

    // check that all accesses are word-aligned
    assert property (
      @(posedge clk_i) (debug_req_i) |-> (debug_addr_i[1:0] == 2'b00) );

endmodule

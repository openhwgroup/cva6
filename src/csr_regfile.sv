// Author: Florian Zaruba, ETH Zurich
// Date: 05.05.2017
// Description: CSR Register File as specified by RISC-V
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

module csr_regfile #(
    parameter int ASID_WIDTH = 1
    )(
    input  logic                  clk_i,    // Clock
    input  logic                  rst_ni,   // Asynchronous reset active low
    // send a flush request out if a CSR with a side effect has changed
    output logic                  flush_o,
    // Core and Cluster ID
    input  logic  [3:0]           core_id_i,
    input  logic  [5:0]           cluster_id_i,
    input  logic  [63:0]          boot_addr_i,
    // we are taking an exception
    input exception               ex_i,

    input  fu_op                  csr_op_i,
    input  logic  [11:0]          csr_addr_i,
    input  logic  [63:0]          csr_wdata_i,
    output logic  [63:0]          csr_rdata_o,
    input  logic  [63:0]          pc_i,             // PC of instruction accessing the CSR
    output exception              csr_exception_o,  // attempts to access a CSR without appropriate privilege
                                                    // level or to write  a read-only register also
                                                    // raises illegal instruction exceptions.
    // Interrupts/Exceptions
    output logic  [3:0]           irq_enable_o,
    output logic  [63:0]          epc_o,
    output logic  [63:0]          trap_vector_base_o,
    output priv_lvl_t             priv_lvl_o,
    // MMU
    output logic                  enable_translation_o,
    output logic                  flag_pum_o,
    output logic                  flag_mxr_o,
    // input logic flag_mprv_i,
    output logic [37:0]           pd_ppn_o,
    output logic [ASID_WIDTH-1:0] asid_o
    // Performance Counter
);

    csr_t csr_addr;
    assign csr_addr = csr_t'(csr_addr_i);

    // internal signal to keep track of access exceptions
    logic read_access_exception, update_access_exception;
    logic csr_we;
    logic [63:0] csr_wdata, csr_rdata;
    // ----------------
    // CSR Registers
    // ----------------
    // privilege level register
    priv_lvl_t   priv_lvl_n, priv_lvl_q, prev_priv_lvl_n, prev_priv_lvl_q;
    typedef struct packed {
        logic         sd;     // signal dirty - read-only - hardwired zero
        logic [62:36] wpri4;  // writes preserved reads ignored
        logic [1:0]   sxl;    // variable supervisor mode xlen - hardwired to zero
        logic [1:0]   uxl;    // variable user mode xlen - hardwired to zero
        logic [8:0]   wpri3;  // writes preserved reads ignored
        logic         tsr;    // trap sret
        logic         tw;     // time wait
        logic         tvm;    // trap virtual memory
        logic         mxr;    // make executable readable
        logic         sum;    // permit supervisor user memory access
        logic         mprv;   // modify privilege - privilege level for ld/st
        logic [1:0]   xs;     // extension register - hardwired to zero
        logic [1:0]   fs;     // extension register - hardwired to zero
        priv_lvl_t    mpp;    // holds the previous privilege mode up to machine
        logic [1:0]   wpri2;  // writes preserved reads ignored
        logic         spp;    // holds the previous privilege mode up to supervisor
        logic         mpie;   // machine interrupts enable bit active prior to trap
        logic         wpri1;  // writes preserved reads ignored
        logic         spie;   // supervisor interrupts enable bit active prior to trap
        logic         upie;   // user interrupts enable bit active prior to trap - hardwired to zero
        logic         mie;    // machine interrupts enable
        logic         wpri0;  // writes preserved reads ignored
        logic         sie;    // supervisor interrupts enable
        logic         uie;    // user interrupts enable - hardwired to zero
    } status_t;

    status_t mstatus_q, mstatus_n;

    logic [63:0] mtvec_q,    mtvec_n;
    logic [63:0] medeleg_q,  medeleg_n;
    logic [63:0] mideleg_q,  mideleg_n;
    logic [63:0] mip_q,      mip_n;
    logic [63:0] mie_q,      mie_n;
    logic [63:0] mscratch_q, mscratch_n;
    logic [63:0] mepc_q,     mepc_n;
    logic [63:0] mcause_q,   mcause_n;
    logic [63:0] mtval_q,    mtval_n;

    logic [63:0] stvec_q,    stvec_n;
    logic [63:0] sscratch_q, sscratch_n;
    logic [63:0] sepc_q,     sepc_n;
    logic [63:0] scause_q,   scause_n;
    logic [63:0] stval_q,    stval_n;

    typedef struct packed {
        logic [3:0]  mode;
        logic [15:0] asid;
        logic [43:0] ppn;
    } sapt_t;

    sapt_t satp_q, satp_n;


    // ----------------
    // CSR Read logic
    // ----------------
    always_comb begin : csr_read
        // a read access exception can only occur if we attempt to read a CSR which does not exist
        read_access_exception = 1'b0;
        csr_rdata = 64'b0;
        case (csr_addr.address)

            CSR_SSTATUS:            csr_rdata = mstatus_q & 64'h3fffe1fee;
            CSR_SIE:                csr_rdata = mie_q & mideleg_q;
            CSR_SIP:                csr_rdata = mip_q & mideleg_q;
            CSR_STVEC:              csr_rdata = stvec_q;
            CSR_SSCRATCH:           csr_rdata = sscratch_q;
            CSR_SEPC:               csr_rdata = sepc_q;
            CSR_SCAUSE:             csr_rdata = scause_q;
            CSR_STVAL:              csr_rdata = stval_q;
            CSR_SATP:               csr_rdata = satp_q;

            CSR_MSTATUS:            csr_rdata = mstatus_q;
            CSR_MISA:               csr_rdata = ISA_CODE;
            CSR_MEDELEG:            csr_rdata = medeleg_q;
            CSR_MIDELEG:            csr_rdata = mideleg_q;
            CSR_MIP:                csr_rdata = mip_q;
            CSR_MIE:                csr_rdata = mie_q;
            CSR_MTVEC:              csr_rdata = mtvec_q;
            CSR_MSCRATCH:           csr_rdata = mscratch_q;
            CSR_MEPC:               csr_rdata = mepc_q;
            CSR_MCAUSE:             csr_rdata = mcause_q;
            CSR_MTVAL:              csr_rdata = mtval_q;
            CSR_MVENDORID:          csr_rdata = 64'b0; // not implemented
            CSR_MARCHID:            csr_rdata = 64'b0; // PULP, anonymous source (no allocated ID yet)
            CSR_MIMPID:             csr_rdata = 64'b0; // not implemented
            CSR_MHARTID:            csr_rdata = {53'b0, cluster_id_i[5:0], 1'b0, core_id_i[3:0]};
            default: read_access_exception = 1'b1;
        endcase
    end
    // ---------------------------
    // CSR Write and update logic
    // ---------------------------
    always_comb begin : csr_update
        update_access_exception = 1'b0;

        priv_lvl_n = priv_lvl_q;
        mstatus_n  = mstatus_q;
        mtvec_n    = mtvec_q;
        medeleg_n  = medeleg_q;
        mideleg_n  = mideleg_q;
        mip_n      = mip_q;
        mie_n      = mie_q;
        mepc_n     = mepc_q;
        mcause_n   = mcause_q;
        mscratch_n = mscratch_q;
        mtval_n    = mtval_q;

        sepc_n     = sepc_q;
        scause_n   = scause_q;
        stvec_n    = stvec_q;
        sscratch_n = sscratch_q;
        stval_n    = stval_q;
        satp_n     = satp_q;

        // check for correct access rights and that we are writing
        if (((priv_lvl_q & csr_addr.csr_decode.priv_lvl) == csr_addr.csr_decode.priv_lvl) && csr_we) begin
            case (csr_addr.address)
                // sstatus is a subset of mstatus - mask it accordingly
                CSR_SSTATUS:            mstatus_n    = csr_wdata & 64'h3fffe1fee;
                // even machine mode interrupts can be visible and set-able to supervisor
                // if the corresponding bit in mideleg is set
                CSR_SIE:                mie_n       = csr_wdata & (~64'h111) & mideleg_q;
                CSR_SIP:                mip_n       = csr_wdata & (~64'h111) & mideleg_q;
                CSR_STVEC:              stvec_n     = {csr_wdata[63:2], 1'b0, csr_wdata[0]};
                CSR_SSCRATCH:           sscratch_n  = csr_wdata;
                CSR_SEPC:               sepc_n      = {csr_wdata[63:1], 1'b0};
                CSR_SCAUSE:             scause_n    = csr_wdata;
                CSR_STVAL:              stval_n     = csr_wdata;
                // supervisor address translation and protection
                CSR_SATP:               satp_n      = sapt_t'(csr_wdata);

                CSR_MSTATUS: begin
                    mstatus_n      = csr_wdata;
                    mstatus_n.sxl  = 2'b0;
                    mstatus_n.uxl  = 2'b0;
                    // hardwired zero registers
                    mstatus_n.sd   = 1'b0;
                    mstatus_n.xs   = 2'b0;
                    mstatus_n.fs   = 2'b0;
                    mstatus_n.upie = 1'b0;
                    mstatus_n.uie  = 1'b0;
                end
                // machine exception delegation register
                // 0 - 12 exceptions supported
                CSR_MEDELEG:            medeleg_n   = csr_wdata & (~64'hBFF);
                // machine interrupt delegation register
                // we do not support user interrupt delegation
                CSR_MIDELEG:            mideleg_n   = csr_wdata & (~64'hAAA);

                // mask the register so that user interrupts can never be set
                CSR_MIE:                mie_n       = csr_wdata & (~64'h111);
                CSR_MIP:                mip_n       = csr_wdata & (~64'h111);

                CSR_MTVEC:              mtvec_n     = {csr_wdata[63:2], 1'b0, csr_wdata[0]};
                CSR_MSCRATCH:           mscratch_n  = csr_wdata;
                CSR_MEPC:               mepc_n      = {csr_wdata[63:1], 1'b0};
                CSR_MCAUSE:             mcause_n    = csr_wdata;
                CSR_MTVAL:              mtval_n     = csr_wdata;
                default: update_access_exception = 1'b1;
            endcase
        end else begin
            update_access_exception = 1'b1;
        end
        // update exception CSRs
        // we got an exception update cause, pc and stval register
        if (ex_i.valid) begin
            automatic priv_lvl_t trap_to_priv_lvl;
            // figure out where to trap to
            // a m-mode trap might be delegated
            // first figure out if this was an exception or an interrupt e.g.: look at bit 63
            if ((ex_i.cause[63] && mideleg_q[ex_i.cause[62:0]]) ||
                (~ex_i.cause[63] && mideleg_q[ex_i.cause[62:0]])) begin
                trap_to_priv_lvl = PRIV_LVL_S;
            end

            // trap to supervisor mode
            if (trap_to_priv_lvl == PRIV_LVL_S) begin
                // update sstatus
                mstatus_n.sie  = 1'b0;
                mstatus_n.spie = mstatus_q.sie;
                mstatus_n.spp  = logic'(priv_lvl_q);
                // set cause
                scause_n = ex_i.cause;
                // set epc
                sepc_n = pc_i;
                // set mtval or stval
                stval_n = ex_i.tval;
            // trap to machine mode
            end else begin
                // update mstatus
                mstatus_n.mie  = 1'b0;
                mstatus_n.mpie = mstatus_q.sie;
                mstatus_n.mpp  = priv_lvl_q;
                mcause_n = ex_i.cause;
                // set epc
                mepc_n = pc_i;
                // set mtval or stval
                mtval_n = ex_i.tval;
            end
            priv_lvl_n = trap_to_priv_lvl;
        end
    end
    // ---------------------------
    // CSR OP Select Logic
    // ---------------------------
    always_comb begin : csr_op_logic
        csr_wdata = csr_wdata_i;
        csr_we    = 1'b1;

        unique case (csr_op_i)
            CSR_WRITE: csr_wdata = csr_wdata_i;
            CSR_SET:   csr_wdata = csr_wdata_i | csr_rdata;
            CSR_CLEAR: csr_wdata = (~csr_wdata_i) & csr_rdata;
            default: csr_we = 1'b0;
        endcase
    end
    // -------------------
    // Exception Control
    // -------------------
    always_comb begin : exception_ctrl
        csr_exception_o = {
            64'b0, 64'b0, 1'b0
        };
        // we got an exception in one of the processes above
        // throw an illegal instruction exception
        if (update_access_exception || read_access_exception) begin
            csr_exception_o = {
                pc_i, ILLEGAL_INSTR, 1'b1
            };
        end
    end
    // -------------------
    // Output Assignments
    // -------------------
    assign csr_rdata_o = csr_rdata;
    assign priv_lvl_o  = priv_lvl_q;
    // MMU outputs
    assign pd_ppn_o    = satp_q.ppn;
    assign asid_o      = satp_q.asid[ASID_WIDTH-1:0];
    assign flag_pum_o  = mstatus_q.sum;
    assign enable_translation_o = mstatus_q.tvm;
    assign flag_mxr_o  = mstatus_q.mxr;

    // output assignments dependent on privilege mode
    always_comb begin : priv_output
        trap_vector_base_o = mtvec_q;
        epc_o              = mepc_q;
        // output user mode stvec
        if (priv_lvl_q == PRIV_LVL_S) begin
            trap_vector_base_o = stvec_q;
        end
        if (prev_priv_lvl_q == PRIV_LVL_S) begin
            epc_o              = sepc_q;
        end

        for (int i = 0; i < 4; i++) begin
          irq_enable_o[i] = mstatus_q.mie;
          if (mideleg_q[i + 4]) begin
            irq_enable_o[i] = mstatus_q.sie & mstatus_q.mie;
          end
        end
    end

    // sequential process
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (~rst_ni) begin
            priv_lvl_q      <= PRIV_LVL_M;
            prev_priv_lvl_q <= PRIV_LVL_M;
            // machine mode registers
            mstatus_q       <= 64'b0;
            mtvec_q         <= {boot_addr_i[63:2], 2'b0}; // set to boot address + direct mode
            medeleg_q       <= 64'b0;
            mideleg_q       <= 64'b0;
            mepc_q          <= 64'b0;
            mcause_q        <= 64'b0;
            mscratch_q      <= 64'b0;
            mtval_q         <= 64'b0;
            // supervisor mode registers
            sepc_q          <= 64'b0;
            scause_q        <= 64'b0;
            stvec_q         <= 64'b0;
            sscratch_q      <= 64'b0;
            stval_q         <= 64'b0;
            satp_q          <= 64'b0;
        end else begin
            priv_lvl_q      <= priv_lvl_n;
            prev_priv_lvl_q <= prev_priv_lvl_n;
            // machine mode registers
            mstatus_q       <= mstatus_n;
            mtvec_q         <= mtvec_n;
            medeleg_q       <= medeleg_n;
            mideleg_q       <= mideleg_n;
            mip_q           <= mip_n;
            mie_q           <= mie_n;
            mepc_q          <= mepc_n;
            mcause_q        <= mcause_n;
            mscratch_q      <= mscratch_n;
            mtval_q         <= mtval_n;
            // supervisor mode registers
            sepc_q          <= sepc_n;
            scause_q        <= scause_n;
            stvec_q         <= stvec_n;
            sscratch_q      <= sscratch_n;
            stval_q         <= stval_n;
            satp_q          <= satp_n;
        end
    end
endmodule
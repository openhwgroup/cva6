// Author: Florian Zaruba, ETH Zurich
// Date: 19.04.2017
// Description: Load Store Unit, handles address calculation and memory interface signals
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

module lsu #(
    parameter int ASID_WIDTH = 1
    )(
    input  logic                     clk_i,
    input  logic                     rst_ni,
    input  logic                     flush_i,

    input  fu_op                     operator_i,
    input  logic [63:0]              operand_a_i,
    input  logic [63:0]              operand_b_i,
    input  logic [63:0]              imm_i,
    output logic                     lsu_ready_o,      // FU is ready e.g. not busy
    input  logic                     lsu_valid_i,      // Input is valid
    input  logic [TRANS_ID_BITS-1:0] lsu_trans_id_i,   // transaction id, needed for WB
    output logic [TRANS_ID_BITS-1:0] lsu_trans_id_o,   // ID of scoreboard entry at which to write back
    output logic [63:0]              lsu_result_o,
    output logic                     lsu_valid_o,      // transaction id for which the output is the requested one
    input  logic                     commit_i,         // commit the pending store

    input  logic                     enable_translation_i,

    input  logic                     fetch_req_i,
    output logic                     fetch_gnt_o,
    output logic                     fetch_valid_o,
    output logic                     fetch_err_o,
    input  logic [63:0]              fetch_vaddr_i,
    output logic [31:0]              fetch_rdata_o,

    input  priv_lvl_t                priv_lvl_i,
    input  logic                     flag_pum_i,
    input  logic                     flag_mxr_i,
    input  logic [37:0]              pd_ppn_i,
    input  logic [ASID_WIDTH-1:0]    asid_i,
    input  logic                     flush_tlb_i,

    mem_if.Slave                     instr_if,
    mem_if.Slave                     data_if,

    output exception                 lsu_exception_o   // to WB, signal exception status LD/ST exception

);
    mem_if ptw_if(clk_i);
    // byte enable based on operation to perform
    // data is misaligned
    logic data_misaligned;
    assign lsu_valid_o = 1'b0;

    enum { IDLE, STORE, LOAD_WAIT_TRANSLATION, LOAD_WAIT_GNT, LOAD_WAIT_RVALID } CS, NS;

    // virtual address as calculated by the AGU in the first cycle
    logic [63:0] vaddr_i;
    // stall signal e.g.: do not update registers from above
    logic stall;
    // gets the data from the register
    logic get_from_register;

    // those are the signals which are always correct
    // e.g.: they keep the value in the stall case
    logic [63:0] vaddr;
    logic [63:0] data;
    logic [7:0]  be;
    fu_op        operator;
    logic [TRANS_ID_BITS-1:0] trans_id;

    // registered address in case of a necessary stall
    logic [63:0]              vaddr_q;
    logic [63:0]              data_q;
    fu_op                     operator_q;
    logic [TRANS_ID_BITS-1:0] trans_id_q;

     // for ld/st address checker
    logic [63:0]             st_buffer_paddr;   // physical address for store
    logic [63:0]             st_buffer_data;  // store buffer data out
    logic [7:0]              st_buffer_be;
    logic                    st_buffer_valid;
    // store buffer control signals
    logic        st_ready;
    logic        st_valid;
    // from MMU
    logic translation_req, translation_valid;
    logic [63:0]  paddr_o;

    // ------------------------------
    // Address Generation Unit (AGU)
    // ------------------------------
    assign vaddr_i = imm_i + operand_a_i;
    assign data_if.address = vaddr_i;

    // ---------------
    // Memory Arbiter
    // ---------------
    logic [2:0][63:0] address_i;
    logic [2:0][63:0] data_wdata_i;
    logic [2:0] data_req_i;
    logic [2:0] data_we_i;
    logic [2:0][7:0] data_be_i;
    logic [2:0] data_gnt_o;
    logic [2:0] data_rvalid_o;
    logic [2:0][63:0] data_rdata_o;

    // port 0 PTW, port 1 loads, port 2 stores
    mem_arbiter mem_arbiter_i (
        // to D$
        .address_o     ( data_if.address     ),
        .data_wdata_o  ( data_if.data_wdata  ),
        .data_req_o    ( data_if.data_req    ),
        .data_we_o     ( data_if.data_we     ),
        .data_be_o     ( data_if.data_be     ),
        .data_gnt_i    ( data_if.data_gnt    ),
        .data_rvalid_i ( data_if.data_rvalid ),
        .data_rdata_i  ( data_if.data_rdata  ),

        // from PTW, Load logic and store queue
        .address_i     ( address_i           ),
        .data_wdata_i  ( data_wdata_i        ),
        .data_req_i    ( data_req_i          ),
        .data_we_i     ( data_we_i           ),
        .data_be_i     ( data_be_i           ),
        .data_gnt_o    ( data_gnt_o          ),
        .data_rvalid_o ( data_rvalid_o       ),
        .data_rdata_o  ( data_rdata_o        ),
        .flush_ready_o (                     ), // TODO: connect, wait for flush to be valid
        .*
    );

    // connecting PTW to D$ IF (aka mem arbiter)
    assign address_i   [0]    = ptw_if.address;
    assign data_wdata_i[0]    = ptw_if.data_wdata;
    assign data_req_i  [0]    = ptw_if.data_req;
    assign data_we_i   [0]    = ptw_if.data_we;
    assign data_be_i   [0]    = ptw_if.data_be;
    assign ptw_if.data_rvalid = data_rvalid_o[0];
    assign ptw_if.data_rdata  = data_rdata_o[0];

    // connect the load logic to the memory arbiter
    assign address_i [1]       = paddr_o;
    // this is a read only interface
    assign data_we_i    [1]    = 1'b0;
    assign data_wdata_i [1]    = 1'b0;
    assign data_be_i    [1]    = be;
    logic [63:0] rdata;
    // data coming from arbiter interface 1
    assign rdata = data_rdata_o[1];
    // -------------------
    // MMU e.g.: TLBs/PTW
    // -------------------
    mmu #(
        .INSTR_TLB_ENTRIES      ( 16                   ),
        .DATA_TLB_ENTRIES       ( 16                   ),
        .ASID_WIDTH             ( ASID_WIDTH           )
    ) i_mmu (
        .lsu_req_i              ( translation_req      ),
        .lsu_vaddr_i            ( vaddr                ),
        .lsu_valid_o            ( translation_valid    ),
        .lsu_paddr_o            ( paddr_o              ),
        .data_if                ( ptw_if               ),
        .*
    );

    // ------------------
    // Address Checker
    // ------------------
    logic address_match;
    // checks if the requested load is in the store buffer
    always_comb begin : address_checker
        address_match = 1'b0;
        // as a beginning the uppermost bits are identical and the entry is valid
        if (translation_valid & (paddr_o[63:3] == st_buffer_paddr[63:3]) & st_buffer_valid) begin
            // TODO: implement propperly, this is overly pessimistic
            address_match = 1'b1;
        end
    end

    // ------------------
    // LSU Control
    // ------------------
    // is the operation a load or store or nothing of relevance for the LSU
    enum { NONE, LD, ST } op;

    always_comb begin : lsu_control
        // default assignment
        NS = CS;
        lsu_trans_id_o  = trans_id;
        lsu_ready_o     = 1'b1;
        // is the store valid e.g.: can we put it in the store buffer
        st_valid        = 1'b0;
        // as a default we are not requesting on the read interface
        data_req_i[1]   = 1'b0;
        // request the address translation
        translation_req = 1'b0;
        // as a default we don't stall
        stall           = 1'b0;
        // as a default we won't take the operands from the internal
        // registers
        get_from_register = 1'b0;

        unique case (CS)
            // we can freely accept new request
            IDLE: begin
                // First of all we distinguish between load and stores
                // 1. for loads we need to wait until they can happen
                // 2. stores can be placed in the store buffer if it is empty
                // in any case we need to do address translation beforehand
                // LOAD
                if (op == LD & lsu_valid_i) begin
                    translation_req = 1'b1;
                    // we can never handle a load in a single cycle
                    // but at least on a tlb hit we can output it to the memory
                    if (translation_valid) begin
                        // check if the address is in the store buffer otherwise we need
                        // to wait until the store buffer has cleared its entry
                        if (~address_match) begin
                            // lets request this read
                            data_req_i[1] = 1'b1;
                            // we already got a grant here so lets wait for the rvalid
                            if (data_gnt_o[1]) begin
                                NS = LOAD_WAIT_RVALID;
                            end else begin // we didn't get a grant so wait for it in a separate stage
                                NS = LOAD_WAIT_GNT;
                            end
                        end
                    end else begin// otherwise we need to wait for the translation
                        NS = LOAD_WAIT_TRANSLATION;
                    end

                    lsu_ready_o = 1'b0;

                // STORE
                end else if (op == ST & lsu_valid_i) begin
                    translation_req = 1'b1;
                    // we can handle this store in this cycle if
                    // a. the storebuffer is not full
                    // b. the TLB was a hit
                    if (st_ready & translation_valid) begin
                        NS = IDLE;
                        // and commit to the store buffer
                        st_valid = 1'b1;
                        // make a dummy writeback so we
                        // tell the scoreboard that we processed the instruction accordingly

                    end else begin
                        // otherwise we are not able to process new requests, we wait for and ad
                        lsu_ready_o = 1'b0;
                        NS = STORE;
                    end
                end
            end
            // we wait here until the store buffer becomes ready again
            STORE: begin
                translation_req = 1'b1;
                // we are here because we weren't able to finish either the translation
                // or the store buffer was not ready. Wait here for both events.
                // this gets the data from the flipflop
                get_from_register = 1'b1;
                if (st_ready & translation_valid) begin
                    // we can accept a new request if we are here
                    // but first lets commit to the store buffer
                    st_valid = 1'b1;
                    // go back to the IDLE state
                    NS = IDLE;
                end else begin // we can't accept a new request and stay in the store state
                    stall = 1'b1;
                end
                // we are not ready to accept new requests in this state.
                lsu_ready_o = 1'b0;
            end
            // we wait here for the translation to finish
            LOAD_WAIT_TRANSLATION: begin
                translation_req = 1'b1;
                // get everything from the registers
                get_from_register = 1'b1;
                // and stall
                stall = 1'b1;
                // we can't accept new data
                lsu_ready_o = 1'b0;
                // wait here for the translation to be valid and request the data
                // also be sure that the address doesn't match with the one in the store buffer
                if (translation_valid & ~address_match) begin
                    // lets request this read
                    data_req_i[1] = 1'b1;
                    // we already got a grant here so lets wait for the rvalid
                    if (data_gnt_o[1]) begin
                        NS = LOAD_WAIT_RVALID;
                    end else begin // we didn't get a grant so wait for it in a separate stage
                        NS = LOAD_WAIT_GNT;
                    end
                end
            end
            // we wait here for the grant to happen
            LOAD_WAIT_GNT: begin
                translation_req = 1'b1;
                // we can't accept new data
                lsu_ready_o = 1'b0;
                // get everything from the registers
                get_from_register = 1'b1;
                // and stall
                stall = 1'b1;
                // lets request this read
                data_req_i[1] = 1'b1;
                // wait for the grant
                if (data_gnt_o[1]) begin
                        NS = LOAD_WAIT_RVALID;
                end
            end
            // we wait here for the rvalid to happen
            LOAD_WAIT_RVALID: begin
                // we got an rvalid, query for new data
                if (data_rvalid_o[1]) begin
                    translation_req = 1'b1;
                    // output the correct transaction_id since we don't use the get from register signal here
                    lsu_trans_id_o = trans_id_q;
                    // we got a rvalid so we can accept a new store/load request
                    lsu_ready_o = 1'b1;
                    // did we get a new request?

                    // essentially the same part as in IDLE but we can't accept a new store
                    // as the store could immediately be performed and we would collide on the
                    // trans id part (e.g.: a structural hazard)
                    if (op == LD & lsu_valid_i) begin
                        translation_req = 1'b1;
                        // we can never handle a load in a single cycle
                        // but at least on a tlb hit we can output it to the memory
                        if (translation_valid) begin
                            // check if the address is in the store buffer otherwise we need
                            // to wait until the store buffer has cleared its entry
                            if (~address_match) begin
                                // lets request this read
                                data_req_i[1] = 1'b1;
                                // we already got a grant here so lets wait for the rvalid
                                if (data_gnt_o[1]) begin
                                    NS = LOAD_WAIT_RVALID;
                                end else begin // we didn't get a grant so wait for it in a separate stage
                                    NS = LOAD_WAIT_GNT;
                                end
                            end
                        end else begin// otherwise we need to wait for the translation
                            NS = LOAD_WAIT_TRANSLATION;
                        end
                    // STORE
                    end else if (op == ST & lsu_valid_i) begin
                        NS = STORE;
                    end else begin
                        NS = IDLE;
                    end

                end else begin
                    // and stall
                    stall = 1'b1;
                     // we can't accept new data
                    lsu_ready_o = 1'b0;
                end
            end
        endcase
    end

    // determine whether this is a load or store
    always_comb begin : which_op
        unique case (operator_i)
            // all loads go here
            LD, LW, LWU, LH, LHU, LB, LBU:  op = LD;
            // all stores go here
            SD, SW, SH, SB, SBU:            op = ST;
            // not relevant for the lsu
            default:                        op = NONE;
        endcase
    end

    // ---------------
    // Store Queue
    // ---------------
    store_queue store_queue_i (
        // store queue write port
        .valid_i       ( st_valid            ),
        .paddr_i       ( paddr_o             ),
        .data_i        ( data                ),
        .be_i          ( be                  ),
        // store buffer in
        .paddr_o       ( st_buffer_paddr     ),
        .data_o        ( st_buffer_data      ),
        .valid_o       ( st_buffer_valid     ),
        .be_o          ( st_buffer_be        ),
        .ready_o       ( st_ready            ),

        .address_o     ( address_i    [2]    ),
        .data_wdata_o  ( data_wdata_i [2]    ),
        .data_req_o    ( data_req_i   [2]    ),
        .data_we_o     ( data_we_i    [2]    ),
        .data_be_o     ( data_be_i    [2]    ),
        .data_gnt_i    ( data_gnt_o   [2]    ),
        .data_rvalid_i ( data_rvalid_o[2]    ),
        .*
    );

    // ---------------
    // Byte Enable - TODO: Find a more beautiful way to accomplish this functionality
    // ---------------
    always_comb begin : byte_enable
        // we can generate the byte enable from the virtual address since the last
        // 12 bit are the same anyway
        // and we can always generate the byte enable from the address at hand
        case (operator)
            LD, SD: // double word
                case (vaddr[2:0])
                    3'b000: be = 8'b1111_1111;
                    // 3'b001: be = 8'b1111_1110;
                    // 3'b010: be = 8'b1111_1100;
                    // 3'b011: be = 8'b1111_1000;
                    // 3'b100: be = 8'b1111_0000;
                    // 3'b101: be = 8'b1110_0000;
                    // 3'b110: be = 8'b1100_0000;
                    // 3'b111: be = 8'b1000_0000;
                endcase
            LW, LWU, SW: // word
                case (vaddr[2:0])
                    3'b000: be = 8'b0000_1111;
                    3'b001: be = 8'b0001_1110;
                    3'b010: be = 8'b0011_1100;
                    3'b011: be = 8'b0111_1000;
                    3'b100: be = 8'b1111_0000;
                    // 3'b101: be = 8'b1110_0000;
                    // 3'b110: be = 8'b1100_0000;
                    // 3'b111: be = 8'b1000_0000;
                endcase
            LH, LHU, SH: // half word
                case (vaddr[2:0])
                    3'b000: be = 8'b0000_0011;
                    3'b001: be = 8'b0000_0110;
                    3'b010: be = 8'b0000_1100;
                    3'b011: be = 8'b0001_1000;
                    3'b100: be = 8'b0011_0000;
                    3'b101: be = 8'b0110_0000;
                    3'b110: be = 8'b1100_0000;
                    // 3'b111: be = 8'b1000_0000;
                endcase
            LB, LBU, SB: // byte
                case (vaddr[2:0])
                    3'b000: be = 8'b0000_0001;
                    3'b001: be = 8'b0000_0010;
                    3'b010: be = 8'b0000_0100;
                    3'b011: be = 8'b0000_1000;
                    3'b100: be = 8'b0001_0000;
                    3'b101: be = 8'b0010_0000;
                    3'b110: be = 8'b0100_0000;
                    3'b111: be = 8'b1000_0000;
                endcase
        endcase
    end

    // ---------------
    // Sign Extend
    // ---------------

    logic [63:0] rdata_d_ext; // sign extension for double words, actually only misaligned assembly
    logic [63:0] rdata_w_ext; // sign extension for words
    logic [63:0] rdata_h_ext; // sign extension for half words
    logic [63:0] rdata_b_ext; // sign extension for bytes

    // double words
    always_comb begin : sign_extend_double_word
        case (vaddr[2:0])
            3'b000: rdata_d_ext = rdata[63:0];
            // this is for misaligned accesse only
            // 3'b001: rdata_d_ext = {data_rdata_i[7:0],  rdata_q[63:8]};
            // 3'b010: rdata_d_ext = {data_rdata_i[15:0], rdata_q[63:16]};
            // 3'b011: rdata_d_ext = {data_rdata_i[23:0], rdata_q[63:24]};
            // 3'b100: rdata_d_ext = {data_rdata_i[31:0], rdata_q[63:32]};
            // 3'b101: rdata_d_ext = {data_rdata_i[39:0], rdata_q[63:40]};
            // 3'b110: rdata_d_ext = {data_rdata_i[47:0], rdata_q[63:48]};
            // 3'b111: rdata_d_ext = {data_rdata_i[55:0], rdata_q[63:56]};
        endcase
    end

      // sign extension for words
    always_comb begin : sign_extend_word
        case (vaddr[2:0])
            3'b000: rdata_w_ext = (operator == LW) ? {{32{rdata[31]}}, rdata[31:0]}  : {32'h0, rdata[31:0]};
            3'b001: rdata_w_ext = (operator == LW) ? {{32{rdata[39]}}, rdata[39:8]}  : {32'h0, rdata[39:8]};
            3'b010: rdata_w_ext = (operator == LW) ? {{32{rdata[47]}}, rdata[47:16]} : {32'h0, rdata[47:16]};
            3'b011: rdata_w_ext = (operator == LW) ? {{32{rdata[55]}}, rdata[55:24]} : {32'h0, rdata[55:24]};
            3'b100: rdata_w_ext = (operator == LW) ? {{32{rdata[63]}}, rdata[63:32]} : {32'h0, rdata[63:32]};
            // miss-aligned access
            // 3'b101: rdata_w_ext = (data_sign_ext_q) ? {{32{data_rdata_i[7]}},  data_rdata_i[7:0],   rdata_q[63:40]} : {32'h0, data_rdata_i[7:0],  rdata_q[63:40]};
            // 3'b110: rdata_w_ext = (data_sign_ext_q) ? {{32{data_rdata_i[15]}},  data_rdata_i[15:0], rdata_q[63:48]} : {32'h0, data_rdata_i[15:0], rdata_q[63:48]};
            // 3'b111: rdata_w_ext = (data_sign_ext_q) ? {{32{data_rdata_i[23]}},  data_rdata_i[23:0], rdata_q[63:56]} : {32'h0, data_rdata_i[23:0], rdata_q[63:56]};
        endcase
    end

    // sign extension for half words
    always_comb begin : sign_extend_half_word
        case (vaddr[2:0])
            3'b000: rdata_h_ext = (operator == LH) ? {{48{rdata[15]}}, rdata[15:0]}  : {48'h0, rdata[15:0]};
            3'b001: rdata_h_ext = (operator == LH) ? {{48{rdata[23]}}, rdata[23:8]}  : {48'h0, rdata[23:8]};
            3'b010: rdata_h_ext = (operator == LH) ? {{48{rdata[31]}}, rdata[31:16]} : {48'h0, rdata[31:16]};
            3'b011: rdata_h_ext = (operator == LH) ? {{48{rdata[39]}}, rdata[39:24]} : {48'h0, rdata[39:24]};
            3'b100: rdata_h_ext = (operator == LH) ? {{48{rdata[47]}}, rdata[47:32]} : {48'h0, rdata[47:32]};
            3'b101: rdata_h_ext = (operator == LH) ? {{48{rdata[55]}}, rdata[55:40]} : {48'h0, rdata[55:40]};
            3'b110: rdata_h_ext = (operator == LH) ? {{48{rdata[63]}}, rdata[63:48]} : {48'h0, rdata[63:48]};
            // miss-aligned access
            // 3'b111: rdata_h_ext = (data_sign_ext_q) ? {{48{data_rdata_i[7]}},  data_rdata_i[7:0], rdata_q[31:24]} : {48'h0, data_rdata_i[7:0], rdata_q[31:24]};
        endcase
    end

    always_comb begin : sign_extend_byte
        case (vaddr[2:0])
            3'b000: rdata_b_ext = (operator == LB) ? {{56{rdata[7]}},  rdata[7:0]}   : {56'h0, rdata[7:0]};
            3'b001: rdata_b_ext = (operator == LB) ? {{56{rdata[15]}}, rdata[15:8]}  : {56'h0, rdata[15:8]};
            3'b010: rdata_b_ext = (operator == LB) ? {{56{rdata[23]}}, rdata[23:16]} : {56'h0, rdata[23:16]};
            3'b011: rdata_b_ext = (operator == LB) ? {{56{rdata[31]}}, rdata[31:24]} : {56'h0, rdata[31:24]};
            3'b100: rdata_b_ext = (operator == LB) ? {{56{rdata[39]}}, rdata[39:32]} : {56'h0, rdata[39:32]};
            3'b101: rdata_b_ext = (operator == LB) ? {{56{rdata[47]}}, rdata[47:40]} : {56'h0, rdata[47:40]};
            3'b110: rdata_b_ext = (operator == LB) ? {{56{rdata[55]}}, rdata[55:48]} : {56'h0, rdata[55:48]};
            3'b111: rdata_b_ext = (operator == LB) ? {{56{rdata[63]}}, rdata[63:56]} : {56'h0, rdata[63:56]};
        endcase // case (rdata_offset_q)
    end

    always_comb begin
        case (operator)
            LD:            lsu_result_o = rdata_d_ext;
            LW, LWU:       lsu_result_o = rdata_w_ext;
            LH, LHU:       lsu_result_o = rdata_h_ext;
            LB, LBU:       lsu_result_o = rdata_b_ext;
        endcase //~case(rdata_type_q)
    end

    // ------------------
    // Exception Control
    // ------------------
    // misaligned detector
    // page fault, privilege exception
    // we can detect a misaligned exception immediately
    always_comb begin : exception_control
        data_misaligned = 1'b0;

        if(lsu_valid_i) begin
          case (operator_i)
            LD, SD: begin // double word
              if(vaddr_i[2:0] != 3'b000)
                data_misaligned = 1'b1;
            end

            LW, LWU, SW: begin // word
              if(vaddr_i[2] == 1'b1 && vaddr_i[2:0] != 3'b100)
                data_misaligned = 1'b1;
            end

            LH, LHU, SH: begin // half word
              if(vaddr_i[2:0] == 3'b111)
                data_misaligned = 1'b1;
            end  // byte -> is always aligned
            default:;
          endcase
        end
    end

    // this process selects the input based on the current state of the LSU
    // it can either be feedthrough from the issue stage or from the internal register
    always_comb begin : input_select
        // if we are stalling use the values we saved
        if (get_from_register) begin
            vaddr    = vaddr_q;
            data     = data_q;
            operator = operator_q;
            trans_id = trans_id_q;
        end else begin // otherwise pass them directly through
            vaddr    = vaddr_i;
            data     = operand_b_i;
            operator = operator_i;
            trans_id = lsu_trans_id_i;
        end
    end

    // registers
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (~rst_ni) begin
            vaddr_q      <= 64'b0;
            data_q       <= 64'b0;
            operator_q   <= ADD;
            trans_id_q   <= '{default: 0};
            CS           <= IDLE;
        end else begin
            CS <= NS;
            if (~stall) begin
                vaddr_q    <= vaddr_i;
                data_q     <= operand_b_i;
                operator_q <= operator_i;
                trans_id_q <= lsu_trans_id_i;
            end
        end
    end

  // // ------------
  // // Assertions
  // // ------------

  // // make sure there is no new request when the old one is not yet completely done
  // // i.e. it should not be possible to get a grant without an rvalid for the
  // // last request
  // `ifndef VERILATOR
  // assert property (
  //   @(posedge clk) ((CS == WAIT_RVALID) && (data_gnt_i == 1'b1)) |-> (data_rvalid_i == 1'b1) )
  //   else begin $error("data grant without rvalid"); $stop(); end

  // // there should be no rvalid when we are in IDLE
  // assert property (
  //   @(posedge clk) (CS == IDLE) |-> (data_rvalid_i == 1'b0) )
  //   else begin $error("Received rvalid while in IDLE state"); $stop(); end

  // // assert that errors are only sent at the same time as grant or rvalid
  // assert property ( @(posedge clk) (data_err_i) |-> (data_gnt_i || data_rvalid_i) )
  //   else begin $error("Error without data grant or rvalid"); $stop(); end

  // // assert that the address does not contain X when request is sent
  // assert property ( @(posedge clk) (data_req_o) |-> (!$isunknown(data_addr_o)) )
  //   else begin $error("address contains X when request is set"); $stop(); end
  // `endif

endmodule
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
    output logic                     lsu_ready_o,              // FU is ready e.g. not busy
    input  logic                     lsu_valid_i,              // Input is valid
    input  logic [TRANS_ID_BITS-1:0] trans_id_i,               // transaction id, needed for WB
    output logic [TRANS_ID_BITS-1:0] lsu_trans_id_o,           // ID of scoreboard entry at which to write back
    output logic [63:0]              lsu_result_o,
    output logic                     lsu_valid_o,              // transaction id for which the output is the requested one
    input  logic                     commit_i,                 // commit the pending store

    input  logic                     enable_translation_i,     // enable virtual memory translation

    input  logic                     fetch_req_i,              // Instruction fetch interface
    output logic                     fetch_gnt_o,              // Instruction fetch interface
    output logic                     fetch_valid_o,            // Instruction fetch interface
    output logic                     fetch_err_o,              // Instruction fetch interface
    input  logic [63:0]              fetch_vaddr_i,            // Instruction fetch interface
    output logic [31:0]              fetch_rdata_o,            // Instruction fetch interface

    input  priv_lvl_t                priv_lvl_i,               // From CSR register file
    input  logic                     flag_pum_i,               // From CSR register file
    input  logic                     flag_mxr_i,               // From CSR register file
    input  logic [37:0]              pd_ppn_i,                 // From CSR register file
    input  logic [ASID_WIDTH-1:0]    asid_i,                   // From CSR register file
    input  logic                     flush_tlb_i,
     // Instruction memory/cache
    output logic [63:0]              instr_if_address_o,
    output logic                     instr_if_data_req_o,
    output logic [3:0]               instr_if_data_be_o,
    input  logic                     instr_if_data_gnt_i,
    input  logic                     instr_if_data_rvalid_i,
    input  logic [31:0]              instr_if_data_rdata_i,
    // Data cache
    output logic [11:0]              data_if_address_index_o,
    output logic [43:0]              data_if_address_tag_o,
    output logic [63:0]              data_if_data_wdata_o,
    output logic                     data_if_data_req_o,
    output logic                     data_if_data_we_o,
    output logic [7:0]               data_if_data_be_o,
    output logic                     data_if_kill_req_o,
    output logic                     data_if_tag_valid_o,
    input  logic                     data_if_data_gnt_i,
    input  logic                     data_if_data_rvalid_i,
    input  logic [63:0]              data_if_data_rdata_i,

    output exception                 lsu_exception_o   // to WB, signal exception status LD/ST exception

);
    // data is misaligned
    logic data_misaligned;
    // --------------------------------------
    // 1st register stage - (stall registers)
    // --------------------------------------
    // those are the signals which are always correct
    // e.g.: they keep the value in the stall case
    logic [63:0]              vaddr;
    logic [63:0]              data;
    logic [7:0]               be;
    fu_op                     operator;
    logic [TRANS_ID_BITS-1:0] trans_id;
    // registered address in case of a necessary stall
    logic [63:0]              vaddr_n,    vaddr_q;
    logic [63:0]              data_n,     data_q;
    fu_op                     operator_n, operator_q;
    logic [TRANS_ID_BITS-1:0] trans_id_n, trans_id_q;
    logic [7:0]               be_n,       be_q;
    logic                     stall_n,    stall_q;
    // ------------------------------
    // Address Generation Unit (AGU)
    // ------------------------------
    // virtual address as calculated by the AGU in the first cycle
    logic [63:0] vaddr_i;
    logic [7:0]  be_i;
    assign vaddr_i = $signed(imm_i) + $signed(operand_a_i);

    logic                     st_valid_i;
    logic                     st_ready_o;
    logic                     ld_valid_i;
    logic                     ld_ready_o;
    logic                     ld_translation_req;
    logic                     st_translation_req;
    logic [63:0]              ld_vaddr;
    logic [63:0]              st_vaddr;
    logic                     translation_req;
    logic                     translation_valid;
    logic [63:0]              mmu_vaddr;
    logic [63:0]              mmu_paddr;
    exception                 mmu_exception;

    logic                     ld_valid;
    logic [TRANS_ID_BITS-1:0] ld_trans_id;
    logic [63:0]              ld_result;
    logic                     st_valid;
    logic [TRANS_ID_BITS-1:0] st_trans_id;
    logic [63:0]              st_result;

    logic [11:0]              page_offset;
    logic                     page_offset_matches;

    exception                 misaligned_exception;
    exception                 ld_ex;
    exception                 st_ex;

    // ---------------
    // Memory Arbiter
    // ---------------
    logic [2:0][11:0]         address_index_i;
    logic [2:0][43:0]         address_tag_i;
    logic [2:0][63:0]         data_wdata_i;
    logic [2:0]               data_req_i;
    logic [2:0]               data_we_i;
    logic [2:0]               kill_req_i;
    logic [2:0]               tag_valid_i;
    logic [2:0][7:0]          data_be_i;
    logic [2:0]               data_gnt_o;
    logic [2:0]               data_rvalid_o;
    logic [2:0][63:0]         data_rdata_o;

    // decreasing priority
    // Port 0: PTW
    // Port 1: Load Unit
    // Port 2: Store Unit
    dcache_arbiter dcache_arbiter_i (
        // to D$
        .address_index_o   ( data_if_address_index_o ),
        .address_tag_o     ( data_if_address_tag_o   ),
        .data_wdata_o      ( data_if_data_wdata_o    ),
        .data_req_o        ( data_if_data_req_o      ),
        .data_we_o         ( data_if_data_we_o       ),
        .data_be_o         ( data_if_data_be_o       ),
        .kill_req_o        ( data_if_kill_req_o      ),
        .tag_valid_o       ( data_if_tag_valid_o     ),
        .data_gnt_i        ( data_if_data_gnt_i      ),
        .data_rvalid_i     ( data_if_data_rvalid_i   ),
        .data_rdata_i      ( data_if_data_rdata_i    ),
        // from PTW, Load Unit and Store Unit
        .address_index_i   ( address_index_i         ),
        .address_tag_i     ( address_tag_i           ),
        .data_wdata_i      ( data_wdata_i            ),
        .data_req_i        ( data_req_i              ),
        .data_we_i         ( data_we_i               ),
        .data_be_i         ( data_be_i               ),
        .kill_req_i        ( kill_req_i              ),
        .tag_valid_i       ( tag_valid_i             ),
        .data_gnt_o        ( data_gnt_o              ),
        .data_rvalid_o     ( data_rvalid_o           ),
        .data_rdata_o      ( data_rdata_o            ),
        .*
    );

    // -------------------
    // MMU e.g.: TLBs/PTW
    // -------------------
    mmu #(
        .INSTR_TLB_ENTRIES      ( 16                   ),
        .DATA_TLB_ENTRIES       ( 16                   ),
        .ASID_WIDTH             ( ASID_WIDTH           )
    ) mmu_i (
            // misaligned bypass
        .misaligned_ex_i        ( misaligned_exception ),
        .lsu_req_i              ( translation_req      ),
        .lsu_vaddr_i            ( mmu_vaddr            ),
        .lsu_valid_o            ( translation_valid    ),
        .lsu_paddr_o            ( mmu_paddr            ),
        .lsu_exception_o        ( mmu_exception        ),
        // connecting PTW to D$ IF (aka mem arbiter
        .address_index_o        ( address_index_i  [0] ),
        .address_tag_o          ( address_tag_i    [0] ),
        .data_wdata_o           ( data_wdata_i     [0] ),
        .data_req_o             ( data_req_i       [0] ),
        .data_we_o              ( data_we_i        [0] ),
        .data_be_o              ( data_be_i        [0] ),
        .kill_req_o             ( kill_req_i       [0] ),
        .tag_valid_o            ( tag_valid_i      [0] ),
        .data_gnt_i             ( data_gnt_o       [0] ),
        .data_rvalid_i          ( data_rvalid_o    [0] ),
        .data_rdata_i           ( data_rdata_o     [0] ),
        .*
    );
    // ------------------
    // Store Unit
    // ------------------
    store_unit store_unit_i (
        .operator_i            ( operator             ),
        .trans_id_i            ( trans_id             ),
        .valid_i               ( st_valid_i           ),
        .vaddr_i               ( vaddr                ),
        .be_i                  ( be                   ),
        .data_i                ( data                 ),
        .valid_o               ( st_valid             ),
        .ready_o               ( st_ready_o           ),
        .trans_id_o            ( st_trans_id          ),
        .result_o              ( st_result            ),
        .ex_o                  ( st_ex                ),
        // MMU port
        .translation_req_o     ( st_translation_req   ),
        .vaddr_o               ( st_vaddr             ),
        .paddr_i               ( mmu_paddr            ),
        .translation_valid_i   ( translation_valid    ),
        .ex_i                  ( mmu_exception        ),
        // Load Unit
        .page_offset_i         ( page_offset          ),
        .page_offset_matches_o ( page_offset_matches  ),
        // to memory arbiter
        .address_index_o       ( address_index_i  [2] ),
        .address_tag_o         ( address_tag_i    [2] ),
        .data_wdata_o          ( data_wdata_i     [2] ),
        .data_req_o            ( data_req_i       [2] ),
        .data_we_o             ( data_we_i        [2] ),
        .data_be_o             ( data_be_i        [2] ),
        .kill_req_o            ( kill_req_i       [2] ),
        .tag_valid_o           ( tag_valid_i      [2] ),
        .data_gnt_i            ( data_gnt_o       [2] ),
        .data_rvalid_i         ( data_rvalid_o    [2] ),
        .*
    );

    // ------------------
    // Load Unit
    // ------------------
    load_unit load_unit_i (
        .operator_i            ( operator             ),
        .trans_id_i            ( trans_id             ),
        .valid_i               ( ld_valid_i           ),
        .vaddr_i               ( vaddr                ),
        .be_i                  ( be                   ),
        .valid_o               ( ld_valid             ),
        .ready_o               ( ld_ready_o           ),
        .trans_id_o            ( ld_trans_id          ),
        .result_o              ( ld_result            ),
        .ex_o                  ( ld_ex                ),
        // MMU port
        .translation_req_o     ( ld_translation_req   ),
        .vaddr_o               ( ld_vaddr             ),
        .paddr_i               ( mmu_paddr            ),
        .translation_valid_i   ( translation_valid    ),
        .ex_i                  ( mmu_exception        ),
        // to store unit
        .page_offset_o         ( page_offset          ),
        .page_offset_matches_i ( page_offset_matches  ),
        // to memory arbiter
        .address_index_o       ( address_index_i  [1] ),
        .address_tag_o         ( address_tag_i    [1] ),
        .data_wdata_o          ( data_wdata_i     [1] ),
        .data_req_o            ( data_req_i       [1] ),
        .data_we_o             ( data_we_i        [1] ),
        .data_be_o             ( data_be_i        [1] ),
        .kill_req_o            ( kill_req_i       [1] ),
        .tag_valid_o           ( tag_valid_i      [1] ),
        .data_gnt_i            ( data_gnt_o       [1] ),
        .data_rvalid_i         ( data_rvalid_o    [1] ),
        .data_rdata_i          ( data_rdata_o     [1] ),
        .*
    );

    // ---------------------
    // Result Sequentialize
    // ---------------------
    lsu_arbiter lsu_arbiter_i (
        .clk_i                ( clk_i                 ),
        .rst_ni               ( rst_ni                ),
        .flush_i              ( flush_i               ),
        .ld_valid_i           ( ld_valid              ),
        .ld_trans_id_i        ( ld_trans_id           ),
        .ld_result_i          ( ld_result             ),
        .ld_ex_i              ( ld_ex                 ),

        .st_valid_i           ( st_valid              ),
        .st_trans_id_i        ( st_trans_id           ),
        .st_result_i          ( st_result             ),
        .st_ex_i              ( st_ex                 ),

        .valid_o              ( lsu_valid_o           ),
        .trans_id_o           ( lsu_trans_id_o        ),
        .result_o             ( lsu_result_o          ),
        .ex_o                 ( lsu_exception_o       )
    );

    // ------------------
    // LSU Control
    // ------------------
    always_comb begin : lsu_control
        // the LSU is ready if both, stores and loads are ready because we do not know
        // which of the two we are getting
        lsu_ready_o = ld_ready_o && st_ready_o;
        // "arbitrate" MMU access, there is only one request possible
        translation_req     = 1'b0;
        mmu_vaddr           = 64'b0;
        // this arbitrates access to the MMU
        if (st_translation_req) begin
            translation_req = 1'b1;
            mmu_vaddr       = st_vaddr;
        end else if (ld_translation_req) begin
            translation_req = 1'b1;
            mmu_vaddr       = ld_vaddr;
        end
    end

    enum logic {LD_OP, ST_OP} op;

    // determine whether this is a load or store
    always_comb begin : which_op

        ld_valid_i = 1'b0;
        st_valid_i = 1'b0;

        // only activate one of the units if we didn't got an misaligned exception
        // we can directly output an misaligned exception and do not need to process it any further
        if (!data_misaligned) begin
            // check the operator to activate the right functional unit accordingly
            unique case (operator)
                // all loads go here
                LD, LW, LWU, LH, LHU, LB, LBU:  begin
                    ld_valid_i = 1'b1;
                    op         = LD_OP;
                end
                // all stores go here
                SD, SW, SH, SB: begin
                    st_valid_i = 1'b1;
                    op         = ST_OP;
                end
                // not relevant for the LSU
                default: ;
            endcase
        end
    end


    // ---------------
    // Byte Enable
    // ---------------
    always_comb begin : byte_enable
        be_i = 8'b0;
        // we can generate the byte enable from the virtual address since the last
        // 12 bit are the same anyway
        // and we can always generate the byte enable from the address at hand
        case (operator_i)
            LD, SD: // double word
                    be_i = 8'b1111_1111;
            LW, LWU, SW: // word
                case (vaddr_i[2:0])
                    3'b000: be_i = 8'b0000_1111;
                    3'b001: be_i = 8'b0001_1110;
                    3'b010: be_i = 8'b0011_1100;
                    3'b011: be_i = 8'b0111_1000;
                    3'b100: be_i = 8'b1111_0000;
                    default:;
                endcase
            LH, LHU, SH: // half word
                case (vaddr_i[2:0])
                    3'b000: be_i = 8'b0000_0011;
                    3'b001: be_i = 8'b0000_0110;
                    3'b010: be_i = 8'b0000_1100;
                    3'b011: be_i = 8'b0001_1000;
                    3'b100: be_i = 8'b0011_0000;
                    3'b101: be_i = 8'b0110_0000;
                    3'b110: be_i = 8'b1100_0000;
                    default:;
                endcase
            LB, LBU, SB: // byte
                case (vaddr_i[2:0])
                    3'b000: be_i = 8'b0000_0001;
                    3'b001: be_i = 8'b0000_0010;
                    3'b010: be_i = 8'b0000_0100;
                    3'b011: be_i = 8'b0000_1000;
                    3'b100: be_i = 8'b0001_0000;
                    3'b101: be_i = 8'b0010_0000;
                    3'b110: be_i = 8'b0100_0000;
                    3'b111: be_i = 8'b1000_0000;
                endcase
            default:
                be_i = 8'b0;
        endcase
    end

    // ------------------------
    // Misaligned Exception
    // ------------------------
    // misaligned detector
    // we can detect a misaligned exception immediately
    // the misaligned exception is passed to the store buffer as a bypass
    // just a hack to get to the LSU arbiter
    always_comb begin : data_misaligned_detection

        misaligned_exception = {
            64'b0,
            64'b0,
            1'b0
        };

        data_misaligned = 1'b0;

        if(lsu_valid_i) begin
            case (operator_i)
                // double word
                LD, SD: begin
                    if (vaddr_i[2:0] != 3'b000)
                        data_misaligned = 1'b1;
                end
                // word
                LW, LWU, SW: begin
                    if (vaddr_i[2] == 1'b1 && vaddr_i[2:0] != 3'b100)
                        data_misaligned = 1'b1;
                end

                // half word
                LH, LHU, SH: begin
                    if (vaddr_i[2:0] == 3'b111)
                        data_misaligned = 1'b1;
                end
                // byte -> is always aligned
                default:;
            endcase
        end

        if (data_misaligned) begin

            if (op == LD_OP) begin
                misaligned_exception = {
                    64'b0,
                    LD_ADDR_MISALIGNED,
                    1'b1
                };

            end else if (op == ST_OP) begin
                misaligned_exception = {
                    64'b0,
                    ST_ADDR_MISALIGNED,
                    1'b1
                };
            end
        end
    end

    // this process selects the input based on the current state of the LSU
    // it can either be feedthrough from the issue stage or from the internal register
    always_comb begin : input_select
        // if we are stalling use the values we saved
        if (stall_q) begin
            vaddr     = vaddr_q;
            data      = data_q;
            operator  = operator_q;
            trans_id  = trans_id_q;
            be        = be_q;
        end else begin // otherwise bypass them
            vaddr     = vaddr_i;
            data      = operand_b_i;
            operator  = operator_i;
            trans_id  = trans_id_i;
            be        = be_i;
        end
    end
    // 1st register stage
    always_comb begin : register_stage
        vaddr_n     = vaddr_q;
        data_n      = data_q;
        operator_n  = operator_q;
        trans_id_n  = trans_id_q;
        be_n        = be_q;
        // get new input data
        if (lsu_valid_i) begin
             vaddr_n     = vaddr_i;
             data_n      = operand_b_i;
             operator_n  = operator_i;
             trans_id_n  = trans_id_i;
             be_n        = be_i;
        end

        if (lsu_ready_o) begin
            stall_n     = 1'b0;
        end else begin
            stall_n     = 1'b1;
        end
    end

    // registers
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (~rst_ni) begin
            // 1st LSU stage
            vaddr_q             <= 64'b0;
            data_q              <= 64'b0;
            operator_q          <= ADD;
            trans_id_q          <= '{default: 0};
            be_q                <= 8'b0;
            stall_q             <= 1'b0;
        end else begin
            // 1st LSU stage
            vaddr_q             <= vaddr_n;
            data_q              <= data_n;
            operator_q          <= operator_n;
            trans_id_q          <= trans_id_n;
            be_q                <= be_n;
            stall_q             <= stall_n;
        end
    end

    // ------------
    // Assertions
    // ------------

    // // make sure there is no new request when the old one is not yet completely done
    // // i.e. it should not be possible to get a grant without an rvalid for the
    // // last request
    `ifndef SYNTHESIS
    `ifndef VERILATOR
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

    // assert that errors are only sent at the same time as grant or rvalid
    // assert that we only get a valid in if we said that we are ready
    // assert property ( @(posedge clk_i) lsu_valid_i |->  lsu_ready_o)
    //   else begin $error("[LSU] We got a valid but didn't say we were ready."); $stop(); end

    // // assert that the address does not contain X when request is sent
    // assert property ( @(posedge clk) (data_req_o) |-> (!$isunknown(data_addr_o)) )
    //   else begin $error("address contains X when request is set"); $stop(); end
    `endif
    `endif
endmodule
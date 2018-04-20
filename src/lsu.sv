// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// Author: Florian Zaruba, ETH Zurich
// Date: 19.04.2017
// Description: Load Store Unit, handles address calculation and memory interface signals

import ariane_pkg::*;

module lsu #(
        parameter int unsigned ASID_WIDTH       = 1,
        parameter logic [63:0] CACHE_START_ADDR = 64'h4000_0000,
        parameter int unsigned AXI_ID_WIDTH     = 10,
        parameter int unsigned AXI_USER_WIDTH   = 1
)(
    input  logic                     clk_i,
    input  logic                     rst_ni,
    input  logic                     flush_i,
    output logic                     no_st_pending_o,

    input  fu_t                      fu_i,
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
    output logic                     commit_ready_o,           // commit queue is ready to accept another commit request

    input  logic                     enable_translation_i,     // enable virtual memory translation
    input  logic                     en_ld_st_translation_i,   // enable virtual memory translation for load/stores

    input  logic                     fetch_req_i,              // Instruction fetch interface
    input  logic [63:0]              fetch_vaddr_i,            // Instruction fetch interface
    output logic                     fetch_valid_o,            // Instruction fetch interface
    output logic [63:0]              fetch_paddr_o,            // Instruction fetch interface
    output exception_t               fetch_exception_o,        // Instruction fetch interface

    input  priv_lvl_t                priv_lvl_i,               // From CSR register file
    input  priv_lvl_t                ld_st_priv_lvl_i,         // From CSR register file
    input  logic                     sum_i,                    // From CSR register file
    input  logic                     mxr_i,                    // From CSR register file
    input  logic [43:0]              satp_ppn_i,               // From CSR register file
    input  logic [ASID_WIDTH-1:0]    asid_i,                   // From CSR register file
    input  logic                     flush_tlb_i,
    // Performance counters
    output logic                     itlb_miss_o,
    output logic                     dtlb_miss_o,
    output logic                     dcache_miss_o,

    input  logic                     dcache_en_i,
    input  logic                     flush_dcache_i,
    output logic                     flush_dcache_ack_o,
    // Data cache refill port
    AXI_BUS.Master                   data_if,
    AXI_BUS.Master                   bypass_if,

    output exception_t               lsu_exception_o   // to WB, signal exception status LD/ST exception

);
    // data is misaligned
    logic data_misaligned;
    // --------------------------------------
    // 1st register stage - (stall registers)
    // --------------------------------------
    // those are the signals which are always correct
    // e.g.: they keep the value in the stall case
    lsu_ctrl_t lsu_ctrl;

    logic      pop_st;
    logic      pop_ld;

    // Address Generation Unit (AGU)
    // ------------------------------
    // virtual address as calculated by the AGU in the first cycle
    logic [63:0] vaddr_i;
    logic [7:0]  be_i;

    assign vaddr_i = $unsigned($signed(imm_i) + $signed(operand_a_i));

    logic                     st_valid_i;
    logic                     ld_valid_i;
    logic                     ld_translation_req;
    logic                     st_translation_req;
    logic [63:0]              ld_vaddr;
    logic [63:0]              st_vaddr;
    logic                     translation_req;
    logic                     translation_valid;
    logic [63:0]              mmu_vaddr;
    logic [63:0]              mmu_paddr;
    exception_t               mmu_exception;
    logic                     dtlb_hit;

    logic                     ld_valid;
    logic [TRANS_ID_BITS-1:0] ld_trans_id;
    logic [63:0]              ld_result;
    logic                     st_valid;
    logic [TRANS_ID_BITS-1:0] st_trans_id;
    logic [63:0]              st_result;

    logic [11:0]              page_offset;
    logic                     page_offset_matches;

    exception_t               misaligned_exception;
    exception_t               ld_ex;
    exception_t               st_ex;

    // ------------
    // NB Dcache
    // ------------
    logic [2:0][11:0]         address_index_i;
    logic [2:0][43:0]         address_tag_i;
    logic [2:0][63:0]         data_wdata_i;
    logic [2:0]               data_req_i;
    logic [2:0]               data_we_i;
    logic [2:0][1:0]          data_size_i;

    logic [2:0]               kill_req_i;
    logic [2:0]               tag_valid_i;
    logic [2:0][7:0]          data_be_i;
    logic [2:0]               data_gnt_o;
    logic [2:0]               data_rvalid_o;
    logic [2:0][63:0]         data_rdata_o;
    amo_t [2:0]               amo_op_i;

    // AMO operations always go through the load unit
    assign amo_op_i[0] = AMO_NONE;
    assign amo_op_i[2] = AMO_NONE;

    // decreasing priority
    // Port 0: PTW
    // Port 1: Load Unit
    // Port 2: Store Unit
    nbdcache #(
        .CACHE_START_ADDR ( CACHE_START_ADDR ),
        .AXI_ID_WIDTH     ( AXI_ID_WIDTH     ),
        .AXI_USER_WIDTH   ( AXI_USER_WIDTH   )
    ) i_nbdcache (
        // to D$
        .data_if           ( data_if                 ),
        .bypass_if         ( bypass_if               ),
        .enable_i          ( dcache_en_i             ),
        .flush_i           ( flush_dcache_i          ),
        .flush_ack_o       ( flush_dcache_ack_o      ),
        // from PTW, Load Unit and Store Unit
        .address_index_i   ( address_index_i         ),
        .address_tag_i     ( address_tag_i           ),
        .data_wdata_i      ( data_wdata_i            ),
        .data_req_i        ( data_req_i              ),
        .data_we_i         ( data_we_i               ),
        .data_be_i         ( data_be_i               ),
        .data_size_i       ( data_size_i             ),
        .kill_req_i        ( kill_req_i              ),
        .tag_valid_i       ( tag_valid_i             ),
        .data_gnt_o        ( data_gnt_o              ),
        .data_rvalid_o     ( data_rvalid_o           ),
        .data_rdata_o      ( data_rdata_o            ),
        .amo_op_i          ( amo_op_i                ),

        .amo_commit_i      (                         ),
        .amo_valid_o       (                         ),
        .amo_result_o      (                         ),
        .amo_flush_i       ( 1'b0                    ),
        .miss_o            ( dcache_miss_o           ),
        .*
    );

    // -------------------
    // MMU e.g.: TLBs/PTW
    // -------------------
    mmu #(
        .INSTR_TLB_ENTRIES      ( 16                   ),
        .DATA_TLB_ENTRIES       ( 16                   ),
        .ASID_WIDTH             ( ASID_WIDTH           )
    ) i_mmu (
            // misaligned bypass
        .misaligned_ex_i        ( misaligned_exception ),
        .lsu_is_store_i         ( st_translation_req   ),
        .lsu_req_i              ( translation_req      ),
        .lsu_vaddr_i            ( mmu_vaddr            ),
        .lsu_valid_o            ( translation_valid    ),
        .lsu_paddr_o            ( mmu_paddr            ),
        .lsu_exception_o        ( mmu_exception        ),
        .lsu_dtlb_hit_o         ( dtlb_hit             ), // send in the same cycle as the request
        // connecting PTW to D$ IF (aka mem arbiter
        .address_index_o        ( address_index_i  [0] ),
        .address_tag_o          ( address_tag_i    [0] ),
        .data_wdata_o           ( data_wdata_i     [0] ),
        .data_req_o             ( data_req_i       [0] ),
        .data_we_o              ( data_we_i        [0] ),
        .data_be_o              ( data_be_i        [0] ),
        .data_size_o            ( data_size_i      [0] ),
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
    store_unit i_store_unit (
        .valid_i               ( st_valid_i           ),
        .lsu_ctrl_i            ( lsu_ctrl             ),
        .pop_st_o              ( pop_st               ),

        .valid_o               ( st_valid             ),
        .trans_id_o            ( st_trans_id          ),
        .result_o              ( st_result            ),
        .ex_o                  ( st_ex                ),
        // MMU port
        .translation_req_o     ( st_translation_req   ),
        .vaddr_o               ( st_vaddr             ),
        .paddr_i               ( mmu_paddr            ),
        .ex_i                  ( mmu_exception        ),
        .dtlb_hit_i            ( dtlb_hit             ),
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
        .data_size_o           ( data_size_i      [2] ),
        .kill_req_o            ( kill_req_i       [2] ),
        .tag_valid_o           ( tag_valid_i      [2] ),
        .data_gnt_i            ( data_gnt_o       [2] ),
        .data_rvalid_i         ( data_rvalid_o    [2] ),
        .*
    );

    // ------------------
    // Load Unit
    // ------------------
    load_unit i_load_unit (
        .valid_i               ( ld_valid_i           ),
        .lsu_ctrl_i            ( lsu_ctrl             ),
        .pop_ld_o              ( pop_ld               ),

        .valid_o               ( ld_valid             ),
        .trans_id_o            ( ld_trans_id          ),
        .result_o              ( ld_result            ),
        .ex_o                  ( ld_ex                ),
        // MMU port
        .translation_req_o     ( ld_translation_req   ),
        .vaddr_o               ( ld_vaddr             ),
        .paddr_i               ( mmu_paddr            ),
        .ex_i                  ( mmu_exception        ),
        .dtlb_hit_i            ( dtlb_hit             ),
        // to store unit
        .page_offset_o         ( page_offset          ),
        .page_offset_matches_i ( page_offset_matches  ),
        // to memory arbiter
        .address_index_o       ( address_index_i  [1] ),
        .address_tag_o         ( address_tag_i    [1] ),
        .data_wdata_o          ( data_wdata_i     [1] ),
        .amo_op_o              ( amo_op_i         [1] ),
        .data_req_o            ( data_req_i       [1] ),
        .data_we_o             ( data_we_i        [1] ),
        .data_be_o             ( data_be_i        [1] ),
        .data_size_o           ( data_size_i      [1] ),
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
    lsu_arbiter i_lsu_arbiter (
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

    // determine whether this is a load or store
    always_comb begin : which_op

        ld_valid_i = 1'b0;
        st_valid_i = 1'b0;

        translation_req      = 1'b0;
        mmu_vaddr            = 64'b0;

        // check the operator to activate the right functional unit accordingly
        unique case (lsu_ctrl.fu)
            // all loads go here
            LOAD:  begin
                ld_valid_i           = lsu_ctrl.valid;
                translation_req      = ld_translation_req;
                mmu_vaddr            = ld_vaddr;
            end
            // all stores go here
            STORE: begin
                st_valid_i           = lsu_ctrl.valid;
                translation_req      = st_translation_req;
                mmu_vaddr            = st_vaddr;
            end
            // not relevant for the LSU
            default: ;
        endcase
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
            LD, SD, FLD, FSD: // double word
                    be_i = 8'b1111_1111;
            LW, LWU, SW, FLW, FSW: // word
                case (vaddr_i[2:0])
                    3'b000: be_i = 8'b0000_1111;
                    3'b001: be_i = 8'b0001_1110;
                    3'b010: be_i = 8'b0011_1100;
                    3'b011: be_i = 8'b0111_1000;
                    3'b100: be_i = 8'b1111_0000;
                    default:;
                endcase
            LH, LHU, SH, FLH, FSH: // half word
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
            LB, LBU, SB, FLB, FSB: // byte
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
    // we can detect a misaligned exception immediately
    // the misaligned exception is passed to the functional unit via the MMU, which in case
    // can augment the exception if other memory related exceptions like a page fault or access errors
    always_comb begin : data_misaligned_detection

        misaligned_exception = {
            64'b0,
            64'b0,
            1'b0
        };

        data_misaligned = 1'b0;

        if(lsu_ctrl.valid) begin
            case (lsu_ctrl.operator)
                // double word
                LD, SD, FLD, FSD: begin
                    if (lsu_ctrl.vaddr[2:0] != 3'b000)
                        data_misaligned = 1'b1;
                end
                // word
                LW, LWU, SW, FLW, FSW: begin
                    if (lsu_ctrl.vaddr[1:0] != 2'b00)
                        data_misaligned = 1'b1;
                end

                // half word
                LH, LHU, SH, FLH, FSH: begin
                    if (lsu_ctrl.vaddr[0] != 1'b0)
                        data_misaligned = 1'b1;
                end
                // byte -> is always aligned
                default:;
            endcase
        end

        if (data_misaligned) begin

            if (lsu_ctrl.fu == LOAD) begin
                misaligned_exception = {
                    LD_ADDR_MISALIGNED,
                    lsu_ctrl.vaddr,
                    1'b1
                };

            end else if (lsu_ctrl.fu == STORE) begin
                misaligned_exception = {
                    ST_ADDR_MISALIGNED,
                    lsu_ctrl.vaddr,
                    1'b1
                };
            end
        end

        // check that all bits in the address >= 39 are equal
        if (!((&lsu_ctrl.vaddr[63:39]) == 1'b1 || (|lsu_ctrl.vaddr[63:39]) == 1'b0)) begin

            if (lsu_ctrl.fu == LOAD) begin
                misaligned_exception = {
                    LOAD_PAGE_FAULT,
                    lsu_ctrl.vaddr,
                    1'b1
                };

            end else if (lsu_ctrl.fu == STORE) begin
                misaligned_exception = {
                    STORE_PAGE_FAULT,
                    lsu_ctrl.vaddr,
                    1'b1
                };
            end
        end
    end

    // ------------------
    // LSU Control
    // ------------------
    // new data arrives here
    lsu_ctrl_t lsu_req_i;

    assign lsu_req_i = {lsu_valid_i, vaddr_i, operand_b_i, be_i, fu_i, operator_i, trans_id_i};

    lsu_bypass lsu_bypass_i (
        .lsu_req_i          ( lsu_req_i   ),
        .lus_req_valid_i    ( lsu_valid_i ),
        .pop_ld_i           ( pop_ld      ),
        .pop_st_i           ( pop_st      ),

        .lsu_ctrl_o         ( lsu_ctrl    ),
        .ready_o            ( lsu_ready_o ),
        .*
    );
    // ------------
    // Assertions
    // ------------

    `ifndef SYNTHESIS
    `ifndef VERILATOR
    // TODO
    `endif
    `endif
endmodule

// ------------------
// LSU Control
// ------------------
// The LSU consists of two independent block which share a common address translation block.
// The one block is the load unit, the other one is the store unit. They will signal their readiness
// with separate signals. If they are not ready the LSU control should keep the last applied signals stable.
// Furthermore it can be the case that another request for one of the two store units arrives in which case
// the LSU control should sample it and store it for later application to the units. It does so, by storing it in a
// two element FIFO. This is necessary as we only know very late in the cycle whether the load/store will succeed (address check,
// TLB hit mainly). So we better unconditionally allow another request to arrive and store this request in case we need to.
module lsu_bypass (
    input  logic      clk_i,
    input  logic      rst_ni,
    input  logic      flush_i,

    input  lsu_ctrl_t lsu_req_i,
    input  logic      lus_req_valid_i,
    input  logic      pop_ld_i,
    input  logic      pop_st_i,

    output lsu_ctrl_t lsu_ctrl_o,
    output logic      ready_o
    );

    lsu_ctrl_t [1:0] mem_n, mem_q;
    logic read_pointer_n, read_pointer_q;
    logic write_pointer_n, write_pointer_q;
    logic [1:0] status_cnt_n, status_cnt_q;

    logic  empty;
    assign empty = (status_cnt_q == 0);
    assign ready_o = empty;

    always_comb begin
        automatic logic [1:0] status_cnt;
        automatic logic write_pointer;
        automatic logic read_pointer;

        status_cnt = status_cnt_q;
        write_pointer = write_pointer_q;
        read_pointer = read_pointer_q;

        mem_n = mem_q;
        // we've got a valid LSU request
        if (lus_req_valid_i) begin
            mem_n[write_pointer_q] = lsu_req_i;
            write_pointer++;
            status_cnt++;
        end

        if (pop_ld_i) begin
            // invalidate the result
            mem_n[read_pointer_q].valid = 1'b0;
            read_pointer++;
            status_cnt--;
        end

        if (pop_st_i) begin
            // invalidate the result
            mem_n[read_pointer_q].valid = 1'b0;
            read_pointer++;
            status_cnt--;
        end

        if (pop_st_i && pop_ld_i)
            mem_n = '{default: 0};

        if (flush_i) begin
            status_cnt = '0;
            write_pointer = '0;
            read_pointer = '0;
            mem_n = '{default: 0};
        end
        // default assignments
        read_pointer_n  = read_pointer;
        write_pointer_n = write_pointer;
        status_cnt_n    = status_cnt;
    end

    // output assignment
    always_comb begin : output_assignments
        if (empty) begin
            lsu_ctrl_o = lsu_req_i;
        end else begin
            lsu_ctrl_o = mem_q[read_pointer_q];
        end
    end

    // registers
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if(~rst_ni) begin
            mem_q           <= '{default: 0};
            status_cnt_q    <= '0;
            write_pointer_q <= '0;
            read_pointer_q  <= '0;
        end else begin
            mem_q           <= mem_n;
            status_cnt_q    <= status_cnt_n;
            write_pointer_q <= write_pointer_n;
            read_pointer_q  <= read_pointer_n;
        end
    end
endmodule


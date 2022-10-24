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
// Date: 22.05.2017
// Description: Store Unit, takes care of all store requests and atomic memory operations (AMOs)


module store_unit import ariane_pkg::*; (
    input  logic                     clk_i,    // Clock
    input  logic                     rst_ni,  // Asynchronous reset active low
    input  logic                     flush_i,
    output logic                     no_st_pending_o,
    output logic                     store_buffer_empty_o,
    // store unit input port
    input  logic                     valid_i,
    input  lsu_ctrl_t                lsu_ctrl_i,
    output logic                     pop_st_o,
    input  logic                     commit_i,
    output logic                     commit_ready_o,
    input  logic                     amo_valid_commit_i,
    // store unit output port
    output logic                     valid_o,
    output logic [TRANS_ID_BITS-1:0] trans_id_o,
    output riscv::xlen_t             result_o,
    output exception_t               ex_o,
    // MMU -> Address Translation
    output logic                     translation_req_o, // request address translation
    output logic [riscv::VLEN-1:0]   vaddr_o,           // virtual address out
    input  logic [riscv::PLEN-1:0]   paddr_i,           // physical address in
    input  exception_t               ex_i,
    input  logic                     dtlb_hit_i,       // will be one in the same cycle translation_req was asserted if it hits
    // address checker
    input  logic [11:0]              page_offset_i,
    output logic                     page_offset_matches_o,
    // D$ interface
    output amo_req_t                 amo_req_o,
    input  amo_resp_t                amo_resp_i,
    input  dcache_req_o_t            req_port_i,
    output dcache_req_i_t            req_port_o
);
    // it doesn't matter what we are writing back as stores don't return anything
    assign result_o = lsu_ctrl_i.data;

    enum logic [1:0] {
        IDLE,
        VALID_STORE,
        WAIT_TRANSLATION,
        WAIT_STORE_READY
    } state_d, state_q;

    // store buffer control signals
    logic st_ready;
    logic st_valid;
    logic st_valid_without_flush;
    logic instr_is_amo;
    assign instr_is_amo = is_amo(lsu_ctrl_i.operator);
    // keep the data and the byte enable for the second cycle (after address translation)
    riscv::xlen_t st_data_n, st_data_q;
    logic [(riscv::XLEN/8)-1:0]   st_be_n,        st_be_q;
    logic [1:0]   st_data_size_n, st_data_size_q;
    amo_t         amo_op_d,       amo_op_q;

    logic [TRANS_ID_BITS-1:0] trans_id_n, trans_id_q;

    // output assignments
    assign vaddr_o    = lsu_ctrl_i.vaddr; // virtual address
    assign trans_id_o = trans_id_q; // transaction id from previous cycle

    always_comb begin : store_control
        translation_req_o      = 1'b0;
        valid_o                = 1'b0;
        st_valid               = 1'b0;
        st_valid_without_flush = 1'b0;
        pop_st_o               = 1'b0;
        ex_o                   = ex_i;
        trans_id_n             = lsu_ctrl_i.trans_id;
        state_d                     = state_q;

        case (state_q)
            // we got a valid store
            IDLE: begin
                if (valid_i) begin
                    state_d = VALID_STORE;
                    translation_req_o = 1'b1;
                    pop_st_o = 1'b1;
                    // check if translation was valid and we have space in the store buffer
                    // otherwise simply stall
                    if (!dtlb_hit_i) begin
                        state_d = WAIT_TRANSLATION;
                        pop_st_o = 1'b0;
                    end

                    if (!st_ready) begin
                        state_d = WAIT_STORE_READY;
                        pop_st_o = 1'b0;
                    end
                end
            end

            VALID_STORE: begin
                valid_o  = 1'b1;
                // post this store to the store buffer if we are not flushing
                if (!flush_i)
                    st_valid = 1'b1;

                st_valid_without_flush = 1'b1;

                // we have another request and its not an AMO (the AMO buffer only has depth 1)
                if (valid_i && !instr_is_amo) begin

                    translation_req_o = 1'b1;
                    state_d = VALID_STORE;
                    pop_st_o = 1'b1;

                    if (!dtlb_hit_i) begin
                        state_d = WAIT_TRANSLATION;
                        pop_st_o = 1'b0;
                    end

                    if (!st_ready) begin
                        state_d = WAIT_STORE_READY;
                        pop_st_o = 1'b0;
                    end
                // if we do not have another request go back to idle
                end else begin
                    state_d = IDLE;
                end
            end

            // the store queue is currently full
            WAIT_STORE_READY: begin
                // keep the translation request high
                translation_req_o = 1'b1;

                if (st_ready && dtlb_hit_i) begin
                    state_d = IDLE;
                end
            end

            // we didn't receive a valid translation, wait for one
            // but we know that the store queue is not full as we could only have landed here if
            // it wasn't full
            WAIT_TRANSLATION: begin
                translation_req_o = 1'b1;

                if (dtlb_hit_i) begin
                    state_d = IDLE;
                end
            end
        endcase

        // -----------------
        // Access Exception
        // -----------------
        // we got an address translation exception (access rights, misaligned or page fault)
        if (ex_i.valid && (state_q != IDLE)) begin
            // the only difference is that we do not want to store this request
            pop_st_o = 1'b1;
            st_valid = 1'b0;
            state_d  = IDLE;
            valid_o  = 1'b1;
        end

        if (flush_i)
            state_d = IDLE;
    end

    // -----------
    // Re-aligner
    // -----------
    // re-align the write data to comply with the address offset
    always_comb begin
        st_be_n   = lsu_ctrl_i.be;
        // don't shift the data if we are going to perform an AMO as we still need to operate on this data
        st_data_n = instr_is_amo ? lsu_ctrl_i.data[riscv::XLEN-1:0]
                                 : data_align(lsu_ctrl_i.vaddr[2:0], lsu_ctrl_i.data);
        st_data_size_n = extract_transfer_size(lsu_ctrl_i.operator);
        // save AMO op for next cycle
        case (lsu_ctrl_i.operator)
            AMO_LRW, AMO_LRD:     amo_op_d = AMO_LR;
            AMO_SCW, AMO_SCD:     amo_op_d = AMO_SC;
            AMO_SWAPW, AMO_SWAPD: amo_op_d = AMO_SWAP;
            AMO_ADDW, AMO_ADDD:   amo_op_d = AMO_ADD;
            AMO_ANDW, AMO_ANDD:   amo_op_d = AMO_AND;
            AMO_ORW, AMO_ORD:     amo_op_d = AMO_OR;
            AMO_XORW, AMO_XORD:   amo_op_d = AMO_XOR;
            AMO_MAXW, AMO_MAXD:   amo_op_d = AMO_MAX;
            AMO_MAXWU, AMO_MAXDU: amo_op_d = AMO_MAXU;
            AMO_MINW, AMO_MIND:   amo_op_d = AMO_MIN;
            AMO_MINWU, AMO_MINDU: amo_op_d = AMO_MINU;
            default: amo_op_d = AMO_NONE;
        endcase
    end

    logic store_buffer_valid, amo_buffer_valid;
    logic store_buffer_ready, amo_buffer_ready;

    // multiplex between store unit and amo buffer
    assign store_buffer_valid = st_valid & (amo_op_q == AMO_NONE);
    assign amo_buffer_valid = st_valid & (amo_op_q != AMO_NONE);

    assign st_ready = store_buffer_ready & amo_buffer_ready;

    // ---------------
    // Store Queue
    // ---------------
    store_buffer store_buffer_i (
        .clk_i,
        .rst_ni,
        .flush_i,
        .no_st_pending_o,
        .store_buffer_empty_o,
        .page_offset_i,
        .page_offset_matches_o,
        .commit_i,
        .commit_ready_o,
        .ready_o               ( store_buffer_ready     ),
        .valid_i               ( store_buffer_valid     ),
        // the flush signal can be critical and we need this valid
        // signal to check whether the page_offset matches or not,
        // functionaly it doesn't make a difference whether we use
        // the correct valid signal or not as we are flushing
        // the whole pipeline anyway
        .valid_without_flush_i ( st_valid_without_flush ),
        .paddr_i,
        .data_i                ( st_data_q              ),
        .be_i                  ( st_be_q                ),
        .data_size_i           ( st_data_size_q         ),
        .req_port_i            ( req_port_i             ),
        .req_port_o            ( req_port_o             )
    );

    amo_buffer i_amo_buffer (
        .clk_i,
        .rst_ni,
        .flush_i,
        .valid_i            ( amo_buffer_valid   ),
        .ready_o            ( amo_buffer_ready   ),
        .paddr_i            ( paddr_i            ),
        .amo_op_i           ( amo_op_q           ),
        .data_i             ( st_data_q          ),
        .data_size_i        ( st_data_size_q     ),
        .amo_req_o          ( amo_req_o          ),
        .amo_resp_i         ( amo_resp_i         ),
        .amo_valid_commit_i ( amo_valid_commit_i ),
        .no_st_pending_i    ( no_st_pending_o    )
    );

    // ---------------
    // Registers
    // ---------------
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (~rst_ni) begin
            state_q             <= IDLE;
            st_be_q        <= '0;
            st_data_q      <= '0;
            st_data_size_q <= '0;
            trans_id_q     <= '0;
            amo_op_q       <= AMO_NONE;
        end else begin
            state_q        <= state_d;
            st_be_q        <= st_be_n;
            st_data_q      <= st_data_n;
            trans_id_q     <= trans_id_n;
            st_data_size_q <= st_data_size_n;
            amo_op_q       <= amo_op_d;
        end
    end

endmodule

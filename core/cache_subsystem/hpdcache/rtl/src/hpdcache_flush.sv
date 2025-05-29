/*
 *  Copyright 2024 CEA*
 *  *Commissariat a l'Energie Atomique et aux Energies Alternatives (CEA)
 *
 *  SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
 *
 *  Licensed under the Solderpad Hardware License v 2.1 (the “License”); you
 *  may not use this file except in compliance with the License, or, at your
 *  option, the Apache License version 2.0. You may obtain a copy of the
 *  License at
 *
 *  https://solderpad.org/licenses/SHL-2.1/
 *
 *  Unless required by applicable law or agreed to in writing, any work
 *  distributed under the License is distributed on an “AS IS” BASIS, WITHOUT
 *  WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the
 *  License for the specific language governing permissions and limitations
 *  under the License.
 */
/*
 *  Authors       : Cesar Fuguet
 *  Creation Date : September, 2024
 *  Description   : HPDcache Flush Controller
 *  History       :
 */
module hpdcache_flush
//  {{{
import hpdcache_pkg::*;
//  Parameters
//  {{{
#(
    parameter hpdcache_cfg_t HPDcacheCfg = '0,

    parameter type hpdcache_nline_t = logic,
    parameter type hpdcache_set_t = logic,
    parameter type hpdcache_word_t = logic,
    parameter type hpdcache_way_vector_t = logic,

    parameter type hpdcache_access_data_t = logic,

    parameter type hpdcache_mem_id_t = logic,
    parameter type hpdcache_mem_data_t = logic,
    parameter type hpdcache_mem_req_t = logic,
    parameter type hpdcache_mem_req_w_t = logic,
    parameter type hpdcache_mem_resp_w_t = logic
)
//  }}}

//  Ports
//  {{{
(
    input  logic                  clk_i,
    input  logic                  rst_ni,

    //      Global control signals
    //      {{{
    output logic                  flush_empty_o,
    output logic                  flush_full_o,
    output logic                  flush_busy_o,
    //      }}}

    //      CHECK interface
    //      {{{
    input  hpdcache_nline_t       flush_check_nline_i,
    output logic                  flush_check_hit_o,
    //      }}}

    //      ALLOC interface
    //      {{{
    input  logic                  flush_alloc_i,
    output logic                  flush_alloc_ready_o,
    input  hpdcache_nline_t       flush_alloc_nline_i,
    input  hpdcache_way_vector_t  flush_alloc_way_i,
    //      }}}

    //      CACHE DATA interface
    //      {{{
    output logic                  flush_data_read_o,
    output hpdcache_set_t         flush_data_read_set_o,
    output hpdcache_word_t        flush_data_read_word_o,
    output hpdcache_way_vector_t  flush_data_read_way_o,
    input  hpdcache_access_data_t flush_data_read_data_i,
    //      }}}

    //      ACK monitoring interface
    //      {{{
    output logic                  flush_ack_o,
    output hpdcache_nline_t       flush_ack_nline_o,
    //      }}}

    //      MEMORY interface
    //      {{{
    input  logic                  mem_req_write_ready_i,
    output logic                  mem_req_write_valid_o,
    output hpdcache_mem_req_t     mem_req_write_o,

    input  logic                  mem_req_write_data_ready_i,
    output logic                  mem_req_write_data_valid_o,
    output hpdcache_mem_req_w_t   mem_req_write_data_o,

    output logic                  mem_resp_write_ready_o,
    input  logic                  mem_resp_write_valid_i,
    input  hpdcache_mem_resp_w_t  mem_resp_write_i
    //      }}}
);

    //  Definition of constants and types
    //  {{{
    localparam int unsigned FlushEntries = HPDcacheCfg.u.flushEntries;
    localparam int unsigned FlushIndexWidth = (FlushEntries > 1) ? $clog2(FlushEntries) : 1;

    typedef struct packed {
        hpdcache_nline_t nline;
    } flush_entry_t;

    typedef flush_entry_t [FlushEntries-1:0] flush_dir_t;
    typedef logic [FlushIndexWidth-1:0] flush_dir_index_t;

    typedef enum {
        FLUSH_IDLE,
        FLUSH_SEND
    } flush_fsm_e;
    //  }}}

    //  Definition of internal signals and registers
    //  {{{
    logic [FlushEntries-1:0] flush_dir_valid_q;
    flush_dir_t              flush_dir_q;
    flush_dir_index_t        flush_dir_free_ptr;
    logic [FlushEntries-1:0] flush_dir_free_bv;
    logic [FlushEntries-1:0] flush_dir_alloc_bv;
    flush_dir_index_t        flush_dir_ack_ptr;
    logic [FlushEntries-1:0] flush_dir_ack_bv;
    hpdcache_set_t           flush_set_q;
    hpdcache_way_vector_t    flush_way_q;
    hpdcache_word_t          flush_word_q, flush_word_d;
    flush_fsm_e              flush_fsm_q, flush_fsm_d;

    logic                    flush_eol;
    logic                    flush_alloc;
    hpdcache_set_t           flush_alloc_set;
    logic                    flush_ack;
    logic                    flush_resizer_w, flush_resizer_wok;
    logic                    flush_resizer_wlast;

    logic                    flush_mem_req_w, flush_mem_req_wok;
    hpdcache_mem_req_t       flush_mem_req_wmeta;
    hpdcache_mem_data_t      flush_mem_req_rdata;
    logic                    flush_mem_req_rlast;

    logic [FlushEntries-1:0] flush_check_hit;

    genvar                   gen_i;
    //  }}}

    //  Flush FSM
    //  {{{
    assign flush_full_o =  (&flush_dir_valid_q);
    assign flush_empty_o = ~(|flush_dir_valid_q);
    assign flush_busy_o = (flush_fsm_q != FLUSH_IDLE);
    assign flush_alloc_set = flush_alloc_nline_i[0 +: HPDcacheCfg.setWidth];

    //    End Of cache Line (EOL)
    //    This signal is used to determine when the entire cacheline has been flushed (read from the
    //    cache and written into the resizer).
    //    Here we make the assumption that the number of cacheline words is a power of 2.
    assign flush_eol = (flush_word_q == 0);

    assign flush_alloc_ready_o = (flush_fsm_q == FLUSH_IDLE)
                               & flush_resizer_wok
                               & flush_mem_req_wok
                               & ~flush_full_o;

    always_comb
    begin : flush_fsm_comb
        flush_fsm_d = flush_fsm_q;
        flush_word_d = flush_word_q;

        flush_alloc = 1'b0;

        flush_data_read_o = 1'b0;
        flush_data_read_set_o = flush_set_q;
        flush_data_read_word_o = flush_word_q;
        flush_data_read_way_o = flush_way_q;

        flush_mem_req_w = 1'b0;

        flush_resizer_w = 1'b0;
        flush_resizer_wlast = 1'b0;

        unique case (flush_fsm_q)
            FLUSH_IDLE: begin
                flush_mem_req_w = flush_resizer_wok & ~flush_full_o & flush_alloc_i;
                if (flush_alloc_i && flush_alloc_ready_o) begin
                    flush_data_read_o = 1'b1;
                    flush_data_read_set_o = flush_alloc_set;
                    flush_data_read_way_o = flush_alloc_way_i;
                    flush_data_read_word_o = 0;

                    flush_alloc = 1'b1;
                    flush_word_d = flush_word_q + hpdcache_word_t'(HPDcacheCfg.u.accessWords);
                    flush_fsm_d = FLUSH_SEND;
                end
            end
            FLUSH_SEND: begin
                flush_resizer_w = 1'b1;
                flush_resizer_wlast = flush_eol;
                if (flush_resizer_wok) begin
                    flush_data_read_o = ~flush_eol;
                    if (flush_eol) begin
                        flush_fsm_d = FLUSH_IDLE;
                    end else begin
                        flush_word_d = flush_word_q + hpdcache_word_t'(HPDcacheCfg.u.accessWords);
                    end
                end
            end
        endcase
    end

    //  Acknowledgement interface
    assign flush_ack = mem_resp_write_valid_i;
    assign flush_dir_ack_ptr = flush_dir_index_t'(mem_resp_write_i.mem_resp_w_id);
    assign mem_resp_write_ready_o = 1'b1;

    assign flush_ack_o = flush_ack;
    assign flush_ack_nline_o = flush_dir_q[flush_dir_ack_ptr].nline;
    //  }}}

    //  Check logic
    //  {{{
    for (gen_i = 0; gen_i < FlushEntries; gen_i++) begin : gen_check
        assign flush_check_hit[gen_i] = (flush_check_nline_i == flush_dir_q[gen_i].nline);
    end
    assign flush_check_hit_o = |(flush_dir_valid_q & ~flush_dir_ack_bv & flush_check_hit);
    //  }}}

    //  Internal state
    //  {{{

    //  FSM
    always_ff @(posedge clk_i or negedge rst_ni)
    begin : flush_fsm_ff
        if (!rst_ni) begin
            flush_fsm_q   <= FLUSH_IDLE;
            flush_word_q  <= '0;
        end else begin
            flush_fsm_q   <= flush_fsm_d;
            flush_word_q  <= flush_word_d;
        end
    end

    //  Directory valid
    assign flush_dir_alloc_bv = flush_dir_free_bv & {FlushEntries{flush_alloc}};

    always_ff @(posedge clk_i or negedge rst_ni)
    begin : flush_dir_valid_ff
        if (!rst_ni) begin
            flush_dir_valid_q <= '0;
        end else begin
            flush_dir_valid_q <= (~flush_dir_valid_q &  flush_dir_alloc_bv) |
                                 ( flush_dir_valid_q & ~flush_dir_ack_bv  );
        end
    end
    //  }}}

    //  Buffers
    always_ff @(posedge clk_i)
    begin : flush_dir_ff
        if (flush_alloc) begin
            flush_dir_q[flush_dir_free_ptr] <= '{
                nline: flush_alloc_nline_i
            };
            flush_set_q <= flush_alloc_set;
            flush_way_q <= flush_alloc_way_i;
        end
    end
    //  }}}

    //  Internal components
    //  {{{
    hpdcache_decoder #(.N(FlushIndexWidth)) flush_ack_decoder_i(
        .en_i           (flush_ack),
        .val_i          (flush_dir_ack_ptr),
        .val_o          (flush_dir_ack_bv)
    );

    //  Select a free entry in the flush directory
    //
    hpdcache_fxarb #(.N(FlushEntries)) flush_dir_free_arb_i(
        .clk_i,
        .rst_ni,
        .req_i          (~flush_dir_valid_q),
        .gnt_o          (flush_dir_free_bv),
        .ready_i        (flush_alloc)
    );
    hpdcache_1hot_to_binary #(.N (FlushEntries)) flush_dir_free_ptr_bin_i(
        .val_i          (flush_dir_free_bv),
        .val_o          (flush_dir_free_ptr)
    );

    //  FIFO for memory request metadata
    //
    localparam hpdcache_uint32 MemReqFlits = HPDcacheCfg.u.memDataWidth < HPDcacheCfg.clWidth ?
        (HPDcacheCfg.clWidth / HPDcacheCfg.u.memDataWidth) - 1 : 0;

    assign flush_mem_req_wmeta = '{
        mem_req_addr: {flush_alloc_nline_i, {HPDcacheCfg.clOffsetWidth{1'b0}} },
        mem_req_len: hpdcache_mem_len_t'(MemReqFlits),
        mem_req_size: get_hpdcache_mem_size(HPDcacheCfg.u.memDataWidth/8),
        mem_req_id: hpdcache_mem_id_t'(flush_dir_free_ptr),
        mem_req_command: HPDCACHE_MEM_WRITE,
        mem_req_atomic: HPDCACHE_MEM_ATOMIC_ADD, /* NOP */
        mem_req_cacheable: 1'b1
    };
    hpdcache_fifo_reg #(
        .FIFO_DEPTH     (2),
        .FEEDTHROUGH    (1'b0),
        .fifo_data_t    (hpdcache_mem_req_t)
    ) mem_req_meta_fifo_i(
        .clk_i,
        .rst_ni,
        .w_i            (flush_mem_req_w),
        .wok_o          (flush_mem_req_wok),
        .wdata_i        (flush_mem_req_wmeta),
        .r_i            (mem_req_write_ready_i),
        .rok_o          (mem_req_write_valid_o),
        .rdata_o        (mem_req_write_o)
    );

    //  Resize data width from the cache controller to the NoC data width
    //
    hpdcache_data_resize #(
        .WR_WIDTH       (HPDcacheCfg.accessWidth),
        .RD_WIDTH       (HPDcacheCfg.u.memDataWidth),
        .DEPTH          (HPDcacheCfg.u.flushFifoDepth)
    ) flush_data_resizer_i(
        .clk_i,
        .rst_ni,

        .w_i            (flush_resizer_w),
        .wok_o          (flush_resizer_wok),
        .wdata_i        (flush_data_read_data_i),
        .wlast_i        (flush_resizer_wlast),

        .r_i            (mem_req_write_data_ready_i),
        .rok_o          (mem_req_write_data_valid_o),
        .rdata_o        (flush_mem_req_rdata),
        .rlast_o        (/* open */)
    );


    //  Logic to detect the end of a packet
    //
    hpdcache_mem_len_t write_flits_cnt_q;

    assign flush_mem_req_rlast = (hpdcache_uint32'(write_flits_cnt_q) == MemReqFlits);

    always_ff @(posedge clk_i or negedge rst_ni)
    begin
        if (!rst_ni) begin
            write_flits_cnt_q <= 0;
        end else begin
            if (mem_req_write_data_valid_o && mem_req_write_data_ready_i) begin
                if (flush_mem_req_rlast) begin
                    write_flits_cnt_q <= 0;
                end else begin
                    write_flits_cnt_q <= write_flits_cnt_q + 1;
                end
            end
        end
    end

    //  Forward data flit to the NoC
    //
    assign mem_req_write_data_o = '{
        mem_req_w_data: flush_mem_req_rdata,
        mem_req_w_be: '1,
        mem_req_w_last: flush_mem_req_rlast
    };
    //  }}}

endmodule

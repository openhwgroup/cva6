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
// Date: 12.02.2018
// ------------------------------
// Instruction Cache
// ------------------------------
import ariane_pkg::*;

module icache #(
    parameter int unsigned SET_ASSOCIATIVITY = 4,
    parameter int unsigned INDEX_WIDTH       = 12, // in bit
    parameter int unsigned TAG_WIDTH         = 44, // in bit
    parameter int unsigned CACHE_LINE_WIDTH  = 64, // in bit
    parameter int unsigned FETCH_WIDTH       = 32  // in bit
)(
    input  logic                     clk_i,
    input  logic                     rst_ni,
    input  logic                     flush_i,          // flush the icache, flush and kill have to be asserted together
    input  logic                     fetch_enable_i,   // the core should fetch instructions
    input  logic                     req_i,            // we request a new word
    input  logic                     is_speculative_i, // is this request speculative or not
    input  logic                     kill_s1_i,        // kill the current request
    input  logic                     kill_s2_i,        // kill the last request
    output logic                     ready_o,          // icache is ready
    input  logic [63:0]              vaddr_i,          // 1st cycle: 12 bit index is taken for lookup
    output logic [FETCH_WIDTH-1:0]   data_o,           // 2+ cycle out: tag
    output logic                     is_speculative_o, // the fetch was speculative
    output logic [63:0]              vaddr_o,          // virtual address out
    output logic                     valid_o,          // signals a valid read
    output exception_t               ex_o,             // we've encountered an exception
    output logic                     miss_o,           // we missed on the cache
    AXI_BUS.Master                   axi,
    // Address translation
    output logic                     fetch_req_o,
    output logic [63:0]              fetch_vaddr_o,
    input  logic                     fetch_valid_i,
    input  logic [63:0]              fetch_paddr_i,
    input  exception_t               fetch_exception_i
);

    localparam int unsigned BYTE_OFFSET = $clog2(CACHE_LINE_WIDTH/8); // 3
    localparam int unsigned ICACHE_NUM_WORD = 2**(INDEX_WIDTH - BYTE_OFFSET);
    localparam int unsigned NR_AXI_REFILLS = ($clog2(CACHE_LINE_WIDTH/64) == 0) ? 1 : $clog2(CACHE_LINE_WIDTH/64);
    // registers
    enum logic [3:0] { FLUSH, IDLE, TAG_CMP, WAIT_AXI_R_RESP, WAIT_KILLED_REFILL, WAIT_KILLED_AXI_R_RESP,
                       REDO_REQ, TAG_CMP_SAVED, REFILL,
                       WAIT_ADDRESS_TRANSLATION, WAIT_ADDRESS_TRANSLATION_KILLED
                     }                      state_d, state_q;
    logic [$clog2(ICACHE_NUM_WORD)-1:0]     cnt_d, cnt_q;
    logic [NR_AXI_REFILLS-1:0]              burst_cnt_d, burst_cnt_q; // counter for AXI transfers
    logic [63:0]                            vaddr_d, vaddr_q;
    logic                                   spec_d, spec_q; // request is speculative
    logic [TAG_WIDTH-1:0]                   tag_d, tag_q;
    logic [SET_ASSOCIATIVITY-1:0]           evict_way_d, evict_way_q;
    logic                                   flushing_d, flushing_q;

    // signals
    logic [SET_ASSOCIATIVITY-1:0]         req;           // request to memory array
    logic [CACHE_LINE_WIDTH-1:0]          data_be;       // byte enable for data array
    logic [(2**NR_AXI_REFILLS-1):0][63:0] be;            // flat byte enable
    logic [$clog2(ICACHE_NUM_WORD)-1:0]   addr;          // this is a cache-line address, to memory array
    logic                                 we;            // write enable to memory array
    logic [SET_ASSOCIATIVITY-1:0]         hit;           // hit from tag compare
    logic [BYTE_OFFSET-1:2]               idx;           // index in cache line
    logic                                 update_lfsr;   // shift the LFSR
    logic [SET_ASSOCIATIVITY-1:0]         random_way;    // random way select from LFSR
    logic [SET_ASSOCIATIVITY-1:0]         way_valid;     // bit string which contains the zapped valid bits
    logic [$clog2(SET_ASSOCIATIVITY)-1:0] repl_invalid;  // first non-valid encountered
    logic                                 repl_w_random; // we need to switch repl strategy since all are valid
    logic [TAG_WIDTH-1:0]                 tag;           // tag to do comparison with

    // tag + valid bit read/write data
    struct packed {
        logic                 valid;
        logic [TAG_WIDTH-1:0] tag;
    } tag_rdata [SET_ASSOCIATIVITY-1:0], tag_wdata;

    logic [CACHE_LINE_WIDTH-1:0] data_rdata [SET_ASSOCIATIVITY-1:0], data_wdata;
    logic [(2**NR_AXI_REFILLS-1):0][63:0] wdata;

    for (genvar i = 0; i < SET_ASSOCIATIVITY; i++) begin : sram_block
        // ------------
        // Tag RAM
        // ------------
        sram #(
            // tag + valid bit
            .DATA_WIDTH ( TAG_WIDTH + 1   ),
            .NUM_WORDS  ( ICACHE_NUM_WORD )
        ) tag_sram (
            .clk_i     ( clk_i            ),
            .req_i     ( req[i]           ),
            .we_i      ( we               ),
            .addr_i    ( addr             ),
            .wdata_i   ( tag_wdata        ),
            .be_i      (  '1              ),
            .rdata_o   ( tag_rdata[i]     )
        );
        // ------------
        // Data RAM
        // ------------
        sram #(
            .DATA_WIDTH ( CACHE_LINE_WIDTH  ),
            .NUM_WORDS  ( ICACHE_NUM_WORD   )
        ) data_sram (
            .clk_i     ( clk_i              ),
            .req_i     ( req[i]             ),
            .we_i      ( we                 ),
            .addr_i    ( addr               ),
            .wdata_i   ( data_wdata         ),
            .be_i      ( data_be            ),
            .rdata_o   ( data_rdata[i]      )
        );
    end
    // --------------------
    // Tag Comparison
    // --------------------
    for (genvar i = 0; i < SET_ASSOCIATIVITY; i++) begin
        assign hit[i] = (tag_rdata[i].tag == tag) ? tag_rdata[i].valid : 1'b0;
    end

    `ifndef SYNTHESIS
    `ifndef VERILATOR
    // assert that cache only hits on one way
    assert property (
      @(posedge clk_i) $onehot0(hit)) else begin $error("[icache] Hit should be one-hot encoded"); $stop(); end
    `endif
    `endif

    // ------------------
    // Way Select
    // ------------------
    assign idx = vaddr_q[BYTE_OFFSET-1:2];
    // cacheline selected by hit
    logic [CACHE_LINE_WIDTH/FETCH_WIDTH-1:0][FETCH_WIDTH-1:0] selected_cl;
    logic [CACHE_LINE_WIDTH-1:0] selected_cl_flat;

    for (genvar i = 0; i < CACHE_LINE_WIDTH; i++) begin
        logic [SET_ASSOCIATIVITY-1:0] hit_masked_cl;

        for (genvar j = 0; j < SET_ASSOCIATIVITY; j++)
            assign hit_masked_cl[j] = data_rdata[j][i] & hit[j];

        assign selected_cl_flat[i] = |hit_masked_cl;
    end

    assign selected_cl = selected_cl_flat;
    // maybe re-work if critical
    assign data_o = selected_cl[idx];

    for (genvar i = 0; i < SET_ASSOCIATIVITY; i++) begin
        assign way_valid[i] = tag_rdata[i].valid;
    end

    // ------------------
    // AXI Plumbing
    // ------------------
    assign axi.aw_valid  = '0;
    assign axi.aw_addr   = '0;
    assign axi.aw_prot   = '0;
    assign axi.aw_region = '0;
    assign axi.aw_len    = '0;
    assign axi.aw_size   = 3'b000;
    assign axi.aw_burst  = 2'b00;
    assign axi.aw_lock   = '0;
    assign axi.aw_cache  = '0;
    assign axi.aw_qos    = '0;
    assign axi.aw_id     = '0;
    assign axi.aw_user   = '0;

    assign axi.w_valid   = '0;
    assign axi.w_data    = '0;
    assign axi.w_strb    = '0;
    assign axi.w_user    = '0;
    assign axi.w_last    = 1'b0;
    assign axi.b_ready   = 1'b0;

    assign axi.ar_prot   = '0;
    assign axi.ar_region = '0;
    assign axi.ar_len    = (2**NR_AXI_REFILLS) - 1;
    assign axi.ar_size   = 3'b011;
    assign axi.ar_burst  = 2'b01;
    assign axi.ar_lock   = '0;
    assign axi.ar_cache  = '0;
    assign axi.ar_qos    = '0;
    assign axi.ar_id     = '0;
    assign axi.ar_user   = '0;

    assign axi.r_ready   = 1'b1;

    assign data_be = be;
    assign data_wdata = wdata;

    assign ex_o = fetch_exception_i;
    // ------------------
    // Cache Ctrl
    // ------------------
    always_comb begin : cache_ctrl
        // default assignments
        state_d     = state_q;
        cnt_d       = cnt_q;
        vaddr_d     = vaddr_q;
        spec_d      = spec_q;
        tag_d       = tag_q;
        evict_way_d = evict_way_q;
        flushing_d  = flushing_q;
        burst_cnt_d = burst_cnt_q;

        is_speculative_o = spec_q;
        vaddr_o          = vaddr_q;

        req         = '0;
        addr        = vaddr_i[INDEX_WIDTH-1:BYTE_OFFSET];
        we          = 1'b0;
        be          = '0;
        wdata       = '0;
        tag_wdata   = '0;
        ready_o     = 1'b0;
        tag         = fetch_paddr_i[TAG_WIDTH+INDEX_WIDTH-1:INDEX_WIDTH];
        valid_o     = 1'b0;
        update_lfsr = 1'b0;
        miss_o      = 1'b0;

        axi.ar_valid = 1'b0;
        axi.ar_addr  = '0;

        fetch_req_o = 1'b0;
        fetch_vaddr_o = vaddr_q;

        case (state_q)
            // ~> we are ready to receive a new request
            IDLE: begin
                ready_o = 1'b1 & fetch_enable_i;
                // we are getting a new request
                if (req_i && fetch_enable_i) begin
                    // request the content of all arrays
                    req = '1;
                    // save the virtual address
                    vaddr_d = vaddr_i;
                    spec_d  = is_speculative_i;
                    state_d = TAG_CMP;
                end

                // go to flushing state
                if (flush_i || flushing_q)
                    state_d = FLUSH;

                if (kill_s1_i)
                    state_d = IDLE;
            end
            // ~> compare the tag
            TAG_CMP, TAG_CMP_SAVED: begin
                fetch_req_o = 1'b1; // request address translation
                // use the saved tag
                if (state_q == TAG_CMP_SAVED)
                    tag = tag_q;
                // -------
                // Hit
                // -------
                if (|hit && fetch_valid_i) begin
                    ready_o = 1'b1;
                    valid_o = 1'b1;
                    // we've got another request
                    if (req_i) begin
                        // request the content of all arrays
                        req = '1;
                        // save the index and stay in compare mode
                        vaddr_d = vaddr_i;
                        spec_d  = is_speculative_i;
                        state_d = TAG_CMP;
                    // no new request -> go back to idle
                    end else begin
                        state_d = IDLE;
                    end

                    if (kill_s1_i)
                        state_d = IDLE;
                // -------
                // Miss
                // -------
                end else begin
                    state_d     = REFILL;
                    evict_way_d = '0;
                    // save tag
                    tag_d       = fetch_paddr_i[TAG_WIDTH+INDEX_WIDTH-1:INDEX_WIDTH];
                    miss_o      = 1'b1;
                    // get way which to replace
                    if (repl_w_random) begin
                        evict_way_d = random_way;
                        // shift the lfsr
                        update_lfsr = 1'b1;
                    end else begin
                        evict_way_d[repl_invalid] = 1'b1;
                    end
                end
                // if we didn't hit on the TLB we need to wait until the request has been completed
                if (!fetch_valid_i) begin
                    state_d = WAIT_ADDRESS_TRANSLATION;
                end
            end
            // ~> wait here for a valid address translation, or on a translation even if the request has been killed
            WAIT_ADDRESS_TRANSLATION, WAIT_ADDRESS_TRANSLATION_KILLED: begin
                fetch_req_o = 1'b1;
                // retry the request if no exception occurred
                if (fetch_valid_i && (state_q == WAIT_ADDRESS_TRANSLATION)) begin
                    if (fetch_exception_i.valid)
                        valid_o = 1'b1;
                    else begin
                        state_d = REDO_REQ;
                        tag_d = fetch_paddr_i[TAG_WIDTH+INDEX_WIDTH-1:INDEX_WIDTH];
                    end
                end else if (fetch_valid_i) begin
                    state_d = IDLE;
                end

                if (kill_s2_i)
                    state_d = WAIT_ADDRESS_TRANSLATION_KILLED;
            end
            // ~> request a cache-line refill
            REFILL, WAIT_KILLED_REFILL: begin
                axi.ar_valid  = 1'b1;
                axi.ar_addr[INDEX_WIDTH+TAG_WIDTH-1:0] = {tag_q, vaddr_q[INDEX_WIDTH-1:BYTE_OFFSET], {BYTE_OFFSET{1'b0}}};
                burst_cnt_d = '0;

                if (kill_s2_i)
                    state_d = WAIT_KILLED_REFILL;

                // we need to finish this AXI transfer
                if (axi.ar_ready)
                    state_d = (kill_s2_i || (state_q == WAIT_KILLED_REFILL)) ? WAIT_KILLED_AXI_R_RESP : WAIT_AXI_R_RESP;
            end
            // ~> wait for the read response
            WAIT_AXI_R_RESP, WAIT_KILLED_AXI_R_RESP: begin

                req     = evict_way_q;
                addr    = vaddr_q[INDEX_WIDTH-1:BYTE_OFFSET];

                if (axi.r_valid) begin
                    we = 1'b1;
                    tag_wdata.tag = tag_q;
                    tag_wdata.valid = 1'b1;
                    wdata[burst_cnt_q] = axi.r_data;
                    // enable the right write path
                    be[burst_cnt_q] = '1;
                    // increase burst count
                    burst_cnt_d = burst_cnt_q + 1;
                end

                if (kill_s2_i)
                    state_d = WAIT_KILLED_AXI_R_RESP;

                if (axi.r_valid && axi.r_last) begin
                    state_d = (kill_s2_i) ? IDLE : REDO_REQ;
                end

                if ((state_q == WAIT_KILLED_AXI_R_RESP) && axi.r_last && axi.r_valid)
                    state_d = IDLE;
            end
            // ~> redo the request,
            REDO_REQ: begin
                req = '1;
                addr = vaddr_q[INDEX_WIDTH-1:BYTE_OFFSET];
                tag = tag_q;
                state_d = TAG_CMP_SAVED; // do tag comparison on the saved tag
            end
            // we need to wait for some AXI responses to come back
            // here for the AW valid
            WAIT_KILLED_REFILL: begin
                if (axi.aw_valid)
                    state_d = IDLE;
            end
            // ~> we are coming here after reset or when a flush was requested
            FLUSH: begin
                addr    = cnt_q;
                cnt_d   = cnt_q + 1;
                req     = '1;
                we      = 1;
                // we've finished flushing, go back to idle
                if (cnt_q == ICACHE_NUM_WORD - 1) begin
                    state_d = IDLE;
                    flushing_d = 1'b0;
                end
            end

            default : state_d = IDLE;
        endcase

        // those are the states where we need to wait a little longer until we can safely exit
        if (kill_s2_i && !(state_q inside {REFILL, WAIT_AXI_R_RESP, WAIT_KILLED_REFILL, WAIT_KILLED_AXI_R_RESP}) && !ready_o) begin
            state_d = IDLE;
        end

        // if we are killing we can never give a valid response
        if (kill_s2_i)
            valid_o = 1'b0;

        if (flush_i) begin
            flushing_d = 1'b1;
            ready_o = 1'b0; // we are not ready to accept a further request here
        end
        // if we are going to flush -> do not accept any new requests
        if (flushing_q)
            ready_o = 1'b0;
    end

    find_first_one #(
        .WIDTH ( SET_ASSOCIATIVITY )
    ) i_ff1 (
        .in_i        ( ~way_valid    ),
        .first_one_o ( repl_invalid  ),
        .no_ones_o   ( repl_w_random )
    );

    // -----------------
    // Replacement LFSR
    // -----------------
    lfsr #(.WIDTH (SET_ASSOCIATIVITY)) i_lfsr (
        .clk_i          ( clk_i       ),
        .rst_ni         ( rst_ni      ),
        .en_i           ( update_lfsr ),
        .refill_way_oh  ( random_way  ),
        .refill_way_bin (             ) // left open
    );


    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (~rst_ni) begin
            state_q     <= FLUSH;
            cnt_q       <= '0;
            vaddr_q     <= '0;
            tag_q       <= '0;
            evict_way_q <= '0;
            flushing_q  <= 1'b0;
            spec_q      <= 1'b0;
            burst_cnt_q <= '0;;
        end else begin
            state_q     <= state_d;
            cnt_q       <= cnt_d;
            vaddr_q     <= vaddr_d;
            tag_q       <= tag_d;
            evict_way_q <= evict_way_d;
            flushing_q  <= flushing_d;
            spec_q      <= spec_d;
            burst_cnt_q <= burst_cnt_d;
        end
    end

    `ifndef SYNTHESIS
        initial begin
            assert ($bits(axi.aw_addr) == 64) else $fatal(1, "Ariane needs a 64-bit bus");
        end
    `endif
endmodule

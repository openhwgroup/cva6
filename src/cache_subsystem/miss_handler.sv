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
// Date: 12.11.2017
// Description: Handles cache misses.

// --------------
// MISS Handler
// --------------
import ariane_pkg::*;
import std_cache_pkg::*;

module miss_handler #(
    parameter int unsigned NR_PORTS         = 3
)(
    input  logic                                        clk_i,
    input  logic                                        rst_ni,
    input  logic                                        flush_i,      // flush request
    output logic                                        flush_ack_o,  // acknowledge successful flush
    output logic                                        miss_o,
    input  logic                                        busy_i,       // dcache is busy with something
    // Bypass or miss
    input  logic [NR_PORTS-1:0][$bits(miss_req_t)-1:0]  miss_req_i,
    // Bypass handling
    output logic [NR_PORTS-1:0]                         bypass_gnt_o,
    output logic [NR_PORTS-1:0]                         bypass_valid_o,
    output logic [NR_PORTS-1:0][63:0]                   bypass_data_o,

    // AXI port
    output ariane_axi::req_t                            axi_bypass_o,
    input  ariane_axi::resp_t                           axi_bypass_i,

    // Miss handling (~> cacheline refill)
    output logic [NR_PORTS-1:0]                         miss_gnt_o,
    output logic [NR_PORTS-1:0]                         active_serving_o,

    output logic [63:0]                                 critical_word_o,
    output logic                                        critical_word_valid_o,
    output ariane_axi::req_t                            axi_data_o,
    input  ariane_axi::resp_t                           axi_data_i,

    input  logic [NR_PORTS-1:0][55:0]                   mshr_addr_i,
    output logic [NR_PORTS-1:0]                         mshr_addr_matches_o,
    output logic [NR_PORTS-1:0]                         mshr_index_matches_o,
    // AMO
    input  amo_req_t                                    amo_req_i,
    output amo_resp_t                                   amo_resp_o,
    // Port to SRAMs, for refill and eviction
    output logic  [DCACHE_SET_ASSOC-1:0]                req_o,
    output logic  [DCACHE_INDEX_WIDTH-1:0]              addr_o, // address into cache array
    output cache_line_t                                 data_o,
    output cl_be_t                                      be_o,
    input  cache_line_t [DCACHE_SET_ASSOC-1:0]          data_i,
    output logic                                        we_o
);

    // FSM states
    enum logic [3:0] {
        IDLE,               // 0
        FLUSHING,           // 1
        FLUSH,              // 2
        WB_CACHELINE_FLUSH, // 3
        FLUSH_REQ_STATUS,   // 4
        WB_CACHELINE_MISS,  // 5
        WAIT_GNT_SRAM,      // 6
        MISS,               // 7
        REQ_CACHELINE,      // 8
        MISS_REPL,          // 9
        SAVE_CACHELINE,     // A
        INIT,               // B
        AMO_LOAD,           // C
        AMO_SAVE_LOAD,      // D
        AMO_STORE           // E
    } state_d, state_q;

    // Registers
    mshr_t                                  mshr_d, mshr_q;
    logic [DCACHE_INDEX_WIDTH-1:0]          cnt_d, cnt_q;
    logic [DCACHE_SET_ASSOC-1:0]            evict_way_d, evict_way_q;
    // cache line to evict
    cache_line_t                            evict_cl_d, evict_cl_q;

    logic serve_amo_d, serve_amo_q;
    // Request from one FSM
    logic [NR_PORTS-1:0]                    miss_req_valid;
    logic [NR_PORTS-1:0]                    miss_req_bypass;
    logic [NR_PORTS-1:0][63:0]              miss_req_addr;
    logic [NR_PORTS-1:0][63:0]              miss_req_wdata;
    logic [NR_PORTS-1:0]                    miss_req_we;
    logic [NR_PORTS-1:0][7:0]               miss_req_be;
    logic [NR_PORTS-1:0][1:0]               miss_req_size;

    // Cache Line Refill <-> AXI
    logic                                    req_fsm_miss_valid;
    logic [63:0]                             req_fsm_miss_addr;
    logic [DCACHE_LINE_WIDTH-1:0]            req_fsm_miss_wdata;
    logic                                    req_fsm_miss_we;
    logic [(DCACHE_LINE_WIDTH/8)-1:0]        req_fsm_miss_be;
    ariane_axi::ad_req_t                     req_fsm_miss_req;
    logic [1:0]                              req_fsm_miss_size;

    logic                                    gnt_miss_fsm;
    logic                                    valid_miss_fsm;
    logic [(DCACHE_LINE_WIDTH/64)-1:0][63:0] data_miss_fsm;

    // Cache Management <-> LFSR
    logic                                  lfsr_enable;
    logic [DCACHE_SET_ASSOC-1:0]           lfsr_oh;
    logic [$clog2(DCACHE_SET_ASSOC-1)-1:0] lfsr_bin;
    // AMOs
    ariane_pkg::amo_t amo_op;
    logic [63:0] amo_operand_a, amo_operand_b, amo_result_o;

    struct packed {
        logic [63:3] address;
        logic        valid;
    } reservation_d, reservation_q;

    // ------------------------------
    // Cache Management
    // ------------------------------
    always_comb begin : cache_management
        automatic logic [DCACHE_SET_ASSOC-1:0] evict_way, valid_way;

        for (int unsigned i = 0; i < DCACHE_SET_ASSOC; i++) begin
            evict_way[i] = data_i[i].valid & data_i[i].dirty;
            valid_way[i] = data_i[i].valid;
        end
        // ----------------------
        // Default Assignments
        // ----------------------
        // memory array
        req_o  = '0;
        addr_o = '0;
        data_o = '0;
        be_o   = '0;
        we_o   = '0;
        // Cache controller
        miss_gnt_o = '0;
        // LFSR replacement unit
        lfsr_enable = 1'b0;
        // to AXI refill
        req_fsm_miss_valid  = 1'b0;
        req_fsm_miss_addr   = '0;
        req_fsm_miss_wdata  = '0;
        req_fsm_miss_we     = 1'b0;
        req_fsm_miss_be     = '0;
        req_fsm_miss_req    = ariane_axi::CACHE_LINE_REQ;
        req_fsm_miss_size   = 2'b11;
        // core
        flush_ack_o         = 1'b0;
        miss_o              = 1'b0; // to performance counter
        serve_amo_d         = serve_amo_q;
        // --------------------------------
        // Flush and Miss operation
        // --------------------------------
        state_d      = state_q;
        cnt_d        = cnt_q;
        evict_way_d  = evict_way_q;
        evict_cl_d   = evict_cl_q;
        mshr_d       = mshr_q;
        // communicate to the requester which unit we are currently serving
        active_serving_o[mshr_q.id] = mshr_q.valid;
        // AMOs
        amo_resp_o.ack = 1'b0;
        amo_resp_o.result = '0;
        // silence the unit when not used
        amo_op = amo_req_i.amo_op;
        amo_operand_a = '0;
        amo_operand_b = '0;

        reservation_d = reservation_q;
        case (state_q)

            IDLE: begin
                // lowest priority are AMOs, wait until everything else is served before going for the AMOs
                if (amo_req_i.req && !busy_i) begin
                    // 1. Flush the cache
                    if (!serve_amo_q) begin
                        state_d = FLUSH_REQ_STATUS;
                        serve_amo_d = 1'b1;
                    // 2. Do the AMO
                    end else begin
                        state_d = AMO_LOAD;
                        serve_amo_d = 1'b0;
                    end
                end
                // check if we want to flush and can flush e.g.: we are not busy anymore
                // TODO: Check that the busy flag is indeed needed
                if (flush_i && !busy_i) begin
                    state_d = FLUSH_REQ_STATUS;
                    cnt_d = '0;
                end

                // check if one of the state machines missed
                for (int unsigned i = 0; i < NR_PORTS; i++) begin
                    // here comes the refill portion of code
                    if (miss_req_valid[i] && !miss_req_bypass[i]) begin
                        state_d      = MISS;
                        // we are taking another request so don't take the AMO
                        serve_amo_d  = 1'b0;
                        // save to MSHR
                        mshr_d.valid = 1'b1;
                        mshr_d.we    = miss_req_we[i];
                        mshr_d.id    = i;
                        mshr_d.addr  = miss_req_addr[i][DCACHE_TAG_WIDTH+DCACHE_INDEX_WIDTH-1:0];
                        mshr_d.wdata = miss_req_wdata[i];
                        mshr_d.be    = miss_req_be[i];
                        break;
                    end
                end
            end

            //  ~> we missed on the cache
            MISS: begin
                // 1. Check if there is an empty cache-line
                // 2. If not -> evict one
                req_o = '1;
                addr_o = mshr_q.addr[DCACHE_INDEX_WIDTH-1:0];
                state_d = MISS_REPL;
                miss_o = 1'b1;
            end

            // ~> second miss cycle
            MISS_REPL: begin
                // if all are valid we need to evict one, pseudo random from LFSR
                if (&valid_way) begin
                    lfsr_enable = 1'b1;
                    evict_way_d = lfsr_oh;
                    // do we need to write back the cache line?
                    if (data_i[lfsr_bin].dirty) begin
                        state_d = WB_CACHELINE_MISS;
                        evict_cl_d.tag = data_i[lfsr_bin].tag;
                        evict_cl_d.data = data_i[lfsr_bin].data;
                        cnt_d = mshr_q.addr[DCACHE_INDEX_WIDTH-1:0];
                    // no - we can request a cache line now
                    end else
                        state_d = REQ_CACHELINE;
                // we have at least one free way
                end else begin
                    // get victim cache-line by looking for the first non-valid bit
                    evict_way_d = get_victim_cl(~valid_way);
                    state_d = REQ_CACHELINE;
                end
            end

            // ~> we can just load the cache-line, the way is store in evict_way_q
            REQ_CACHELINE: begin
                req_fsm_miss_valid  = 1'b1;
                req_fsm_miss_addr   = mshr_q.addr;

                if (gnt_miss_fsm) begin
                    state_d = SAVE_CACHELINE;
                    miss_gnt_o[mshr_q.id] = 1'b1;
                end
            end

            // ~> replace the cacheline
            SAVE_CACHELINE: begin
                // calculate cacheline offset
                automatic logic [$clog2(DCACHE_LINE_WIDTH)-1:0] cl_offset;
                cl_offset = mshr_q.addr[DCACHE_BYTE_OFFSET-1:3] << 6;
                // we've got a valid response from refill unit
                if (valid_miss_fsm) begin

                    addr_o       = mshr_q.addr[DCACHE_INDEX_WIDTH-1:0];
                    req_o        = evict_way_q;
                    we_o         = 1'b1;
                    be_o         = '1;
                    be_o.vldrty  = evict_way_q;
                    data_o.tag   = mshr_q.addr[DCACHE_TAG_WIDTH+DCACHE_INDEX_WIDTH-1:DCACHE_INDEX_WIDTH];
                    data_o.data  = data_miss_fsm;
                    data_o.valid = 1'b1;
                    data_o.dirty = 1'b0;

                    // is this a write?
                    if (mshr_q.we) begin
                        // Yes, so safe the updated data now
                        for (int i = 0; i < 8; i++) begin
                            // check if we really want to write the corresponding byte
                            if (mshr_q.be[i])
                                data_o.data[(cl_offset + i*8) +: 8] = mshr_q.wdata[i];
                        end
                        // its immediately dirty if we write
                        data_o.dirty = 1'b1;
                    end
                    // reset MSHR
                    mshr_d.valid = 1'b0;
                    // go back to idle
                    state_d = IDLE;
                end
            end

            // ------------------------------
            // Write Back Operation
            // ------------------------------
            // ~> evict a cache line from way saved in evict_way_q
            WB_CACHELINE_FLUSH, WB_CACHELINE_MISS: begin

                req_fsm_miss_valid  = 1'b1;
                req_fsm_miss_addr   = {evict_cl_q.tag, cnt_q[DCACHE_INDEX_WIDTH-1:DCACHE_BYTE_OFFSET], {{DCACHE_BYTE_OFFSET}{1'b0}}};
                req_fsm_miss_be     = '1;
                req_fsm_miss_we     = 1'b1;
                req_fsm_miss_wdata  = evict_cl_q.data;

                // we've got a grant --> this is timing critical, think about it
                if (gnt_miss_fsm) begin
                    // write status array
                    addr_o     = cnt_q;
                    req_o      = 1'b1;
                    we_o       = 1'b1;
                    data_o.valid = INVALIDATE_ON_FLUSH ? 1'b0 : 1'b1;
                    // invalidate
                    be_o.vldrty = evict_way_q;
                    // go back to handling the miss or flushing, depending on where we came from
                    state_d = (state_q == WB_CACHELINE_MISS) ? MISS : FLUSH_REQ_STATUS;
                end
            end

            // ------------------------------
            // Flushing & Initialization
            // ------------------------------
            // ~> make another request to check the same cache-line if there are still some valid entries
            FLUSH_REQ_STATUS: begin
                req_o   = '1;
                addr_o  = cnt_q;
                state_d = FLUSHING;
            end

            FLUSHING: begin
                // this has priority
                // at least one of the cache lines is dirty
                if (|evict_way) begin
                    // evict cache line, look for the first cache-line which is dirty
                    evict_way_d = get_victim_cl(evict_way);
                    evict_cl_d  = data_i[one_hot_to_bin(evict_way)];
                    state_d     = WB_CACHELINE_FLUSH;
                // not dirty ~> increment and continue
                end else begin
                    // increment and re-request
                    cnt_d       = cnt_q + (1'b1 << DCACHE_BYTE_OFFSET);
                    state_d     = FLUSH_REQ_STATUS;
                    addr_o      = cnt_q;
                    req_o       = 1'b1;
                    be_o.vldrty = INVALIDATE_ON_FLUSH ? '1 : '0;
                    we_o        = 1'b1;
                    // finished with flushing operation, go back to idle
                    if (cnt_q[DCACHE_INDEX_WIDTH-1:DCACHE_BYTE_OFFSET] == DCACHE_NUM_WORDS-1) begin
                        // only acknowledge if the flush wasn't triggered by an atomic
                        flush_ack_o = ~serve_amo_q;
                        state_d     = IDLE;
                    end
                end
            end

            // ~> only called after reset
            INIT: begin
                // initialize status array
                addr_o = cnt_q;
                req_o  = 1'b1;
                we_o   = 1'b1;
                // only write the dirty array
                be_o.vldrty = '1;
                cnt_d       = cnt_q + (1'b1 << DCACHE_BYTE_OFFSET);
                // finished initialization
                if (cnt_q[DCACHE_INDEX_WIDTH-1:DCACHE_BYTE_OFFSET] == DCACHE_NUM_WORDS-1)
                    state_d = IDLE;
            end
            // ----------------------
            // AMOs
            // ----------------------
            // TODO(zarubaf) Move this closer to memory
            // ~> we are here because we need to do the AMO, the cache is clean at this point
            // start by executing the load
            AMO_LOAD: begin
                req_fsm_miss_valid = 1'b1;
                // address is in operand a
                req_fsm_miss_addr = amo_req_i.operand_a;
                req_fsm_miss_req = ariane_axi::SINGLE_REQ;
                req_fsm_miss_size = amo_req_i.size;
                // the request has been granted
                if (gnt_miss_fsm) begin
                    state_d = AMO_SAVE_LOAD;
                end
            end
            // save the load value
            AMO_SAVE_LOAD: begin
                if (valid_miss_fsm) begin
                    // we are only concerned about the lower 64-bit
                    mshr_d.wdata = data_miss_fsm[0];
                    state_d = AMO_STORE;
                end
            end
            // and do the store
            AMO_STORE: begin
                automatic logic [63:0] load_data;
                // re-align load data
                load_data = data_align(amo_req_i.operand_a[2:0], mshr_q.wdata);
                // Sign-extend for word operation
                if (amo_req_i.size == 2'b10) begin
                    amo_operand_a = sext32(load_data[31:0]);
                    amo_operand_b = sext32(amo_req_i.operand_b[31:0]);
                end else begin
                    amo_operand_a = load_data;
                    amo_operand_b = amo_req_i.operand_b;
                end

                //  we do not need a store request for load reserved or a failing store conditional
                //  we can bail-out without making any further requests
                if (amo_req_i.amo_op == AMO_LR ||
                   (amo_req_i.amo_op == AMO_SC &&
                   ((reservation_q.valid && reservation_q.address != amo_req_i.operand_a[63:3]) || !reservation_q.valid))) begin
                    req_fsm_miss_valid = 1'b0;
                    state_d = IDLE;
                    amo_resp_o.ack = 1'b1;
                    // write-back the result
                    amo_resp_o.result = amo_operand_a;
                    // we know that the SC failed
                    if (amo_req_i.amo_op == AMO_SC) begin
                        amo_resp_o.result = 1'b1;
                        // also clear the reservation
                        reservation_d.valid = 1'b0;
                    end
                end else begin
                    req_fsm_miss_valid = 1'b1;
                end

                req_fsm_miss_we   = 1'b1;
                req_fsm_miss_req  = ariane_axi::SINGLE_REQ;
                req_fsm_miss_size = amo_req_i.size;
                req_fsm_miss_addr = amo_req_i.operand_a;

                req_fsm_miss_wdata = data_align(amo_req_i.operand_a[2:0], amo_result_o);
                req_fsm_miss_be = be_gen(amo_req_i.operand_a[2:0], amo_req_i.size);

                // place a reservation on the memory
                if (amo_req_i.amo_op == AMO_LR) begin
                    reservation_d.address = amo_req_i.operand_a[63:3];
                    reservation_d.valid = 1'b1;
                end

                // the request is valid or we didn't need to go for another store
                if (valid_miss_fsm) begin
                    state_d = IDLE;
                    amo_resp_o.ack = 1'b1;
                    // write-back the result
                    amo_resp_o.result = amo_operand_a;

                    if (amo_req_i.amo_op == AMO_SC) begin
                        amo_resp_o.result = 1'b0;
                        // An SC must fail if there is a nother SC (to any address) between the LR and the SC in program
                        // order (even to the same address).
                        // in any case destory the reservation
                        reservation_d.valid = 1'b0;
                    end
                end
            end
        endcase
    end

    // check MSHR for aliasing
    always_comb begin

        mshr_addr_matches_o  = 'b0;
        mshr_index_matches_o = 'b0;

        for (int i = 0; i < NR_PORTS; i++) begin
            // check mshr for potential matching of other units, exclude the unit currently being served
            if (mshr_q.valid && mshr_addr_i[i][55:DCACHE_BYTE_OFFSET] == mshr_q.addr[55:DCACHE_BYTE_OFFSET]) begin
                mshr_addr_matches_o[i] = 1'b1;
            end

            // same as previous, but checking only the index
            if (mshr_q.valid && mshr_addr_i[i][DCACHE_INDEX_WIDTH-1:DCACHE_BYTE_OFFSET] == mshr_q.addr[DCACHE_INDEX_WIDTH-1:DCACHE_BYTE_OFFSET]) begin
                mshr_index_matches_o[i] = 1'b1;
            end
        end
    end
    // --------------------
    // Sequential Process
    // --------------------
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (~rst_ni) begin
            mshr_q        <= '0;
            state_q       <= INIT;
            cnt_q         <= '0;
            evict_way_q   <= '0;
            evict_cl_q    <= '0;
            serve_amo_q   <= 1'b0;
            reservation_q <= '0;
        end else begin
            mshr_q        <= mshr_d;
            state_q       <= state_d;
            cnt_q         <= cnt_d;
            evict_way_q   <= evict_way_d;
            evict_cl_q    <= evict_cl_d;
            serve_amo_q   <= serve_amo_d;
            reservation_q <= reservation_d;
        end
    end

    //pragma translate_off
    `ifndef VERILATOR
    // assert that cache only hits on one way
    assert property (
      @(posedge clk_i) $onehot0(evict_way_q)) else $warning("Evict-way should be one-hot encoded");
    `endif
    //pragma translate_on
    // ----------------------
    // Bypass Arbiter
    // ----------------------
    // Connection Arbiter <-> AXI
    logic                        req_fsm_bypass_valid;
    logic [63:0]                 req_fsm_bypass_addr;
    logic [63:0]                 req_fsm_bypass_wdata;
    logic                        req_fsm_bypass_we;
    logic [7:0]                  req_fsm_bypass_be;
    logic [1:0]                  req_fsm_bypass_size;
    logic                        gnt_bypass_fsm;
    logic                        valid_bypass_fsm;
    logic [63:0]                 data_bypass_fsm;
    logic [$clog2(NR_PORTS)-1:0] id_fsm_bypass;
    logic [3:0]                  id_bypass_fsm;
    logic [3:0]                  gnt_id_bypass_fsm;

    arbiter #(
        .NR_PORTS       ( NR_PORTS                                 ),
        .DATA_WIDTH     ( 64                                       )
    ) i_bypass_arbiter (
        // Master Side
        .data_req_i     ( miss_req_valid & miss_req_bypass         ),
        .address_i      ( miss_req_addr                            ),
        .data_wdata_i   ( miss_req_wdata                           ),
        .data_we_i      ( miss_req_we                              ),
        .data_be_i      ( miss_req_be                              ),
        .data_size_i    ( miss_req_size                            ),
        .data_gnt_o     ( bypass_gnt_o                             ),
        .data_rvalid_o  ( bypass_valid_o                           ),
        .data_rdata_o   ( bypass_data_o                            ),
        // Slave Sid
        .id_i           ( id_bypass_fsm[$clog2(NR_PORTS)-1:0]      ),
        .id_o           ( id_fsm_bypass                            ),
        .gnt_id_i       ( gnt_id_bypass_fsm[$clog2(NR_PORTS)-1:0]  ),
        .address_o      ( req_fsm_bypass_addr                      ),
        .data_wdata_o   ( req_fsm_bypass_wdata                     ),
        .data_req_o     ( req_fsm_bypass_valid                     ),
        .data_we_o      ( req_fsm_bypass_we                        ),
        .data_be_o      ( req_fsm_bypass_be                        ),
        .data_size_o    ( req_fsm_bypass_size                      ),
        .data_gnt_i     ( gnt_bypass_fsm                           ),
        .data_rvalid_i  ( valid_bypass_fsm                         ),
        .data_rdata_i   ( data_bypass_fsm                          ),
        .*
    );

    axi_adapter #(
        .DATA_WIDTH            ( 64                 ),
        .AXI_ID_WIDTH          ( 4                  ),
        .CACHELINE_BYTE_OFFSET ( DCACHE_BYTE_OFFSET )
    ) i_bypass_axi_adapter (
        .clk_i,
        .rst_ni,
        .req_i                 ( req_fsm_bypass_valid   ),
        .type_i                ( ariane_axi::SINGLE_REQ ),
        .gnt_o                 ( gnt_bypass_fsm         ),
        .addr_i                ( req_fsm_bypass_addr    ),
        .we_i                  ( req_fsm_bypass_we      ),
        .wdata_i               ( req_fsm_bypass_wdata   ),
        .be_i                  ( req_fsm_bypass_be      ),
        .size_i                ( req_fsm_bypass_size    ),
        .id_i                  ( {2'b10, id_fsm_bypass} ),
        .valid_o               ( valid_bypass_fsm       ),
        .rdata_o               ( data_bypass_fsm        ),
        .gnt_id_o              ( gnt_id_bypass_fsm      ),
        .id_o                  ( id_bypass_fsm          ),
        .critical_word_o       (                        ), // not used for single requests
        .critical_word_valid_o (                        ), // not used for single requests
        .axi_req_o             ( axi_bypass_o           ),
        .axi_resp_i            ( axi_bypass_i           )
    );

    // ----------------------
    // Cache Line AXI Refill
    // ----------------------
    axi_adapter  #(
        .DATA_WIDTH            ( DCACHE_LINE_WIDTH  ),
        .AXI_ID_WIDTH          ( 4                  ),
        .CACHELINE_BYTE_OFFSET ( DCACHE_BYTE_OFFSET )
    ) i_miss_axi_adapter (
        .clk_i,
        .rst_ni,
        .req_i               ( req_fsm_miss_valid ),
        .type_i              ( req_fsm_miss_req   ),
        .gnt_o               ( gnt_miss_fsm       ),
        .addr_i              ( req_fsm_miss_addr  ),
        .we_i                ( req_fsm_miss_we    ),
        .wdata_i             ( req_fsm_miss_wdata ),
        .be_i                ( req_fsm_miss_be    ),
        .size_i              ( req_fsm_miss_size  ),
        .id_i                ( 4'b1100            ),
        .gnt_id_o            (                    ), // open
        .valid_o             ( valid_miss_fsm     ),
        .rdata_o             ( data_miss_fsm      ),
        .id_o                (                    ),
        .critical_word_o,
        .critical_word_valid_o,
        .axi_req_o           ( axi_data_o         ),
        .axi_resp_i          ( axi_data_i         )
    );

    // -----------------
    // Replacement LFSR
    // -----------------
    lfsr_8bit #(.WIDTH (DCACHE_SET_ASSOC)) i_lfsr (
        .en_i           ( lfsr_enable ),
        .refill_way_oh  ( lfsr_oh     ),
        .refill_way_bin ( lfsr_bin    ),
        .*
    );

    // -----------------
    // AMO ALU
    // -----------------
    amo_alu i_amo_alu (
        .amo_op_i        ( amo_op        ),
        .amo_operand_a_i ( amo_operand_a ),
        .amo_operand_b_i ( amo_operand_b ),
        .amo_result_o    ( amo_result_o  )
    );

    // -----------------
    // Struct Split
    // -----------------
    // Hack as system verilog support in modelsim seems to be buggy here
    always_comb begin
        automatic miss_req_t miss_req;

        for (int unsigned i = 0; i < NR_PORTS; i++) begin
            miss_req =  miss_req_t'(miss_req_i[i]);
            miss_req_valid  [i]  = miss_req.valid;
            miss_req_bypass [i]  = miss_req.bypass;
            miss_req_addr   [i]  = miss_req.addr;
            miss_req_wdata  [i]  = miss_req.wdata;
            miss_req_we     [i]  = miss_req.we;
            miss_req_be     [i]  = miss_req.be;
            miss_req_size   [i]  = miss_req.size;
        end
    end
endmodule

// --------------
// AXI Arbiter
// --------------s
//
// Description: Arbitrates access to AXI refill/bypass
//
module arbiter #(
        parameter int unsigned NR_PORTS   = 3,
        parameter int unsigned DATA_WIDTH = 64
)(
    input  logic                                   clk_i,          // Clock
    input  logic                                   rst_ni,         // Asynchronous reset active low
    // master ports
    input  logic [NR_PORTS-1:0]                    data_req_i,
    input  logic [NR_PORTS-1:0][63:0]              address_i,
    input  logic [NR_PORTS-1:0][DATA_WIDTH-1:0]    data_wdata_i,
    input  logic [NR_PORTS-1:0]                    data_we_i,
    input  logic [NR_PORTS-1:0][DATA_WIDTH/8-1:0]  data_be_i,
    input  logic [NR_PORTS-1:0][1:0]               data_size_i,
    output logic [NR_PORTS-1:0]                    data_gnt_o,
    output logic [NR_PORTS-1:0]                    data_rvalid_o,
    output logic [NR_PORTS-1:0][DATA_WIDTH-1:0]    data_rdata_o,
    // slave port
    input  logic [$clog2(NR_PORTS)-1:0]            id_i,
    output logic [$clog2(NR_PORTS)-1:0]            id_o,
    input  logic [$clog2(NR_PORTS)-1:0]            gnt_id_i,
    output logic                                   data_req_o,
    output logic [63:0]                            address_o,
    output logic [DATA_WIDTH-1:0]                  data_wdata_o,
    output logic                                   data_we_o,
    output logic [DATA_WIDTH/8-1:0]                data_be_o,
    output logic [1:0]                             data_size_o,
    input  logic                                   data_gnt_i,
    input  logic                                   data_rvalid_i,
    input  logic [DATA_WIDTH-1:0]                  data_rdata_i
);

    enum logic [1:0] { IDLE, REQ, SERVING } state_d, state_q;

    struct packed {
        logic [$clog2(NR_PORTS)-1:0] id;
        logic [63:0]                 address;
        logic [63:0]                 data;
        logic [1:0]                  size;
        logic [DATA_WIDTH/8-1:0]     be;
        logic                        we;
    } req_d, req_q;

    always_comb begin
        automatic logic [$clog2(NR_PORTS)-1:0] request_index;
        request_index = 0;

        state_d = state_q;
        req_d   = req_q;
        // request port
        data_req_o                = 1'b0;
        address_o                 = req_q.address;
        data_wdata_o              = req_q.data;
        data_be_o                 = req_q.be;
        data_size_o               = req_q.size;
        data_we_o                 = req_q.we;
        id_o                      = req_q.id;
        data_gnt_o                = '0;
        // read port
        data_rvalid_o             = '0;
        data_rdata_o              = '0;
        data_rdata_o[req_q.id]    = data_rdata_i;

        case (state_q)

            IDLE: begin
                // wait for incoming requests
                for (int unsigned i = 0; i < NR_PORTS; i++) begin
                    if (data_req_i[i] == 1'b1) begin
                        data_req_o    = data_req_i[i];
                        data_gnt_o[i] = data_req_i[i];
                        request_index = i[$bits(request_index)-1:0];
                        // save the request
                        req_d.address = address_i[i];
                        req_d.id = i[$bits(req_q.id)-1:0];
                        req_d.data = data_wdata_i[i];
                        req_d.size = data_size_i[i];
                        req_d.be = data_be_i[i];
                        req_d.we = data_we_i[i];
                        state_d = SERVING;
                        break; // break here as this is a priority select
                    end
                end

                address_o                 = address_i[request_index];
                data_wdata_o              = data_wdata_i[request_index];
                data_be_o                 = data_be_i[request_index];
                data_size_o               = data_size_i[request_index];
                data_we_o                 = data_we_i[request_index];
                id_o                      = request_index;
            end

            SERVING: begin
                data_req_o = 1'b1;
                if (data_rvalid_i) begin
                    data_rvalid_o[req_q.id] = 1'b1;
                    state_d = IDLE;
                end
            end

            default : /* default */;
        endcase
    end

    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (~rst_ni) begin
            state_q <= IDLE;
            req_q   <= '0;
        end else begin
            state_q <= state_d;
            req_q   <= req_d;
        end
    end
    // ------------
    // Assertions
    // ------------

    //pragma translate_off
    `ifndef VERILATOR
    // make sure that we eventually get an rvalid after we received a grant
    assert property (@(posedge clk_i) data_gnt_i |-> ##[1:$] data_rvalid_i )
        else begin $error("There was a grant without a rvalid"); $stop(); end
    // assert that there is no grant without a request
    assert property (@(negedge clk_i) data_gnt_i |-> data_req_o)
        else begin $error("There was a grant without a request."); $stop(); end
    // assert that the address does not contain X when request is sent
    assert property ( @(posedge clk_i) (data_req_o) |-> (!$isunknown(address_o)) )
      else begin $error("address contains X when request is set"); $stop(); end

    `endif
    //pragma translate_on
endmodule

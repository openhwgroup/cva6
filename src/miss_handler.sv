// --------------
// MISS Handler
// --------------
//
// Description: Handles cache misses.
//
import nbdcache_pkg::*;

module miss_handler #(
    parameter int unsigned NR_PORTS = 3
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
    AXI_BUS.Master                                      bypass_if,
    // Miss handling (~> cacheline refill)
    output logic [NR_PORTS-1:0]                         miss_gnt_o,

    output logic [63:0]                                 critical_word_o,
    output logic                                        critical_word_valid_o,
    AXI_BUS.Master                                      data_if,

    input  logic [NR_PORTS-1:0][55:0]                   mshr_addr_i,
    output logic [NR_PORTS-1:0]                         mashr_addr_matches_o,
    // Port to SRAMs, for refill and eviction
    output logic  [SET_ASSOCIATIVITY-1:0]               req_o,
    output logic  [INDEX_WIDTH-1:0]                     addr_o, // address into cache array
    input  logic                                        gnt_i,
    output cache_line_t                                 data_o,
    output cl_be_t                                      be_o,
    input  cache_line_t [SET_ASSOCIATIVITY-1:0]         data_i,
    output logic                                        we_o
);
    // FSM states
    enum logic [3:0] { IDLE, FLUSHING, FLUSH, WB_CACHELINE_FLUSH, FLUSH_REQ_STATUS, WB_CACHELINE_MISS, WAIT_GNT_SRAM, MISS,
                       REQ_CACHELINE, MISS_REPL, SAVE_CACHELINE, INIT } state_d, state_q;
    // Registers
    mshr_t                                  mshr_d, mshr_q;
    logic [INDEX_WIDTH-1:0]                 cnt_d, cnt_q;
    logic [SET_ASSOCIATIVITY-1:0]           evict_way_d, evict_way_q;
    // cache line to evict
    cache_line_t                            evict_cl_d, evict_cl_q;

    // Request from one FSM
    logic [NR_PORTS-1:0]                    miss_req_valid;
    logic [NR_PORTS-1:0]                    miss_req_bypass;
    logic [NR_PORTS-1:0][63:0]              miss_req_addr;
    logic [NR_PORTS-1:0][63:0]              miss_req_wdata;
    logic [NR_PORTS-1:0]                    miss_req_we;
    logic [NR_PORTS-1:0][7:0]               miss_req_be;

    // Cache Line Refill <-> AXI
    logic                                   req_fsm_miss_valid;
    logic                                   req_fsm_miss_bypass;
    logic [63:0]                            req_fsm_miss_addr;
    logic [CACHE_LINE_WIDTH-1:0]            req_fsm_miss_wdata;
    logic                                   req_fsm_miss_we;
    logic [(CACHE_LINE_WIDTH/8)-1:0]        req_fsm_miss_be;
    logic                                   gnt_miss_fsm;
    logic                                   valid_miss_fsm;
    logic [(CACHE_LINE_WIDTH/64)-1:0][63:0] data_miss_fsm;

    // Cache Management <-> LFSR
    logic                                   lfsr_enable;
    logic [SET_ASSOCIATIVITY-1:0]           lfsr_oh;
    logic [$clog2(SET_ASSOCIATIVITY-1)-1:0] lfsr_bin;

    // ------------------------------
    // Cache Management
    // ------------------------------
    always_comb begin : cache_management
        automatic logic [SET_ASSOCIATIVITY-1:0] evict_way, valid_way;

        for (int unsigned i = 0; i < SET_ASSOCIATIVITY; i++) begin
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
        miss_gnt_o = 1'b0;
        // LFSR replacement unit
        lfsr_enable = 1'b0;
        // to AXI refill
        req_fsm_miss_valid  = 1'b0;
        req_fsm_miss_bypass = 1'b0;
        req_fsm_miss_addr   = '0;
        req_fsm_miss_wdata  = '0;
        req_fsm_miss_we     = 1'b0;
        req_fsm_miss_be     = '0;
        // core
        flush_ack_o         = 1'b0;
        miss_o              = 1'b0; // to performance counter
        // --------------------------------
        // Flush and Miss operation
        // --------------------------------
        state_d      = state_q;
        cnt_d        = cnt_q;
        evict_way_d  = evict_way_q;
        evict_cl_d   = evict_cl_q;
        mshr_d       = mshr_q;

        case (state_q)

            IDLE: begin

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
                        // save to MSHR
                        mshr_d.valid = 1'b1;
                        mshr_d.we    = miss_req_we[i];
                        mshr_d.id    = i;
                        mshr_d.addr  = miss_req_addr[i][TAG_WIDTH+INDEX_WIDTH-1:0];
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
                addr_o = mshr_q.addr[INDEX_WIDTH-1:0];
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
                        cnt_d = mshr_q.addr[INDEX_WIDTH-1:0];
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
                automatic logic [$clog2(CACHE_LINE_WIDTH)-1:0] cl_offset;
                cl_offset = mshr_q.addr[BYTE_OFFSET-1:3] << 6;
                // we've got a valid response from refill unit
                if (valid_miss_fsm) begin

                    addr_o       = mshr_q.addr[INDEX_WIDTH-1:0];
                    req_o        = evict_way_q;
                    we_o         = 1'b1;
                    be_o         = '1;
                    be_o.valid   = evict_way_q;
                    be_o.dirty   = evict_way_q;
                    data_o.tag   = mshr_q.addr[TAG_WIDTH+INDEX_WIDTH-1:INDEX_WIDTH];
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
                req_fsm_miss_addr   = {evict_cl_q.tag, cnt_q};
                req_fsm_miss_be     = '1;
                req_fsm_miss_we     = 1'b1;
                req_fsm_miss_wdata  = evict_cl_q.data;

                // we've got a grant --> this is timing critical, think about it
                if (gnt_miss_fsm) begin
                    // write status array
                    addr_o     = cnt_q;
                    req_o      = 1'b1;
                    we_o       = 1'b1;
                    // invalidate
                    be_o.valid = evict_way_q;
                    be_o.dirty = evict_way_q;
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
                    cnt_d   = cnt_q + (1'b1 << BYTE_OFFSET);
                    state_d = FLUSH_REQ_STATUS;
                    // finished with flushing operation, go back to idle
                    if (cnt_q[INDEX_WIDTH-1:BYTE_OFFSET] == NUM_WORDS-1) begin
                        flush_ack_o = 1'b1;
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
                be_o.dirty = '1;
                be_o.valid = '1;
                data_o     = 'b0;
                cnt_d      = cnt_q + (1'b1 << BYTE_OFFSET);
                // finished initialization
                if (cnt_q[INDEX_WIDTH-1:BYTE_OFFSET] == NUM_WORDS-1)
                    state_d = IDLE;
            end
        endcase
    end

    // check MSHR for aliasing
    always_comb begin

        mashr_addr_matches_o = 'b0;

        for (int i = 0; i < NR_PORTS; i++) begin
            if (mshr_q.valid && mshr_addr_i[i][55:$clog2(CACHE_LINE_WIDTH/8)] == mshr_q.addr[55:$clog2(CACHE_LINE_WIDTH/8)]) begin
                mashr_addr_matches_o[i] = 1'b1;
            end
        end
    end
    // --------------------
    // Sequential Process
    // --------------------
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (~rst_ni) begin
            mshr_q       <= '0;
            state_q      <= INIT;
            cnt_q        <= '0;
            evict_way_q  <= '0;
            evict_cl_q   <= '0;
        end else begin
            mshr_q       <= mshr_d;
            state_q      <= state_d;
            cnt_q        <= cnt_d;
            evict_way_q  <= evict_way_d;
            evict_cl_q   <= evict_cl_d;
        end
    end

    `ifndef SYNTHESIS
    `ifndef VERILATOR
    // assert that cache only hits on one way
    assert property (
      @(posedge clk_i) $onehot0(evict_way_q)) else $warning("Evict-way should be one-hot encoded");
    `endif
    `endif
    // ----------------------
    // Bypass Arbiter
    // ----------------------
    // Connection Arbiter <-> AXI
    logic                                     req_fsm_bypass_valid;
    logic [63:0]                              req_fsm_bypass_addr;
    logic [63:0]              req_fsm_bypass_wdata;
    logic                                     req_fsm_bypass_we;
    logic [7:0]          req_fsm_bypass_be;

    logic                                     gnt_bypass_fsm;
    logic                                     valid_bypass_fsm;
    logic [63:0]   data_bypass_fsm;
    logic [$clog2(NR_PORTS)-1:0]              id_fsm_bypass;
    logic [AXI_ID_WIDTH-1:0]                  id_bypass_fsm;

    arbiter #(
        .NR_PORTS          ( NR_PORTS                                                ),
        .DATA_WIDTH        ( 64                                                      )
    ) i_bypass_arbiter (
        // Master Side
        .data_req_i            ( miss_req_valid & miss_req_bypass                         ),
        .address_i             ( miss_req_addr                                            ),
        .data_wdata_i          ( miss_req_wdata                                           ),
        .data_we_i             ( miss_req_we                                              ),
        .data_be_i             ( miss_req_be                                              ),
        .data_gnt_o            ( bypass_gnt_o                                             ),
        .data_rvalid_o         ( bypass_valid_o                                           ),
        .data_rdata_o          ( bypass_data_o                                            ),
        // Slave Sid
        .id_i                  ( id_bypass_fsm[$clog2(NR_PORTS)-1:0]                      ),
        .id_o                  ( id_fsm_bypass                                            ),
        .address_o             ( req_fsm_bypass_addr                                      ),
        .data_wdata_o          ( req_fsm_bypass_wdata                                     ),
        .data_req_o            ( req_fsm_bypass_valid                                     ),
        .data_we_o             ( req_fsm_bypass_we                                        ),
        .data_be_o             ( req_fsm_bypass_be                                        ),
        .data_gnt_i            ( gnt_bypass_fsm                                           ),
        .data_rvalid_i         ( valid_bypass_fsm                                         ),
        .data_rdata_i          ( data_bypass_fsm                                          ),
        .*
    );

    axi_adapter #(
        .DATA_WIDTH            ( 64                                                       )
    ) i_bypass_axi_adapter (
        .req_i                 ( req_fsm_bypass_valid                                     ),
        .type_i                ( SINGLE_REQ                                               ),
        .gnt_o                 ( gnt_bypass_fsm                                           ),
        .addr_i                ( req_fsm_bypass_addr                                      ),
        .we_i                  ( req_fsm_bypass_we                                        ),
        .wdata_i               ( req_fsm_bypass_wdata                                     ),
        .be_i                  ( req_fsm_bypass_be                                        ),
        .id_i                  ( {{{AXI_ID_WIDTH-$clog2(NR_PORTS)}{1'b0}}, id_fsm_bypass} ),
        .valid_o               ( valid_bypass_fsm                                         ),
        .rdata_o               ( data_bypass_fsm                                          ),
        .id_o                  ( id_bypass_fsm                                            ),
        .critical_word_o       (                                                          ), // not used for single requests
        .critical_word_valid_o (                                                          ), // not used for single requests
        .axi                   ( bypass_if                                                ),
        .*
    );

    // ----------------------
    // Cache Line Arbiter
    // ----------------------
    axi_adapter  #(
        .DATA_WIDTH          ( CACHE_LINE_WIDTH   )
    ) i_miss_axi_adapter (
        .req_i               ( req_fsm_miss_valid ),
        .type_i              ( CACHE_LINE_REQ     ),
        .gnt_o               ( gnt_miss_fsm       ),
        .addr_i              ( req_fsm_miss_addr  ),
        .we_i                ( req_fsm_miss_we    ),
        .wdata_i             ( req_fsm_miss_wdata ),
        .be_i                ( req_fsm_miss_be    ),
        .id_i                ( '0                 ),
        .valid_o             ( valid_miss_fsm     ),
        .rdata_o             ( data_miss_fsm      ),
        .id_o                (                    ),
        .axi                 ( data_if            ),
        .*
    );

    // -----------------
    // Replacement LFSR
    // -----------------
    lfsr i_lfsr (
        .en_i           ( lfsr_enable ),
        .refill_way_oh  ( lfsr_oh     ),
        .refill_way_bin ( lfsr_bin    ),
        .*
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
        end
    end

    `ifndef SYNTHESIS
        initial begin
            assert (AXI_ID_WIDTH >= $clog2(NR_PORTS)) else $fatal (1, "AXI ID Width needs to be larger than number of requestors");
        end
    `endif

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
    output logic [NR_PORTS-1:0]                    data_gnt_o,
    output logic [NR_PORTS-1:0]                    data_rvalid_o,
    output logic [NR_PORTS-1:0][DATA_WIDTH-1:0]    data_rdata_o,
    // slave port
    input  logic [$clog2(NR_PORTS)-1:0]            id_i,
    output logic [$clog2(NR_PORTS)-1:0]            id_o,
    output logic                                   data_req_o,
    output logic [63:0]                            address_o,
    output logic [DATA_WIDTH-1:0]                  data_wdata_o,
    output logic                                   data_we_o,
    output logic [DATA_WIDTH/8-1:0]                data_be_o,
    input  logic                                   data_gnt_i,
    input  logic                                   data_rvalid_i,
    input  logic [DATA_WIDTH-1:0]                  data_rdata_i
);


    // addressing read and full write
    always_comb begin : read_req_write
        automatic logic [$clog2(NR_PORTS)-1:0] request_index;
        request_index = 0;

        data_req_o = 1'b0;
        data_gnt_o = '0;

        for (int unsigned i = 0; i < NR_PORTS; i++) begin
            if (data_req_i[i] == 1'b1) begin
                data_req_o        = data_req_i[i];
                request_index     = i;
                break; // break here as this is a priority select
            end
        end

        // pass through all signals from the correct slave port
        address_o                 = address_i[request_index];
        data_wdata_o              = data_wdata_i[request_index];
        data_be_o                 = data_be_i[request_index];
        data_we_o                 = data_we_i[request_index];
        data_gnt_o[request_index] = data_gnt_i;
        id_o                      = request_index;
    end

    // ------------
    // Read port
    // ------------

    always_comb begin : slave_read_port
        data_rvalid_o = '0;
        data_rdata_o = '0;
        // if there is a valid signal the FIFO should not be empty anyway
        if (data_rvalid_i) begin
            data_rvalid_o[id_i] = data_rvalid_i;
            data_rdata_o [id_i] = data_rdata_i;
        end
    end

    // ------------
    // Assertions
    // ------------

    `ifndef SYNTHESIS
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
    `endif
endmodule
// --------------
// AXI Adapter
// --------------
//
// Description: Manages communication with the AXI Bus
//
module axi_adapter #(
        parameter int unsigned DATA_WIDTH          = 256,
        parameter logic        CRITICAL_WORD_FIRST = 1 // the AXI subsystem needs to support wrapping reads for this feature
    )(
    input  logic                                        clk_i,  // Clock
    input  logic                                        rst_ni, // Asynchronous reset active low

    input  logic                                        req_i,
    input  req_t                                        type_i,
    output logic                                        gnt_o,
    input  logic [63:0]                                 addr_i,
    input  logic                                        we_i,
    input  logic [(DATA_WIDTH/64)-1:0][63:0]            wdata_i,
    input  logic [(DATA_WIDTH/64)-1:0][7:0]             be_i,
    input  logic [AXI_ID_WIDTH-1:0]                     id_i,
    // read port
    output logic                                        valid_o,
    output logic [(DATA_WIDTH/64)-1:0][63:0]            rdata_o,
    output logic [AXI_ID_WIDTH-1:0]                     id_o,
    // critical word - read port
    output logic [63:0]                                 critical_word_o,
    output logic                                        critical_word_valid_o,
    // AXI port
    AXI_BUS.Master                                      axi
);
    localparam BURST_SIZE = DATA_WIDTH/64-1;
    localparam ADDR_INDEX = ($clog2(DATA_WIDTH/64) > 0) ? $clog2(DATA_WIDTH/64) : 1;

    enum logic [3:0] {
        IDLE, WAIT_B_VALID, WAIT_AW_READY, WAIT_LAST_W_READY, WAIT_LAST_W_READY_AW_READY, WAIT_AW_READY_BURST,
        WAIT_R_VALID, WAIT_R_VALID_MULTIPLE, COMPLETE_READ
    } state_q, state_d;

    // counter for AXI transfers
    logic [$clog2(DATA_WIDTH/64)-1:0] cnt_d, cnt_q;
    logic [(DATA_WIDTH/64)-1:0][63:0] cache_line_d, cache_line_q;
    // save the address for a read, as we allow for non-cacheline aligned accesses
    logic [(DATA_WIDTH/64)-1:0] addr_offset_d, addr_offset_q;
    logic [AXI_ID_WIDTH-1:0]    id_d, id_q;
    logic [ADDR_INDEX-1:0]      index;

    always_comb begin : axi_fsm
        // Default assignments
        axi.aw_valid  = 1'b0;
        axi.aw_addr   = addr_i;
        axi.aw_prot   = 3'b0;
        axi.aw_region = 4'b0;
        axi.aw_len    = 8'b0;
        axi.aw_size   = 3'b011; // 8 bytes
        axi.aw_burst  = (type_i == SINGLE_REQ) ? 2'b00 :  2'b01;  // fixed size for single request and incremental transfer for everything else
        axi.aw_lock   = 1'b0;
        axi.aw_cache  = 4'b0;
        axi.aw_qos    = 4'b0;
        axi.aw_id     = id_i;
        axi.aw_user   = '0;

        axi.ar_valid  = 1'b0;
        // in case of a single request or wrapping transfer we can simply begin at the address, if we want to request a cache-line
        // with an incremental transfer we need to output the corresponding base address of the cache line
        axi.ar_addr   = (CRITICAL_WORD_FIRST || type_i == SINGLE_REQ) ? addr_i : { addr_i[63:BYTE_OFFSET], {{BYTE_OFFSET}{1'b0}}};
        axi.ar_prot   = 3'b0;
        axi.ar_region = 4'b0;
        axi.ar_len    = 8'b0;
        axi.ar_size   = 3'b011; // 8 bytes
        axi.ar_burst  = (type_i == SINGLE_REQ) ? 2'b00 : (CRITICAL_WORD_FIRST ? 2'b10 : 2'b01);  // wrapping transfer in case of a critical word first strategy
        axi.ar_lock   = 1'b0;
        axi.ar_cache  = 4'b0;
        axi.ar_qos    = 4'b0;
        axi.ar_id     = id_i;
        axi.ar_user   = '0;

        axi.w_valid   = 1'b0;
        axi.w_data    = wdata_i[0];
        axi.w_strb    = be_i[0];
        axi.w_user    = '0;
        axi.w_last    = 1'b0;

        axi.b_ready   = 1'b0;
        axi.r_ready   = 1'b0;

        gnt_o         = 1'b0;
        valid_o       = 1'b0;
        id_o          = axi.r_id;

        // rdata_o   = axi.r_data;
        critical_word_o         = axi.r_data;
        critical_word_valid_o   = 1'b0;
        rdata_o                 = cache_line_q;

        state_d                 = state_q;
        cnt_d                   = cnt_q;
        cache_line_d            = cache_line_q;
        addr_offset_d           = addr_offset_q;
        id_d                    = id_q;

        case (state_q)

            IDLE: begin
                cnt_d = '0;
                // we have an incoming request
                if (req_i) begin
                    // is this a read or write?
                    // write
                    if (we_i) begin
                        // the data is valid
                        axi.aw_valid = 1'b1;
                        axi.w_valid  = 1'b1;
                        // its a single write
                        if (type_i == SINGLE_REQ) begin
                            // single req can be granted here
                            gnt_o = axi.aw_ready & axi.w_ready;

                            case ({axi.aw_ready, axi.w_ready})
                                2'b11: state_d = WAIT_B_VALID;
                                2'b01: state_d = WAIT_AW_READY;
                                2'b10: state_d = WAIT_LAST_W_READY;
                                default: state_d = IDLE;
                            endcase
                        // its a request for the whole cache line
                        end else begin
                            axi.aw_len = BURST_SIZE; // number of bursts to do
                            axi.w_last = 1'b0;
                            axi.w_data = wdata_i[0];
                            axi.w_strb = be_i[0];

                            if (axi.w_ready)
                                cnt_d = BURST_SIZE - 1;
                            else
                                cnt_d = BURST_SIZE;

                            case ({axi.aw_ready, axi.w_ready})
                                2'b11: state_d = WAIT_LAST_W_READY;
                                2'b01: state_d = WAIT_LAST_W_READY_AW_READY;
                                2'b10: state_d = WAIT_LAST_W_READY;
                                default:;
                            endcase
                        end
                    // read
                    end else begin

                        axi.ar_valid = 1'b1;
                        gnt_o = axi.ar_ready;

                        if (type_i != SINGLE_REQ) begin
                            axi.ar_len = BURST_SIZE;
                            cnt_d = BURST_SIZE;
                        end

                        if (axi.ar_ready) begin
                            state_d = (type_i == SINGLE_REQ) ? WAIT_R_VALID : WAIT_R_VALID_MULTIPLE;
                            addr_offset_d = addr_i[ADDR_INDEX-1+3:3];
                        end
                    end
                end
            end

            // ~> from single write, write request has already been granted
            WAIT_AW_READY: begin
                axi.aw_valid = 1'b1;
                axi.aw_len   = 8'b0;

                if (axi.aw_ready)
                    state_d = WAIT_B_VALID;

            end

            // ~> we need to wait for an aw_ready and there is at least one outstanding write
            WAIT_LAST_W_READY_AW_READY: begin

                axi.w_valid  = 1'b1;
                axi.w_last   = (cnt_q == '0) ? 1'b1 : 1'b0;
                axi.w_data   = wdata_i[BURST_SIZE-cnt_q];
                axi.w_strb   = be_i[BURST_SIZE-cnt_q];

                axi.aw_valid = 1'b1;
                // we are here because we want to write a cache line
                axi.aw_len   = DATA_WIDTH/64;
                // we got an aw_ready
                case ({axi.aw_ready, axi.w_ready})
                    // we got an aw ready
                    2'b01: begin
                        // are there any outstanding transactions?
                        if (cnt_q == 0)
                            state_d = WAIT_AW_READY_BURST;
                        else // yes, so reduce the count and stay here
                            cnt_d = cnt_q - 1;
                    end
                    2'b10: state_d = WAIT_LAST_W_READY;
                    2'b11: begin
                        // we are finished
                        if (cnt_q == 0) begin
                            state_d = WAIT_B_VALID;
                            gnt_o = 1'b1;
                        // there are outstanding transactions
                        end else begin
                            state_d = WAIT_LAST_W_READY;
                            cnt_d = cnt_q - 1;
                        end
                    end
                    default:;
               endcase

            end

            // ~> all data has already been sent, we are only waiting for the aw_ready
            WAIT_AW_READY_BURST: begin
                axi.aw_valid = 1'b1;
                axi.aw_len   = DATA_WIDTH/64;

                if (axi.aw_ready) begin
                    state_d = WAIT_B_VALID;
                    gnt_o = 1'b1;
                end
            end

            // ~> from write, there is an outstanding write
            WAIT_LAST_W_READY: begin
                axi.w_valid = 1'b1;
                axi.w_data  = wdata_i[BURST_SIZE-cnt_q];
                axi.w_strb  = be_i[BURST_SIZE-cnt_q];

                // this is the last write
                axi.w_last  = (cnt_q == '0) ? 1'b1 : 1'b0;

                if (axi.w_ready) begin
                    // last write -> go to WAIT_B_VALID
                    if (cnt_q == '0) begin
                        state_d = WAIT_B_VALID;
                        gnt_o = (cnt_q == '0);
                    end else begin
                        cnt_d = cnt_q - 1;
                    end
                end
            end

            // ~> finish write transaction
            WAIT_B_VALID: begin
                axi.b_ready = 1'b1;
                id_o = axi.b_id;

                // Write is valid
                if (axi.b_valid) begin
                    state_d = IDLE;
                    valid_o = 1'b1;
                end
            end

            // ~> cacheline read, single read
            WAIT_R_VALID_MULTIPLE, WAIT_R_VALID: begin
                if (CRITICAL_WORD_FIRST)
                    index = addr_offset_q + (BURST_SIZE-cnt_q);
                else
                    index = BURST_SIZE-cnt_q;

                // reads are always wrapping here
                axi.r_ready = 1'b1;
                // this is the first read a.k.a the critical word
                if (axi.r_valid) begin
                    if (CRITICAL_WORD_FIRST) begin
                        // this is the first word of a cacheline read, e.g.: the word which was causing the miss
                        if (state_q == WAIT_R_VALID_MULTIPLE && cnt_q == BURST_SIZE) begin
                            critical_word_valid_o = 1'b1;
                            critical_word_o       = axi.r_data;
                        end
                    end else begin
                        // check if the address offset matches - then we are getting the critical word
                        if (index == addr_offset_q) begin
                            critical_word_valid_o = 1'b1;
                            critical_word_o       = axi.r_data;
                        end
                    end

                    // this is the last read
                    if (axi.r_last) begin
                        state_d = COMPLETE_READ;
                        // save id
                        id_d = axi.r_id;
                    end

                    // save the word
                    if (state_q == WAIT_R_VALID_MULTIPLE) begin
                        cache_line_d[index] = axi.r_data;

                    end else
                        cache_line_d[0] = axi.r_data;

                    // Decrease the counter
                    cnt_d = cnt_q - 1;
                end
            end
            // ~> read is complete
            COMPLETE_READ: begin
                valid_o = 1'b1;
                state_d = IDLE;
                id_o    = id_q;
            end
        endcase
    end

    // ----------------
    // Registers
    // ----------------
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (~rst_ni) begin
            // start in flushing state and initialize the memory
            state_q       <= IDLE;
            cnt_q         <= '0;
            cache_line_q  <= '0;
            addr_offset_q <= '0;
            id_q          <= '0;
        end else begin
            state_q       <= state_d;
            cnt_q         <= cnt_d;
            cache_line_q  <= cache_line_d;
            addr_offset_q <= addr_offset_d;
            id_q          <= id_d;
        end
    end

endmodule

// --------------
// 8-bit LFSR
// --------------
//
// Description: Shift register for way selection
//
module lfsr #(
        parameter logic [7:0]  SEED = 8'b0
    )(
        input  logic                                  clk_i,
        input  logic                                  rst_ni,
        input  logic                                  en_i,
        output logic [SET_ASSOCIATIVITY-1:0]          refill_way_oh,
        output logic [$clog2(SET_ASSOCIATIVITY)-1:0]  refill_way_bin
    );

    localparam int unsigned LOG_SET_ASSOCIATIVITY = $clog2(SET_ASSOCIATIVITY);

    logic [7:0] shift_d, shift_q;


    always_comb begin

        automatic logic shift_in;
        shift_in = !(shift_q[7] ^ shift_q[3] ^ shift_q[2] ^ shift_q[1]);

        shift_d = shift_q;

        if (en_i)
            shift_d = {shift_q[6:0], shift_in};

        // output assignment
        refill_way_oh = 'b0;
        refill_way_oh[shift_q[LOG_SET_ASSOCIATIVITY-1:0]] = 1'b1;
        refill_way_bin = shift_q;
    end

    always_ff @(posedge clk_i or negedge rst_ni) begin : proc_
        if(~rst_ni) begin
            shift_q <= SEED;
        end else begin
            shift_q <= shift_d;
        end
    end

    `ifndef SYNTHESIS
        initial begin
            assert (SET_ASSOCIATIVITY <= 8) else $fatal(1, "SET_ASSOCIATIVITY needs to be less than 8 because of the 8-bit LFSR");
        end
    `endif

endmodule

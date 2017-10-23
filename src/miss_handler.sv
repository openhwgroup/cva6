// --------------
// MISS Handler
// --------------
//
// Description: Handles cache misses.
//
import nbdcache_pkg::*;

module miss_handler #(
    parameter int unsigned NR_PORTS          = 3,
    parameter int unsigned CACHE_LINE_WIDTH  = 256,
    parameter int unsigned AXI_ID_WIDTH      = 10,
    parameter int unsigned AXI_USER_WIDTH    = 10
)(
    input  logic                                        clk_i,
    input  logic                                        rst_ni,
    input  logic [NR_PORTS-1:0][$bits(miss_req_t)-1:0]  miss_req_i,
    output logic [NR_PORTS-1:0]                         miss_gnt_o,
    output logic [NR_PORTS-1:0]                         miss_valid_o,
    output logic [NR_PORTS-1:0][63:0]                   miss_data_o,
    AXI_BUS.Master                                      bypass_if
    // update cache
);

    // ------------------
    // Cacheline Refills
    // ------------------

    // ------------------
    // Bypass
    // ------------------
    // AXI Adapter
    // request from FSM


    logic [NR_PORTS-1:0]        miss_req_valid;
    logic [NR_PORTS-1:0]        miss_req_bypass;
    logic [NR_PORTS-1:0][63:0]  miss_req_addr;
    logic [NR_PORTS-1:0][63:0]  miss_req_wdata;
    logic [NR_PORTS-1:0]        miss_req_we;
    logic [NR_PORTS-1:0][7:0]   miss_req_be;

    logic         req_fsm_bypass_valid;
    logic         req_fsm_bypass_bypass;
    logic [63:0]  req_fsm_bypass_addr;
    logic [63:0]  req_fsm_bypass_wdata;
    logic         req_fsm_bypass_we;
    logic [7:0]   req_fsm_bypass_be;

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


    logic                                     gnt_bypass_fsm;
    logic                                     valid_bypass_fsm;
    logic [(CACHE_LINE_WIDTH/64)-1:0][63:0]   data_bypass_fsm;
    logic [$clog2(NR_PORTS)-1:0]              id_fsm_bypass;
    logic [AXI_ID_WIDTH-1:0]                  id_bypass_fsm;

    miss_arbiter #(
            .NR_PORTS  ( NR_PORTS                             )
        ) i_bypass_arbiter (
        // Master Side
        .data_req_i    ( miss_req_valid & miss_req_bypass     ),
        .address_i     ( miss_req_addr                        ),
        .data_wdata_i  ( miss_req_wdata                       ),
        .data_we_i     ( miss_req_we                          ),
        .data_be_i     ( miss_req_be                          ),
        .data_gnt_o    ( miss_gnt_o                           ),
        .data_rvalid_o ( miss_valid_o                         ),
        .data_rdata_o  ( miss_data_o                          ),
        // Slave Side
        .id_i          ( id_bypass_fsm[$clog2(NR_PORTS)-1:0]  ),
        .id_o          ( id_fsm_bypass                        ),
        .address_o     ( req_fsm_bypass_addr                  ),
        .data_wdata_o  ( req_fsm_bypass_wdata                 ),
        .data_req_o    ( req_fsm_bypass_valid                 ),
        .data_we_o     ( req_fsm_bypass_we                    ),
        .data_be_o     ( req_fsm_bypass_be                    ),
        .data_gnt_i    ( gnt_bypass_fsm                       ),
        .data_rvalid_i ( valid_bypass_fsm                     ),
        .data_rdata_i  ( data_bypass_fsm[0]                   ),
        .*
    );

    axi_adapter #(
        .CACHE_LINE_WIDTH   ( CACHE_LINE_WIDTH ),
        .AXI_ID_WIDTH       ( AXI_ID_WIDTH     ),
        .AXI_USER_WIDTH     ( AXI_USER_WIDTH   )
    ) i_bypass_axi_adapter (
        .req_i               ( req_fsm_bypass_valid                                     ),
        .type_i              ( SINGLE_REQ                                               ),
        .gnt_o               ( gnt_bypass_fsm                                           ),
        .addr_i              ( req_fsm_bypass_addr                                      ),
        .we_i                ( req_fsm_bypass_we                                        ),
        .wdata_i             ( {{{CACHE_LINE_WIDTH-64}{1'b0}}, req_fsm_bypass_wdata}    ),
        .be_i                ( {{{CACHE_LINE_WIDTH/8-8}{1'b0}}, req_fsm_bypass_be}      ),
        .id_i                ( {{{AXI_ID_WIDTH-$clog2(NR_PORTS)}{1'b0}}, id_fsm_bypass} ),
        .valid_o             ( valid_bypass_fsm                                         ),
        .rdata_o             ( data_bypass_fsm                                          ),
        .id_o                ( id_bypass_fsm                                            ),
        .critical_word_o     (                                                          ), // not used for single requests
        .critical_word_valid (                                                          ), // not used for single requests
        .axi                 ( bypass_if                                                ),
        .*
    );

endmodule

module miss_arbiter #(
        parameter int unsigned NR_PORTS = 3
)(
    input  logic                           clk_i,          // Clock
    input  logic                           rst_ni,         // Asynchronous reset active low
    // master ports
    input  logic [NR_PORTS-1:0]            data_req_i,
    input  logic [NR_PORTS-1:0][63:0]      address_i,
    input  logic [NR_PORTS-1:0][63:0]      data_wdata_i,
    input  logic [NR_PORTS-1:0]            data_we_i,
    input  logic [NR_PORTS-1:0][7:0]       data_be_i,
    output logic [NR_PORTS-1:0]            data_gnt_o,
    output logic [NR_PORTS-1:0]            data_rvalid_o,
    output logic [NR_PORTS-1:0][63:0]      data_rdata_o,
    // slave port
    input  logic [$clog2(NR_PORTS)-1:0]    id_i,
    output logic [$clog2(NR_PORTS)-1:0]    id_o,
    output logic                           data_req_o,
    output logic [63:0]                    address_o,
    output logic [63:0]                    data_wdata_o,
    output logic                           data_we_o,
    output logic [7:0]                     data_be_o,
    input  logic                           data_gnt_i,
    input  logic                           data_rvalid_i,
    input  logic [63:0]                    data_rdata_i
);


    // addressing read and full write
    always_comb begin : read_req_write
        automatic logic [$clog2(NR_PORTS)-1:0] request_index = 0;

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

    // there should be no rvalid when we are in IDLE
    // assert property (
    //   @(posedge clk) (CS == IDLE) |-> (data_rvalid_i == 1'b0) )
    //   else begin $error("Received rvalid while in IDLE state"); $stop(); end

    // assert that errors are only sent at the same time as grant or rvalid
    // assert property ( @(posedge clk) (data_err_i) |-> (data_gnt_i || data_rvalid_i) )
    //   else begin $error("Error without data grant or rvalid"); $stop(); end

    `endif
    `endif
endmodule

module axi_adapter #(
    parameter int unsigned CACHE_LINE_WIDTH  = 256,
    parameter int unsigned AXI_ID_WIDTH      = 10,
    parameter int unsigned AXI_USER_WIDTH    = 10
)(
    input  logic                                        clk_i,  // Clock
    input  logic                                        rst_ni, // Asynchronous reset active low

    input  logic                                        req_i,
    input  req_t                                        type_i,
    output logic                                        gnt_o,
    input  logic [63:0]                                 addr_i,
    input  logic                                        we_i,
    input  logic [(CACHE_LINE_WIDTH/64)-1:0][63:0]      wdata_i,
    input  logic [(CACHE_LINE_WIDTH/64)-1:0][7:0]       be_i,
    input  logic [AXI_ID_WIDTH-1:0]                     id_i,
    // read port
    output logic                                        valid_o,
    output logic [(CACHE_LINE_WIDTH/64)-1:0][63:0]      rdata_o,
    output logic [AXI_ID_WIDTH-1:0]                     id_o,
    // critical word - read port
    output logic [63:0]                                 critical_word_o,
    output logic                                        critical_word_valid,
    // AXI port
    AXI_BUS.Master                                      axi
);
    localparam BURST_SIZE = CACHE_LINE_WIDTH/64;

    enum logic [3:0] {
        IDLE, WAIT_B_VALID, WAIT_AW_READY, WAIT_LAST_W_READY, WAIT_LAST_W_READY_AW_READY, WAIT_AW_READY_BURST,
        WAIT_R_VALID, WAIT_R_VALID_MULTIPLE, COMPLETE_READ
    } state_q, state_d;

    // counter for AXI transfers
    logic [$clog2(CACHE_LINE_WIDTH/64)-1:0] cnt_d, cnt_q;
    logic [(CACHE_LINE_WIDTH/64)-1:0][63:0] cache_line_d, cache_line_q;
    // save the address for a read, as we allow for non-cacheline aligned accesses
    logic [$clog2(CACHE_LINE_WIDTH/64)-1:0]  addr_offset_d, addr_offset_q;
    logic [AXI_ID_WIDTH-1:0]                 id_d, id_q;

    always_comb begin : axi_fsm
        // Default assignments
        axi.aw_valid  = 1'b0;
        axi.aw_addr   = addr_i;
        axi.aw_prot   = 3'b0;
        axi.aw_region = 4'b0;
        axi.aw_len    = 8'b0;
        axi.aw_size   = 3'b011; // 8 bytes
        axi.aw_burst  = 2'b01;  // incremental transfer
        axi.aw_lock   = 1'b0;
        axi.aw_cache  = 4'b0;
        axi.aw_qos    = 4'b0;
        axi.aw_id     = id_i;
        axi.aw_user   = '0;

        axi.ar_valid  = 1'b0;
        axi.ar_addr   = addr_i;
        axi.ar_prot   = 3'b0;
        axi.ar_region = 4'b0;
        axi.ar_len    = 8'b0;
        axi.ar_size   = 3'b011; // 8 bytes
        axi.ar_burst  = 2'b10;  // wrapping transfer
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
        critical_word_o       = axi.r_data;
        critical_word_valid   = 1'b0;
        rdata_o               = cache_line_q;

        state_d       = state_q;
        cnt_d         = cnt_q;
        cache_line_d  = cache_line_q;
        addr_offset_d = addr_offset_q;
        id_d          = id_q;

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
                            axi.ar_len = CACHE_LINE_WIDTH/64;
                            cnt_d = CACHE_LINE_WIDTH/64 - 1;
                        end

                        if (axi.ar_ready) begin
                            state_d = (type_i == SINGLE_REQ) ? WAIT_R_VALID : WAIT_R_VALID_MULTIPLE;
                            addr_offset_d = addr_i[$clog2(CACHE_LINE_WIDTH/64)-1:0];
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
                axi.aw_len   = CACHE_LINE_WIDTH/64;
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
                axi.aw_len   = CACHE_LINE_WIDTH/64;

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
                gnt_o = (cnt_q == '0);

                if (axi.w_ready) begin
                    // last write -> go to WAIT_B_VALID
                    if (cnt_q == '0)
                        state_d = WAIT_B_VALID;
                    else
                        cnt_d = cnt_q - 1;
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
                // reads are always wrapping here
                axi.r_ready = 1'b1;
                // this is the first read a.k.a the critical word
                if (axi.r_valid) begin
                    // this is the first word of a cacheline read
                    if (state_q == WAIT_R_VALID_MULTIPLE) begin
                        critical_word_valid = 1'b1;
                        critical_word_o     = axi.r_data;
                    end
                    // this is the last read
                    if (axi.r_last) begin
                        state_d = COMPLETE_READ;
                        // save id
                        id_d = axi.r_id;
                    end

                    // save the word
                    if (state_q == WAIT_R_VALID_MULTIPLE)
                        cache_line_d[addr_offset_q + cnt_q] = axi.r_data;
                    else
                        cache_line_d[0] = axi.r_data;
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

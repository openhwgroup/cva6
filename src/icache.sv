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
// Author:       Igor Loi - igor.loi@unibo.it
//
// Additional contributions by:
//
// Create Date:    22/03/2016
// Module Name:    icache
// Language:       SystemVerilog
//
// Description:    Top module for the private instruction cache, which instantiates
//                 the cache controller and the refill compactor
//
// Revision:
// Revision v0.1 - File Created
// Revision v0.2 - Remove SCMs

module icache #(
    parameter int unsigned FETCH_ADDR_WIDTH = 56,       // Size of the fetch address
    parameter int unsigned FETCH_DATA_WIDTH = 64,       // Size of the fetch data
    parameter int unsigned ID_WIDTH         = 4,

    parameter int unsigned AXI_ADDR_WIDTH   = 64,
    parameter int unsigned AXI_DATA_WIDTH   = 64,
    parameter int unsigned AXI_USER_WIDTH   = 6,
    parameter int unsigned AXI_ID_WIDTH     = ID_WIDTH,
    parameter int unsigned SLICE_DEPTH      = 2,
    parameter int unsigned AXI_STRB_WIDTH   = AXI_DATA_WIDTH/8,

    parameter int unsigned NB_BANKS         = 1,        // Number of Cache Banks : DO NOT CHANGE
    parameter int unsigned NB_WAYS          = 4,        // Cache associativity
    parameter int unsigned CACHE_SIZE       = 16*1024,  // Ccache capacity in Byte
    parameter int unsigned CACHE_LINE       = 2         // in word of [FETCH_DATA_WIDTH]
)(
    input logic                            clk_i,
    input logic                            rst_n,
    input logic                            test_en_i,
    // interface with processor
    input  logic                           fetch_req_i,
    input  logic [FETCH_ADDR_WIDTH-1:0]    fetch_addr_i,
    output logic                           fetch_gnt_o,
    output logic                           fetch_rvalid_o,
    output logic [FETCH_DATA_WIDTH-1:0]    fetch_rdata_o,

    AXI_BUS.Master                         axi,                 // refill port

    input  logic                           bypass_icache_i,
    output logic                           cache_is_bypassed_o,
    input  logic                           flush_icache_i,
    output logic                           cache_is_flushed_o,
    input  logic                           flush_set_ID_req_i,
    input  logic [FETCH_ADDR_WIDTH-1:0]    flush_set_ID_addr_i,
    output logic                           flush_set_ID_ack_o
);
    localparam OFFSET             = $clog2(FETCH_DATA_WIDTH)-3;
    localparam WAY_SIZE           = CACHE_SIZE/NB_WAYS;
    localparam SCM_NUM_ROWS       = WAY_SIZE/(CACHE_LINE*FETCH_DATA_WIDTH/8); // TAG
    localparam SCM_TAG_ADDR_WIDTH = $clog2(SCM_NUM_ROWS);

    localparam TAG_WIDTH          = (FETCH_ADDR_WIDTH - SCM_TAG_ADDR_WIDTH - $clog2(CACHE_LINE) - OFFSET + 1);

    localparam DATA_WIDTH          = FETCH_DATA_WIDTH;
    localparam SCM_DATA_ADDR_WIDTH = $clog2(SCM_NUM_ROWS)+$clog2(CACHE_LINE);  // Because of 64 Access

    localparam SET_ID_LSB          = $clog2(DATA_WIDTH*CACHE_LINE)-3;
    localparam SET_ID_MSB          = SET_ID_LSB + SCM_TAG_ADDR_WIDTH - 1;
    localparam TAG_LSB             = SET_ID_MSB + 1;
    localparam TAG_MSB             = TAG_LSB + TAG_WIDTH - 2 ; //1 bit is count for valid

    // interface with READ PORT --> SCM DATA
    logic [NB_WAYS-1:0]                    DATA_req_int;
    logic                                  DATA_we_int;
    logic [SCM_DATA_ADDR_WIDTH-1:0]        DATA_addr_int;
    logic [NB_WAYS-1:0][DATA_WIDTH-1:0]    DATA_rdata_int;
    logic [DATA_WIDTH-1:0]                 DATA_wdata_int;

    // interface with READ PORT --> SCM TAG
    logic [NB_WAYS-1:0]                    TAG_req_int;
    logic                                  TAG_we_int;
    logic [SCM_TAG_ADDR_WIDTH-1:0]         TAG_addr_int;
    logic [NB_WAYS-1:0][TAG_WIDTH-1:0]     TAG_rdata_int;
    logic [TAG_WIDTH-1:0]                  TAG_wdata_int;

    logic                                  refill_req_to_comp;
    logic                                  refill_type_to_comp;
    logic                                  refill_gnt_from_comp;
    logic [FETCH_ADDR_WIDTH-1:0]           refill_addr_to_comp;
    logic [ID_WIDTH-1:0]                   refill_ID_to_comp;

    logic                                  refill_r_valid_from_comp;
    logic                                  refill_r_last_from_comp;
    logic [FETCH_DATA_WIDTH-1:0]           refill_r_rdata_from_comp;
    logic [ID_WIDTH-1:0]                   refill_r_ID_from_comp;

/*
    logic [NB_WAYS-1:0]                    DATA_read_enable;
    logic [NB_WAYS-1:0]                    DATA_write_enable;

    logic [NB_WAYS-1:0]                    TAG_read_enable;
    logic [NB_WAYS-1:0]                    TAG_write_enable;
*/
    icache_controller #(
        .FETCH_ADDR_WIDTH         ( FETCH_ADDR_WIDTH         ),
        .FETCH_DATA_WIDTH         ( FETCH_DATA_WIDTH         ),

        .NB_CORES                 ( 1                        ),
        .NB_WAYS                  ( NB_WAYS                  ),
        .CACHE_LINE               ( CACHE_LINE               ),

        .SCM_TAG_ADDR_WIDTH       ( SCM_TAG_ADDR_WIDTH       ),
        .SCM_DATA_ADDR_WIDTH      ( SCM_DATA_ADDR_WIDTH      ),
        .SCM_TAG_WIDTH            ( TAG_WIDTH                ),
        .SCM_DATA_WIDTH           ( DATA_WIDTH               ),

        .SET_ID_LSB               ( SET_ID_LSB               ),
        .SET_ID_MSB               ( SET_ID_MSB               ),
        .TAG_LSB                  ( TAG_LSB                  ),
        .TAG_MSB                  ( TAG_MSB                  )
   ) i_icache_controller_private (
        .clk                      ( clk_i                      ),
        .rst_n                    ( rst_n                    ),

        .bypass_icache_i          ( bypass_icache_i          ),
        .cache_is_bypassed_o      ( cache_is_bypassed_o      ),
        .flush_icache_i           ( flush_icache_i           ),
        .cache_is_flushed_o       ( cache_is_flushed_o       ),
        .flush_set_ID_req_i       ( flush_set_ID_req_i       ),
        .flush_set_ID_addr_i      ( flush_set_ID_addr_i      ),
        .flush_set_ID_ack_o       ( flush_set_ID_ack_o       ),


        // interface with processor
        .fetch_req_i              ( fetch_req_i              ),
        .fetch_addr_i             ( fetch_addr_i             ),
        .fetch_gnt_o              ( fetch_gnt_o              ),
        .fetch_rvalid_o           ( fetch_rvalid_o           ),
        .fetch_rdata_o            ( fetch_rdata_o            ),


        // interface with READ PORT --> SCM DATA
        .DATA_req_o               ( DATA_req_int             ),
        .DATA_we_o                ( DATA_we_int              ),
        .DATA_addr_o              ( DATA_addr_int            ),
        .DATA_rdata_i             ( DATA_rdata_int           ),
        .DATA_wdata_o             ( DATA_wdata_int           ),

        // interface with READ PORT --> SCM TAG
        .TAG_req_o                ( TAG_req_int              ),
        .TAG_addr_o               ( TAG_addr_int             ),
        .TAG_rdata_i              ( TAG_rdata_int            ),
        .TAG_wdata_o              ( TAG_wdata_int            ),
        .TAG_we_o                 ( TAG_we_int               ),

        // Interface to cache_controller_to uDMA L2 port
        .refill_req_o             ( refill_req_to_comp       ),
        .refill_type_o            ( refill_type_to_comp      ),
        .refill_gnt_i             ( refill_gnt_from_comp     ),
        .refill_addr_o            ( refill_addr_to_comp      ),

        .refill_r_valid_i         ( refill_r_valid_from_comp ),
        .refill_r_last_i          ( refill_r_last_from_comp  ),
        .refill_r_data_i          ( refill_r_rdata_from_comp )
   );

   logic [NB_WAYS-1:0] dummy_bit;
   generate
      for (genvar i = 0; i < NB_WAYS; i++) begin : sram_block

        // ------------
        // Tag RAM
        // ------------
        sram #(
            .DATA_WIDTH ( 46  ),
            .NUM_WORDS  ( 256 )
        ) tag_sram (
            .clk_i     ( clk_i                            ),
            .req_i     ( TAG_req_int[i]                   ),
            .we_i      ( TAG_we_int                       ),
            .addr_i    ( TAG_addr_int                     ),
            .wdata_i   ( {1'b0, TAG_wdata_int}            ),
            .be_i      ( '1                               ),
            .rdata_o   ( {dummy_bit[i], TAG_rdata_int[i]} )
        );

        // ------------
        // Data RAM
        // ------------
        sram #(
            .DATA_WIDTH ( 64  ),
            .NUM_WORDS  ( 512 )
        ) data_sram (
            .clk_i     ( clk_i             ),
            .req_i     ( DATA_req_int[i]   ),
            .we_i      ( DATA_we_int       ),
            .addr_i    ( DATA_addr_int     ),
            .wdata_i   ( DATA_wdata_int    ),
            .be_i      ( '1                ),
            .rdata_o   ( DATA_rdata_int[i] )
        );
      end
   endgenerate

   assign refill_ID_to_comp = '0;

   lint_to_axi_refill #(
       .FETCH_ADDR_WIDTH ( FETCH_ADDR_WIDTH ), //= 56,
       .FETCH_DATA_WIDTH ( FETCH_DATA_WIDTH ), //= 64,
       .ID_WIDTH         ( ID_WIDTH         ), //= 5,

       .AXI_ADDR_WIDTH   ( AXI_ADDR_WIDTH   ), //= 64,
       .AXI_DATA_WIDTH   ( AXI_DATA_WIDTH   ), //= 64,
       .AXI_USER_WIDTH   ( AXI_USER_WIDTH   ), //= 6,
       .AXI_ID_WIDTH     ( AXI_ID_WIDTH     ), //= ID_WIDTH,
       .SLICE_DEPTH      ( SLICE_DEPTH      ), //= 2,
       .AXI_STRB_WIDTH   ( AXI_STRB_WIDTH   ) //= AXI_DATA_WIDTH/8
   ) lint_to_axi_refill_i (
        .clk_i                  ( clk_i                    ),
        .rst_n                  ( rst_n                    ),
        .test_en_i              ( test_en_i                ),

        // Interface between cache_controller_to  and Compactor
        .refill_req_i           ( refill_req_to_comp       ),
        .refill_type_i          ( refill_type_to_comp      ), // 0 | 1 : 0 --> 64 Bit ,  1--> 128bit
        .refill_gnt_o           ( refill_gnt_from_comp     ),
        .refill_addr_i          ( refill_addr_to_comp      ),
        .refill_ID_i            ( refill_ID_to_comp        ),

        .refill_r_valid_o       ( refill_r_valid_from_comp ),
        .refill_r_data_o        ( refill_r_rdata_from_comp ),
        .refill_r_last_o        ( refill_r_last_from_comp  ),
        .refill_r_ID_o          ( refill_r_ID_from_comp    ),

        .axi                    ( axi                      )
   );

endmodule

module lint_to_axi_refill #(
    parameter int unsigned FETCH_ADDR_WIDTH = 56,
    parameter int unsigned FETCH_DATA_WIDTH = 64,
    parameter int unsigned ID_WIDTH         = 5,

    parameter int unsigned AXI_ADDR_WIDTH   = 32,
    parameter int unsigned AXI_DATA_WIDTH   = 64,
    parameter int unsigned AXI_USER_WIDTH   = 6,
    parameter int unsigned AXI_ID_WIDTH     = ID_WIDTH,
    parameter int unsigned SLICE_DEPTH      = 2,
    parameter int unsigned AXI_STRB_WIDTH   = AXI_DATA_WIDTH/8
)(
   input  logic                         clk_i,
   input  logic                         rst_n,
   input  logic                         test_en_i,

   // Interface between cache_controller_to and Compactor
   input  logic                         refill_req_i,
   input  logic                         refill_type_i, // 0 | 1 : 0 --> 64 Bit ,  1--> 128bit
   output logic                         refill_gnt_o,
   input  logic [FETCH_ADDR_WIDTH-1:0]  refill_addr_i,
   input  logic [ID_WIDTH-1:0]          refill_ID_i,

   output logic                         refill_r_valid_o,
   output logic [FETCH_DATA_WIDTH-1:0]  refill_r_data_o,
   output logic                         refill_r_last_o,
   output logic [ID_WIDTH-1:0]          refill_r_ID_o,

   AXI_BUS.Master                       axi
);

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

    assign axi.ar_valid  = refill_req_i;
    assign axi.ar_addr   = refill_addr_i;
    assign axi.ar_prot   = '0;
    assign axi.ar_region = '0;
    assign axi.ar_len    = (refill_type_i) ? 8'h01 : 8'h00;
    assign axi.ar_size   = 3'b011;
    assign axi.ar_burst  = 2'b01;
    assign axi.ar_lock   = '0;
    assign axi.ar_cache  = '0;
    assign axi.ar_qos    = '0;
    assign axi.ar_id     = refill_ID_i;
    assign axi.ar_user   = '0;

    assign axi.r_ready   = 1'b1;

    assign refill_gnt_o     = axi.ar_ready;
    assign refill_r_valid_o = axi.r_valid;
    assign refill_r_ID_o    = axi.r_id;
    assign refill_r_data_o  = axi.r_data;
    assign refill_r_last_o  = axi.r_last;

endmodule

// Private instruction cache controller
// Author: Igor Loi - igor.loi@unibo.it
// Date: 22/03/2016
module icache_controller #(
   parameter FETCH_ADDR_WIDTH       = 56,
   parameter FETCH_DATA_WIDTH       = 64,

   parameter NB_CORES               = 4,
   parameter NB_WAYS                = 4,
   parameter CACHE_LINE             = 2,

   parameter SCM_TAG_ADDR_WIDTH     = 4,
   parameter SCM_DATA_ADDR_WIDTH    = 5,
   parameter SCM_TAG_WIDTH          = 8,
   parameter SCM_DATA_WIDTH         = FETCH_DATA_WIDTH,

   parameter SET_ID_LSB             = $clog2(FETCH_DATA_WIDTH*CACHE_LINE)-3,
   parameter SET_ID_MSB             = SET_ID_LSB + SCM_TAG_ADDR_WIDTH - 1,
   parameter TAG_LSB                = SET_ID_MSB + 1,
   parameter TAG_MSB                = TAG_LSB + SCM_TAG_WIDTH - 2,
   parameter MAX_OUT_TRANS_DIS_MODE = 4
)(
   input logic                                              clk,
   input logic                                              rst_n,
   input  logic                                             bypass_icache_i,
   output logic                                             cache_is_bypassed_o,
   input  logic                                             flush_icache_i,
   output logic                                             cache_is_flushed_o,

   input  logic                                             flush_set_ID_req_i,
   input  logic [FETCH_ADDR_WIDTH-1:0]                      flush_set_ID_addr_i,
   output logic                                             flush_set_ID_ack_o,
   // interface with processor
   input  logic                                             fetch_req_i,
   input  logic [FETCH_ADDR_WIDTH-1:0]                      fetch_addr_i,
   output logic                                             fetch_gnt_o,
   output logic                                             fetch_rvalid_o,
   output logic [FETCH_DATA_WIDTH-1:0]                      fetch_rdata_o,
   // interface with READ PORT --> SCM DATA
   output logic [NB_WAYS-1:0]                               DATA_req_o,
   output logic                                             DATA_we_o,
   output logic [SCM_DATA_ADDR_WIDTH-1:0]                   DATA_addr_o,
   input  logic [NB_WAYS-1:0][SCM_DATA_WIDTH-1:0]           DATA_rdata_i,
   output logic [FETCH_DATA_WIDTH-1:0]                      DATA_wdata_o,
   // interface with READ PORT --> SCM TAG
   output logic [NB_WAYS-1:0]                               TAG_req_o,
   output logic [SCM_TAG_ADDR_WIDTH-1:0]                    TAG_addr_o,
   input  logic [NB_WAYS-1:0][SCM_TAG_WIDTH-1:0]            TAG_rdata_i,
   output logic [SCM_TAG_WIDTH-1:0]                         TAG_wdata_o,
   output logic                                             TAG_we_o,
   // Interface to cache_controller_to uDMA L2 port
   output logic                                             refill_req_o,
   input  logic                                             refill_gnt_i,
   output logic                                             refill_type_o,
   output logic [FETCH_ADDR_WIDTH-1:0]                      refill_addr_o,
   input  logic                                             refill_r_valid_i,
   input  logic [FETCH_DATA_WIDTH-1:0]                      refill_r_data_i,
   input  logic                                             refill_r_last_i
);

    typedef logic [NB_WAYS-1:0] logic_nbways;

    localparam OFFSET     = $clog2(SCM_DATA_WIDTH*CACHE_LINE)-3;

    logic [FETCH_ADDR_WIDTH-1:0]                    fetch_addr_Q;
    logic                                           fetch_req_Q;
    logic [NB_WAYS-1:0]                             fetch_way_Q;

    logic                                           save_pipe_status;
    logic                                           clear_pipe;
    logic                                           enable_pipe;
    logic                                           save_fetch_way;

    // save the cuurent fetch, when there is a miss
    logic                                           save_curr_fetch;
    logic                                           clear_curr_fetch;
    logic [FETCH_ADDR_WIDTH-1:0]                    fetch_addr_saved;
    logic                                           fetch_req_saved;

    logic [SCM_TAG_ADDR_WIDTH-1:0] counter_FLUSH_NS, counter_FLUSH_CS;

    logic [NB_WAYS-1:0]                         way_match;
    logic [NB_WAYS-1:0]                         way_valid;

    logic [NB_WAYS-1:0]                         way_valid_Q;

    logic [NB_WAYS-1:0]                         random_way;
    logic [$clog2(NB_WAYS)-1:0]                 first_available_way;
    logic [NB_WAYS-1:0]                         first_available_way_OH;

    logic [$clog2(NB_WAYS)-1:0]                 HIT_WAY;
    logic [$clog2(MAX_OUT_TRANS_DIS_MODE)-1:0]  pending_trans_dis_cache;

    assign first_available_way_OH = logic_nbways'(1 << first_available_way);

    enum logic [2:0] { DISABLED_ICACHE, WAIT_REFILL_DONE, OPERATIVE, REQ_REFILL , WAIT_PENDING_TRANS, FLUSH_ICACHE, FLUSH_SET_ID, RESTART_FROM_SAVED_FETCH } CS, NS;

    logic update_lfsr;
    logic [NB_WAYS-1:0] fetch_way_int;

    // ---------------------
    // TAG CHECK MULTI WAY
    // ---------------------
    generate
        for (genvar k = 0; k < NB_WAYS; k++) begin
            assign way_match[k]  = ((TAG_rdata_i[k][SCM_TAG_WIDTH-1] == 1'b1) && (TAG_rdata_i[k][SCM_TAG_WIDTH-2:0] == fetch_addr_Q[TAG_MSB:TAG_LSB]));
            assign way_valid[k]  = (TAG_rdata_i[k][SCM_TAG_WIDTH-1] == 1'b1);
        end
    endgenerate

    always_comb begin
        // default assignments
        TAG_req_o           = '0;
        TAG_we_o            = 1'b0;
        TAG_addr_o          = fetch_addr_i[SET_ID_MSB:SET_ID_LSB];
        TAG_wdata_o         = {1'b1,fetch_addr_Q[TAG_MSB:TAG_LSB]};

        DATA_req_o          = '0;
        DATA_addr_o         = fetch_addr_i[SET_ID_MSB:SET_ID_LSB-1];
        DATA_wdata_o        = refill_r_data_i;
        DATA_we_o           = 1'b0;

        fetch_gnt_o         = 1'b0;
        fetch_rvalid_o      = 1'b0;
        fetch_rdata_o       = refill_r_data_i; // FIXME ok for AXI 64 and 32bit INSTR

        refill_req_o        = 1'b0;
        refill_type_o       = 1'b1; // 0 --> 64 bit; 1 --> 128bit
        refill_addr_o       = fetch_addr_i;
        fetch_way_int       = '0;

        save_pipe_status    = 1'b0;
        save_fetch_way      = '0;

        enable_pipe         = 1'b0;
        clear_pipe          = 1'b0;

        NS                  = CS;
        update_lfsr         = 1'b0;

        cache_is_bypassed_o = 1'b0;
        cache_is_flushed_o  = 1'b0;

        counter_FLUSH_NS    = counter_FLUSH_CS;

        flush_set_ID_ack_o  = 1'b0;

        save_curr_fetch     = 1'b0;
        clear_curr_fetch    = 1'b0;

        case (CS)
            DISABLED_ICACHE: begin
                flush_set_ID_ack_o  = 1'b1;
                refill_type_o       = 1'b0;

                counter_FLUSH_NS    = '0;
                clear_pipe          = 1'b1;
                cache_is_bypassed_o = 1'b1;
                cache_is_flushed_o  = 1'b1;
                fetch_rdata_o       = refill_r_data_i;
                fetch_rvalid_o      = refill_r_valid_i; // Must a single beat transaction

                if (bypass_icache_i == 1'b1) begin // Already Bypassed
                    NS = DISABLED_ICACHE;
                    refill_req_o  = fetch_req_i & (pending_trans_dis_cache != '1);
                    fetch_gnt_o   = refill_gnt_i & fetch_req_i & (pending_trans_dis_cache != '1);
                    refill_addr_o = fetch_addr_i;
                end else begin // Enable ICache
                    fetch_gnt_o   = 1'b0;
                    refill_req_o  = 1'b0;
                    NS            = WAIT_PENDING_TRANS;
                end
            end

            WAIT_PENDING_TRANS: begin
                flush_set_ID_ack_o  = 1'b1;
                clear_pipe            = 1'b1;
                cache_is_bypassed_o   = 1'b1;
                cache_is_flushed_o    = 1'b1;

                fetch_rdata_o         = refill_r_data_i;
                fetch_rvalid_o        = refill_r_valid_i; // Must a single beat transaction

                fetch_gnt_o           = 1'b0;
                refill_req_o          = 1'b0;

                if (pending_trans_dis_cache == 0) begin
                    NS = FLUSH_ICACHE;
                end else begin
                    NS = WAIT_PENDING_TRANS;
                end
            end

            FLUSH_ICACHE: begin
                fetch_gnt_o           = 1'b0;
                flush_set_ID_ack_o    = 1'b1;
                clear_pipe            = 1'b1;

                if (counter_FLUSH_CS < 2**SCM_TAG_ADDR_WIDTH-1) begin
                    NS = FLUSH_ICACHE;
                    counter_FLUSH_NS = counter_FLUSH_CS + 1'b1;
                end else begin
                    NS = OPERATIVE;
                    cache_is_flushed_o  = 1'b1;
                    counter_FLUSH_NS    = '0;
                end

                TAG_req_o   = '1;
                TAG_we_o    = 1'b1;
                TAG_addr_o  = counter_FLUSH_CS;
                TAG_wdata_o = '0;
                // To keep VCS happy
                DATA_req_o   = '1;
                DATA_we_o    = 1'b1;
                DATA_addr_o  = counter_FLUSH_CS;
                DATA_wdata_o = '0;
            end

            FLUSH_SET_ID: begin
                fetch_gnt_o           = 1'b0;
                flush_set_ID_ack_o    = 1'b1;

                NS = OPERATIVE;

                TAG_req_o   = '1;
                TAG_we_o    = 1'b1;
                TAG_addr_o  = flush_set_ID_addr_i[SET_ID_MSB:SET_ID_LSB];
                TAG_wdata_o = '0;
            end

            OPERATIVE: begin
                 cache_is_bypassed_o  = 1'b0;
                 cache_is_flushed_o   = 1'b0;
                 flush_set_ID_ack_o   = 1'b0;

                 fetch_gnt_o          = fetch_req_i & ~(bypass_icache_i | flush_icache_i | flush_set_ID_req_i );

                 if (bypass_icache_i | flush_icache_i | flush_set_ID_req_i) begin // first check if the previous fetch has a miss or HIT
                    if (fetch_req_Q) begin
                        if (|way_match) begin : HIT_BYP
                            if (bypass_icache_i) begin
                                NS = DISABLED_ICACHE;
                            end else if (flush_icache_i) begin
                                NS = FLUSH_ICACHE;
                            end else begin
                                NS = FLUSH_SET_ID;
                            end

                            if (fetch_req_i == 1'b0)
                                clear_pipe = 1'b1;

                           fetch_rvalid_o  = 1'b1;
                           fetch_rdata_o   = DATA_rdata_i[HIT_WAY];
                        end else begin : MISS_BYP
                           // ask for the last refill, then go into DISABLED / FLUSH / SET_ID FLUSH state
                           NS               = REQ_REFILL;
                           save_pipe_status = 1'b1;
                        end
                    end else begin
                        // No Request in the PIPE
                        if (bypass_icache_i) begin
                            NS = DISABLED_ICACHE;
                        end else if (flush_icache_i) begin
                            NS = FLUSH_ICACHE;
                        end else begin
                            NS = FLUSH_SET_ID;
                        end

                        clear_pipe = 1'b1;
                    end
                end else begin// NO Bypass, FLUSH or SET_IF FLUSH request
                    enable_pipe          = fetch_req_i;
                    // read the DATA and TAG
                    TAG_req_o   = {NB_WAYS{fetch_req_i}};
                    TAG_we_o    = 1'b0;
                    TAG_addr_o  = fetch_addr_i[SET_ID_MSB:SET_ID_LSB];

                    DATA_req_o  = {NB_WAYS{fetch_req_i}};
                    DATA_we_o   = 1'b0;
                    DATA_addr_o = fetch_addr_i[SET_ID_MSB:SET_ID_LSB-1];

                    if (fetch_req_Q) begin
                        if (|way_match) begin : HIT
                            NS = OPERATIVE;

                            if (fetch_req_i == 1'b0)
                                clear_pipe = 1'b1;

                            fetch_rvalid_o  = 1'b1;
                            fetch_rdata_o   = DATA_rdata_i[HIT_WAY];
                        end else begin : MISS
                            save_pipe_status = 1'b1;
                            save_curr_fetch  = 1'b1;
                            enable_pipe      = 1'b0;
                            NS               = REQ_REFILL;
                        end
                    end else begin
                        NS = OPERATIVE;
                    end
                end
            end

            REQ_REFILL: begin
                cache_is_bypassed_o  = 1'b0;
                cache_is_flushed_o   = 1'b0;
                flush_set_ID_ack_o   = 1'b0;

                enable_pipe      = 1'b0;
                refill_req_o     = 1'b1;
                refill_type_o    = 1'b1;

                refill_addr_o    = {fetch_addr_Q[FETCH_ADDR_WIDTH-1:4],4'b0000};

                save_fetch_way   = 1'b1;
                // this check is postponed because tag check is complex. better to do one cycle later
                if (|way_valid_Q) begin // all the lines are valid, invalidate one random line
                      fetch_way_int = random_way;
                      update_lfsr = 1'b1;
                end else begin
                      fetch_way_int = first_available_way_OH;
                      update_lfsr = 1'b0;
                end

                if (refill_gnt_i) begin
                   NS = WAIT_REFILL_DONE;
                end else begin
                    NS = REQ_REFILL;
                end
            end


            WAIT_REFILL_DONE: begin
                cache_is_bypassed_o  = 1'b0;
                cache_is_flushed_o   = 1'b0;
                flush_set_ID_ack_o   = 1'b0;

                fetch_rdata_o   = refill_r_data_i;
                fetch_rvalid_o  = refill_r_valid_i & ( fetch_addr_Q[3] == refill_r_last_i);

                DATA_req_o      = fetch_way_Q & {NB_WAYS{refill_r_valid_i}};
                DATA_addr_o     = {fetch_addr_Q[SET_ID_MSB:SET_ID_LSB],refill_r_last_i};
                DATA_wdata_o    = refill_r_data_i;
                DATA_we_o       = 1'b1;

                TAG_req_o       = fetch_way_Q & {NB_WAYS{refill_r_valid_i}};
                TAG_we_o        = 1'b1;
                TAG_addr_o      = fetch_addr_Q[SET_ID_MSB:SET_ID_LSB];
                TAG_wdata_o     = {1'b1,fetch_addr_Q[TAG_MSB:TAG_LSB]};


                if (refill_r_valid_i) begin
                    if (refill_r_last_i)
                        if(fetch_req_saved) begin
                            NS = RESTART_FROM_SAVED_FETCH;
                        end else begin
                            NS = OPERATIVE;
                        end
                    else begin
                        NS = WAIT_REFILL_DONE;
                    end

                    clear_pipe = refill_r_last_i;
                end else begin
                    NS = WAIT_REFILL_DONE;
                end
            end

            RESTART_FROM_SAVED_FETCH: begin
                //Read the DATA nd TAG
                TAG_req_o   = {NB_WAYS{fetch_req_saved}};
                TAG_we_o    = 1'b0;
                TAG_addr_o  = fetch_addr_saved[SET_ID_MSB:SET_ID_LSB];

                DATA_req_o  = {NB_WAYS{fetch_req_saved}};
                DATA_we_o   = 1'b0;
                DATA_addr_o = fetch_addr_saved[SET_ID_MSB:SET_ID_LSB-1];

                enable_pipe      = 1'b1;
                clear_curr_fetch = 1'b1;

                NS = OPERATIVE;
            end

            default: begin
             NS = DISABLED_ICACHE;
            end
        endcase // CS
    if (!rst_n)
      begin
        DATA_req_o          = -1;
        DATA_we_o           = 1'b0;
        TAG_req_o           = -1;
        TAG_we_o            = 1'b0;
      end
    end

    // -----------------
    // Replacement LFSR
    // -----------------
    lfsr #(.WIDTH (NB_WAYS)) i_lfsr (
        .clk_i          ( clk         ),
        .rst_ni         ( rst_n       ),
        .en_i           ( update_lfsr ),
        .refill_way_oh  ( random_way  ),
        .refill_way_bin (             ) // left open
    );

    always_comb begin
        first_available_way = 0;
        HIT_WAY             = 0;

        for (int unsigned index = 0; index < NB_WAYS; index++) begin
            if (way_valid_Q[index] == 0)
                first_available_way = index;

            if(way_match[index]==1)
                HIT_WAY=index;
        end
   end

    // ---------------------
    // Sequential process
    // ---------------------
    always_ff @(posedge clk, negedge rst_n) begin
        if (~rst_n) begin
            CS                       <= DISABLED_ICACHE;
            fetch_addr_Q             <= '0;
            fetch_req_Q              <= 1'b0;
            way_valid_Q              <= '0;
            fetch_way_Q              <= '0;
            pending_trans_dis_cache  <= '0;
            counter_FLUSH_CS         <= '0;
            fetch_addr_saved         <= '0;
            fetch_req_saved          <= 1'b0;
        end else begin
            CS <= NS;
            counter_FLUSH_CS <= counter_FLUSH_NS;


            if (save_fetch_way)
                fetch_way_Q <= fetch_way_int;

            //Use this code to be sure thhat there is not apending transaction when enable cache request is asserted
            if (CS == DISABLED_ICACHE || CS == WAIT_PENDING_TRANS) begin
                case ({(refill_req_o & refill_gnt_i), refill_r_valid_i})
                    2'b00: begin pending_trans_dis_cache <= pending_trans_dis_cache;       end
                    2'b10: begin pending_trans_dis_cache <= pending_trans_dis_cache+1'b1;  end
                    2'b01: begin pending_trans_dis_cache <= pending_trans_dis_cache-1'b1;  end
                    2'b11: begin pending_trans_dis_cache <= pending_trans_dis_cache;       end
                endcase
            end else begin
                pending_trans_dis_cache <= '0;
            end

            if (save_curr_fetch) begin
                fetch_addr_saved <= fetch_addr_i;
                fetch_req_saved  <= fetch_req_i;
            end else begin
                if (clear_curr_fetch)
                    fetch_req_saved <= 1'b0;
            end

            if (save_pipe_status) begin
                way_valid_Q <= way_valid;
            end


            if (enable_pipe) begin
                fetch_req_Q  <= 1'b1;
                fetch_addr_Q <= (CS == RESTART_FROM_SAVED_FETCH) ? fetch_addr_saved : fetch_addr_i;
            end else if (clear_pipe) begin
                fetch_req_Q  <= '0;
            end

        end
    end

endmodule

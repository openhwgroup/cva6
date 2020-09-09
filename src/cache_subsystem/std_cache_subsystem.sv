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
// Author: Florian Zaruba    <zarubaf@iis.ee.ethz.ch>, ETH Zurich
//         Michael Schaffner <schaffner@iis.ee.ethz.ch>, ETH Zurich
// Date: 15.08.2018
// Description: Standard Ariane cache subsystem with instruction cache and
//              write-back data cache.


module std_cache_subsystem import ariane_pkg::*; import std_cache_pkg::*; #(
  parameter logic [63:0] CACHE_START_ADDR = 64'h4000_0000
) (
    input logic                            clk_i,
    input logic                            rst_ni,
    input riscv::priv_lvl_t                priv_lvl_i,
    // I$
    input  logic                           icache_en_i,            // enable icache (or bypass e.g: in debug mode)
    input  logic                           icache_flush_i,         // flush the icache, flush and kill have to be asserted together
    output logic                           icache_miss_o,          // to performance counter
    // address translation requests
    input  icache_areq_i_t                 icache_areq_i,          // to/from frontend
    output icache_areq_o_t                 icache_areq_o,
    // data requests
    input  icache_dreq_i_t                 icache_dreq_i,          // to/from frontend
    output icache_dreq_o_t                 icache_dreq_o,
    // AMOs
    input  amo_req_t                       amo_req_i,
    output amo_resp_t                      amo_resp_o,
    // D$
    // Cache management
    input  logic                           dcache_enable_i,        // from CSR
    input  logic                           dcache_flush_i,         // high until acknowledged
    output logic                           dcache_flush_ack_o,     // send a single cycle acknowledge signal when the cache is flushed
    output logic                           dcache_miss_o,          // we missed on a ld/st
    output logic                           wbuffer_empty_o,        // statically set to 1, as there is no wbuffer in this cache system
    // Request ports
    input  dcache_req_i_t   [2:0]          dcache_req_ports_i,     // to/from LSU
    output dcache_req_o_t   [2:0]          dcache_req_ports_o,     // to/from LSU
    // memory side
    output ariane_axi::req_t               axi_req_o,
    input  ariane_axi::resp_t              axi_resp_i
);

  assign wbuffer_empty_o = 1'b1;

    ariane_axi::req_t  axi_req_icache;
    ariane_axi::resp_t axi_resp_icache;
    ariane_axi::req_t  axi_req_bypass;
    ariane_axi::resp_t axi_resp_bypass;
    ariane_axi::req_t  axi_req_data;
    ariane_axi::resp_t axi_resp_data;

    std_icache i_icache (
        .clk_i      ( clk_i                 ),
        .rst_ni     ( rst_ni                ),
        .priv_lvl_i ( priv_lvl_i            ),
        .flush_i    ( icache_flush_i        ),
        .en_i       ( icache_en_i           ),
        .miss_o     ( icache_miss_o         ),
        .areq_i     ( icache_areq_i         ),
        .areq_o     ( icache_areq_o         ),
        .dreq_i     ( icache_dreq_i         ),
        .dreq_o     ( icache_dreq_o         ),
        .axi_req_o  ( axi_req_icache        ),
        .axi_resp_i ( axi_resp_icache       )
    );

   // decreasing priority
   // Port 0: PTW
   // Port 1: Load Unit
   // Port 2: Store Unit
   std_nbdcache #(
      .CACHE_START_ADDR ( CACHE_START_ADDR )
   ) i_nbdcache (
      .clk_i,
      .rst_ni,
      .enable_i     ( dcache_enable_i        ),
      .flush_i      ( dcache_flush_i         ),
      .flush_ack_o  ( dcache_flush_ack_o     ),
      .miss_o       ( dcache_miss_o          ),
      .axi_bypass_o ( axi_req_bypass         ),
      .axi_bypass_i ( axi_resp_bypass        ),
      .axi_data_o   ( axi_req_data           ),
      .axi_data_i   ( axi_resp_data          ),
      .req_ports_i  ( dcache_req_ports_i     ),
      .req_ports_o  ( dcache_req_ports_o     ),
      .amo_req_i,
      .amo_resp_o
   );

    // -----------------------
    // Arbitrate AXI Ports
    // -----------------------
    logic [1:0] w_select, w_select_fifo, w_select_arbiter;
    logic w_fifo_empty;


    // AR Channel
    stream_arbiter #(
        .DATA_T ( ariane_axi::ar_chan_t ),
        .N_INP  ( 3                     )
    ) i_stream_arbiter_ar (
        .clk_i,
        .rst_ni,
        .inp_data_i  ( {axi_req_icache.ar, axi_req_bypass.ar, axi_req_data.ar} ),
        .inp_valid_i ( {axi_req_icache.ar_valid, axi_req_bypass.ar_valid, axi_req_data.ar_valid} ),
        .inp_ready_o ( {axi_resp_icache.ar_ready, axi_resp_bypass.ar_ready, axi_resp_data.ar_ready} ),
        .oup_data_o  ( axi_req_o.ar        ),
        .oup_valid_o ( axi_req_o.ar_valid  ),
        .oup_ready_i ( axi_resp_i.ar_ready )
    );

    // AW Channel
    stream_arbiter #(
        .DATA_T ( ariane_axi::aw_chan_t ),
        .N_INP  ( 3                     )
    ) i_stream_arbiter_aw (
        .clk_i,
        .rst_ni,
        .inp_data_i  ( {axi_req_icache.aw, axi_req_bypass.aw, axi_req_data.aw} ),
        .inp_valid_i ( {axi_req_icache.aw_valid, axi_req_bypass.aw_valid, axi_req_data.aw_valid} ),
        .inp_ready_o ( {axi_resp_icache.aw_ready, axi_resp_bypass.aw_ready, axi_resp_data.aw_ready} ),
        .oup_data_o  ( axi_req_o.aw        ),
        .oup_valid_o ( axi_req_o.aw_valid  ),
        .oup_ready_i ( axi_resp_i.aw_ready )
    );

    // WID has been removed in AXI 4 so we need to keep track which AW request has been accepted
    // to forward the correct write data.
    always_comb begin
        w_select = 0;
        unique case (axi_req_o.aw.id)
            4'b1100:                            w_select = 2; // dcache
            4'b1000, 4'b1001, 4'b1010, 4'b1011: w_select = 1; // bypass
            default:                            w_select = 0; // icache
        endcase
    end

    // TODO(zarubaf): This causes a cycle delay, might be optimize-able, FALL_THROUGH
    // option made problems during synthesis (timing loop)
    fifo_v3 #(
      .DATA_WIDTH   ( 2    ),
      // we can have a maximum of 4 oustanding transactions as each port is blocking
      .DEPTH        ( 4    )
    ) i_fifo_w_channel (
      .clk_i      ( clk_i           ),
      .rst_ni     ( rst_ni          ),
      .flush_i    ( 1'b0            ),
      .testmode_i ( 1'b0            ),
      .full_o     (                 ), // leave open
      .empty_o    ( w_fifo_empty    ),
      .usage_o    (                 ), // leave open
      .data_i     ( w_select        ),
      // a new transaction was requested and granted
      .push_i     ( axi_req_o.aw_valid & axi_resp_i.aw_ready ),
      // write ID to select the output MUX
      .data_o     ( w_select_fifo   ),
      // transaction has finished
      .pop_i      ( axi_req_o.w_valid & axi_resp_i.w_ready & axi_req_o.w.last )
    );

    // icache will never write so select it as default (e.g.: when no arbitration is active)
    // this is equal to setting it to zero
    assign w_select_arbiter = (w_fifo_empty) ? 0 : w_select_fifo;

    stream_mux #(
        .DATA_T ( ariane_axi::w_chan_t ),
        .N_INP  ( 3                    )
    ) i_stream_mux_w (
        .inp_data_i  ( {axi_req_data.w, axi_req_bypass.w, axi_req_icache.w} ),
        .inp_valid_i ( {axi_req_data.w_valid, axi_req_bypass.w_valid, axi_req_icache.w_valid} ),
        .inp_ready_o ( {axi_resp_data.w_ready, axi_resp_bypass.w_ready, axi_resp_icache.w_ready} ),
        .inp_sel_i   ( w_select_arbiter   ),
        .oup_data_o  ( axi_req_o.w        ),
        .oup_valid_o ( axi_req_o.w_valid  ),
        .oup_ready_i ( axi_resp_i.w_ready )
    );

    // Route responses based on ID
    // 0000            -> I$
    // 10[00|10|01|11] -> Bypass
    // 1100            -> D$
    // R Channel
    assign axi_resp_icache.r = axi_resp_i.r;
    assign axi_resp_bypass.r = axi_resp_i.r;
    assign axi_resp_data.r   = axi_resp_i.r;

    logic [1:0] r_select;

    always_comb begin
        r_select = 0;
        unique case (axi_resp_i.r.id)
            4'b1100:                            r_select = 0; // dcache
            4'b1000, 4'b1001, 4'b1010, 4'b1011: r_select = 1; // bypass
            4'b0000:                            r_select = 2; // icache
            default:                            r_select = 0;
        endcase
    end

    stream_demux #(
        .N_OUP ( 3 )
    ) i_stream_demux_r (
        .inp_valid_i ( axi_resp_i.r_valid ),
        .inp_ready_o ( axi_req_o.r_ready  ),
        .oup_sel_i   ( r_select           ),
        .oup_valid_o ( {axi_resp_icache.r_valid, axi_resp_bypass.r_valid, axi_resp_data.r_valid} ),
        .oup_ready_i ( {axi_req_icache.r_ready, axi_req_bypass.r_ready, axi_req_data.r_ready} )
    );

    // B Channel
    logic [1:0] b_select;

    assign axi_resp_icache.b = axi_resp_i.b;
    assign axi_resp_bypass.b = axi_resp_i.b;
    assign axi_resp_data.b   = axi_resp_i.b;

    always_comb begin
        b_select = 0;
        unique case (axi_resp_i.b.id)
            4'b1100:                            b_select = 0; // dcache
            4'b1000, 4'b1001, 4'b1010, 4'b1011: b_select = 1; // bypass
            4'b0000:                            b_select = 2; // icache
            default:                            b_select = 0;
        endcase
    end

    stream_demux #(
        .N_OUP ( 3 )
    ) i_stream_demux_b (
        .inp_valid_i ( axi_resp_i.b_valid ),
        .inp_ready_o ( axi_req_o.b_ready  ),
        .oup_sel_i   ( b_select           ),
        .oup_valid_o ( {axi_resp_icache.b_valid, axi_resp_bypass.b_valid, axi_resp_data.b_valid} ),
        .oup_ready_i ( {axi_req_icache.b_ready, axi_req_bypass.b_ready, axi_req_data.b_ready} )
    );

///////////////////////////////////////////////////////
// assertions
///////////////////////////////////////////////////////

//pragma translate_off
`ifndef VERILATOR

  a_invalid_instruction_fetch: assert property (
    @(posedge clk_i) disable iff (~rst_ni) icache_dreq_o.valid |-> (|icache_dreq_o.data) !== 1'hX)
      else $warning(1,"[l1 dcache] reading invalid instructions: vaddr=%08X, data=%08X",
        icache_dreq_o.vaddr, icache_dreq_o.data);

  a_invalid_write_data: assert property (
    @(posedge clk_i) disable iff (~rst_ni) dcache_req_ports_i[2].data_req |-> |dcache_req_ports_i[2].data_be |-> (|dcache_req_ports_i[2].data_wdata) !== 1'hX)
      else $warning(1,"[l1 dcache] writing invalid data: paddr=%016X, be=%02X, data=%016X",
        {dcache_req_ports_i[2].address_tag, dcache_req_ports_i[2].address_index}, dcache_req_ports_i[2].data_be, dcache_req_ports_i[2].data_wdata);
  generate
      for(genvar j=0; j<2; j++) begin
        a_invalid_read_data: assert property (
          @(posedge clk_i) disable iff (~rst_ni) dcache_req_ports_o[j].data_rvalid |-> (|dcache_req_ports_o[j].data_rdata) !== 1'hX)
            else $warning(1,"[l1 dcache] reading invalid data on port %01d: data=%016X",
              j, dcache_req_ports_o[j].data_rdata);
     end
  endgenerate

`endif
//pragma translate_on
endmodule // std_cache_subsystem

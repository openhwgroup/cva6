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
// Date: 19.03.2017
// Description: Ariane Top-level module

import ariane_pkg::*;

module ariane_wrapped #(
        parameter logic [63:0] CACHE_START_ADDR  = 64'h8000_0000, // address on which to decide whether the request is cache-able or not
        parameter int unsigned AXI_ID_WIDTH      = 10,
        parameter int unsigned AXI_USER_WIDTH    = 1,
        parameter int unsigned AXI_ADDRESS_WIDTH = 64,
        parameter int unsigned AXI_DATA_WIDTH    = 64
    )(
        input  logic                           clk_i,
        input  logic                           rst_ni,
        input  logic                           test_en_i,     // enable all clock gates for testing
        // Core ID, Cluster ID and boot address are considered more or less static
        input  logic [ 3:0]                    core_id_i,
        input  logic [ 5:0]                    cluster_id_i,
        input  logic                           flush_req_i,
        output logic                           flushing_o,
        // Interrupt inputs
        input  logic [1:0]                     irq_i,        // level sensitive IR lines, mip & sip
        input  logic                           ipi_i,        // inter-processor interrupts
        output logic                           sec_lvl_o,    // current privilege level oot
        // Timer facilities
        input  logic [63:0]                    time_i,        // global time (most probably coming from an RTC)
        input  logic                           time_irq_i,    // timer interrupt in
        
        input logic [15:0] i_dip,
        output logic [15:0] o_led
    );

    logic [63:0]                    boot_addr_i = 64'h40000000;
 
    localparam int unsigned AXI_NUMBYTES = AXI_DATA_WIDTH/8;

    logic        flush_dcache_ack, flush_dcache;
    logic        flush_dcache_d, flush_dcache_q;

    AXI_BUS #(
        .AXI_ADDR_WIDTH ( 64             ),
        .AXI_DATA_WIDTH ( 64             ),
        .AXI_ID_WIDTH   ( AXI_ID_WIDTH   ),
        .AXI_USER_WIDTH ( AXI_USER_WIDTH )
    ) data_if();

    AXI_BUS #(
        .AXI_ADDR_WIDTH ( 64             ),
        .AXI_DATA_WIDTH ( 64             ),
        .AXI_ID_WIDTH   ( AXI_ID_WIDTH   ),
        .AXI_USER_WIDTH ( AXI_USER_WIDTH )
    ) bypass_if();

    AXI_BUS #(
        .AXI_ADDR_WIDTH ( 64             ),
        .AXI_DATA_WIDTH ( 64             ),
        .AXI_ID_WIDTH   ( AXI_ID_WIDTH   ),
        .AXI_USER_WIDTH ( AXI_USER_WIDTH )
    ) instr_if();

    ariane #(
        .CACHE_START_ADDR ( CACHE_START_ADDR ),
        .AXI_ID_WIDTH     ( 10               ),
        .AXI_USER_WIDTH   ( 1                )
    ) i_ariane (
        .*,
        .flush_dcache_i         ( flush_dcache         ),
        .flush_dcache_ack_o     ( flush_dcache_ack     ),
        .data_if                ( data_if              ),
        .bypass_if              ( bypass_if            ),
        .instr_if               ( instr_if             )
    );

    assign flush_dcache = flush_dcache_q;
    assign flushing_o = flush_dcache_q;

    // direct store interface
    always_ff @(posedge clk_i or negedge rst_ni) begin

        automatic logic [63:0] store_address;

        if (~rst_ni) begin
            flush_dcache_q  <= 1'b0;
        end else begin
            // got acknowledge from dcache - release the flush signal
            if (flush_dcache_ack)
                flush_dcache_q <= 1'b0;

            if (flush_req_i) begin
                flush_dcache_q <= 1'b1;
            end
        end
    end

    logic        master0_req,     master1_req;
    logic [63:0] master0_address, master1_address;
    logic        master0_we,      master1_we;
    logic [7:0]  master0_be,      master1_be;
    logic [63:0] master0_wdata,   master1_wdata;
    logic [63:0] master0_rdata,   master1_rdata;

   // sharedmem shared port
   logic [7:0]  sharedmem_en;
   logic [63:0] sharedmem_dout;
   logic        shared_sel;
   
        // Debug Interface
         logic                           debug_gnt_o;
         logic                           debug_rvalid_o;
         logic [31:0] debug_addr;
         logic [15:0]                    debug_addr_i = debug_addr[15:0];
         logic                           debug_we_i;
         logic [63:0]                    debug_wdata_i;
         logic [63:0]                    debug_rdata_o;
         logic                           debug_halted_o;
         logic                           debug_halt_i;
         logic                           debug_resume_i;
         logic        debug_req, debug_fetch_disable;
         logic        debug_reset;
         logic        debug_runtest;
         logic        debug_clk, debug_blocksel_i;
         logic [1:0]  debug_unused;
         
         logic [63:0] debug_dout;
        // CPU Control Signals
         logic                           fetch_enable_i = ~(debug_blocksel_i && debug_fetch_disable);
         logic                           debug_req_i = debug_blocksel_i && debug_req;

/*
logic [AXI_ADDR_WIDTH-1:0] aw_addr;
logic [2:0]                aw_prot;
logic [3:0]                aw_region;
logic [7:0]                aw_len;
logic [2:0]                aw_size;
logic [1:0]                aw_burst;
logic                      aw_lock;
logic [3:0]                aw_cache;
logic [3:0]                aw_qos;
logic [AXI_ID_WIDTH-1:0]   aw_id;
logic [AXI_USER_WIDTH-1:0] aw_user;
logic                      aw_ready;
logic                      aw_valid;

logic [AXI_ADDR_WIDTH-1:0] ar_addr;
logic [2:0]                ar_prot;
logic [3:0]                ar_region;
logic [7:0]                ar_len;
logic [2:0]                ar_size;
logic [1:0]                ar_burst;
logic                      ar_lock;
logic [3:0]                ar_cache;
logic [3:0]                ar_qos;
logic [AXI_ID_WIDTH-1:0]   ar_id;
logic [AXI_USER_WIDTH-1:0] ar_user;
logic                      ar_ready;
logic                      ar_valid;

logic                      w_valid;
logic [AXI_DATA_WIDTH-1:0] w_data;
logic [AXI_STRB_WIDTH-1:0] w_strb;
logic [AXI_USER_WIDTH-1:0] w_user;
logic                      w_last;
logic                      w_ready;

logic [AXI_DATA_WIDTH-1:0] r_data;
logic [1:0]                r_resp;
logic                      r_last;
logic [AXI_ID_WIDTH-1:0]   r_id;
logic [AXI_USER_WIDTH-1:0] r_user;
logic                      r_ready;
logic                      r_valid;

logic [1:0]                b_resp;
logic [AXI_ID_WIDTH-1:0]   b_id;
logic [AXI_USER_WIDTH-1:0] b_user;
logic                      b_ready;
logic                      b_valid;
*/

    AXI_BUS #(
        .AXI_ADDR_WIDTH ( 64             ),
        .AXI_DATA_WIDTH ( 64             ),
        .AXI_ID_WIDTH   ( AXI_ID_WIDTH   ),
        .AXI_USER_WIDTH ( AXI_USER_WIDTH )
    ) master0_if();

    AXI_BUS #(
        .AXI_ADDR_WIDTH ( 64             ),
        .AXI_DATA_WIDTH ( 64             ),
        .AXI_ID_WIDTH   ( AXI_ID_WIDTH   ),
        .AXI_USER_WIDTH ( AXI_USER_WIDTH )
    ) master1_if();

axi_crossbar_0 crossbar (
  .aclk(clk_i),                      // input wire aclk
  .aresetn(rst_ni),                // input wire aresetn
  .s_axi_awid({bypass_if.aw_id,data_if.aw_id,instr_if.aw_id}),          // input wire [29 : 0] s_axi_awid
  .s_axi_awaddr({bypass_if.aw_addr,data_if.aw_addr,instr_if.aw_addr}),      // input wire [191 : 0] s_axi_awaddr
  .s_axi_awlen({bypass_if.aw_len,data_if.aw_len,instr_if.aw_len}),        // input wire [23 : 0] s_axi_awlen
  .s_axi_awsize({bypass_if.aw_size,data_if.aw_size,instr_if.aw_size}),      // input wire [8 : 0] s_axi_awsize
  .s_axi_awburst({bypass_if.aw_burst,data_if.aw_burst,instr_if.aw_burst}),    // input wire [5 : 0] s_axi_awburst
  .s_axi_awlock({bypass_if.aw_lock,data_if.aw_lock,instr_if.aw_lock}),      // input wire [2 : 0] s_axi_awlock
  .s_axi_awcache({bypass_if.aw_cache,data_if.aw_cache,instr_if.aw_cache}),    // input wire [11 : 0] s_axi_awcache
  .s_axi_awprot({bypass_if.aw_prot,data_if.aw_prot,instr_if.aw_prot}),      // input wire [8 : 0] s_axi_awprot
  .s_axi_awqos({bypass_if.aw_qos,data_if.aw_qos,instr_if.aw_qos}),        // input wire [11 : 0] s_axi_awqos
  .s_axi_awuser({bypass_if.aw_user,data_if.aw_user,instr_if.aw_user}),      // input wire [2 : 0] s_axi_awuser
  .s_axi_awvalid({bypass_if.aw_valid,data_if.aw_valid,instr_if.aw_valid}),    // input wire [2 : 0] s_axi_awvalid
  .s_axi_awready({bypass_if.aw_ready,data_if.aw_ready,instr_if.aw_ready}),    // output wire [2 : 0] s_axi_awready
  .s_axi_wdata({bypass_if.w_data,data_if.w_data,instr_if.w_data}),        // input wire [191 : 0] s_axi_wdata
  .s_axi_wstrb({bypass_if.w_strb,data_if.w_strb,instr_if.w_strb}),        // input wire [23 : 0] s_axi_wstrb
  .s_axi_wlast({bypass_if.w_last,data_if.w_last,instr_if.w_last}),        // input wire [2 : 0] s_axi_wlast
  .s_axi_wuser({bypass_if.w_user,data_if.w_user,instr_if.w_user}),        // input wire [2 : 0] s_axi_wuser
  .s_axi_wvalid({bypass_if.w_valid,data_if.w_valid,instr_if.w_valid}),      // input wire [2 : 0] s_axi_wvalid
  .s_axi_wready({bypass_if.w_ready,data_if.w_ready,instr_if.w_ready}),      // output wire [2 : 0] s_axi_wready
  .s_axi_bid({bypass_if.b_id,data_if.b_id,instr_if.b_id}),            // output wire [29 : 0] s_axi_bid
  .s_axi_bresp({bypass_if.b_resp,data_if.b_resp,instr_if.b_resp}),        // output wire [5 : 0] s_axi_bresp
  .s_axi_buser({bypass_if.b_user,data_if.b_user,instr_if.b_user}),        // output wire [2 : 0] s_axi_buser
  .s_axi_bvalid({bypass_if.b_valid,data_if.b_valid,instr_if.b_valid}),      // output wire [2 : 0] s_axi_bvalid
  .s_axi_bready({bypass_if.b_ready,data_if.b_ready,instr_if.b_ready}),      // input wire [2 : 0] s_axi_bready
  .s_axi_arid({bypass_if.ar_id,data_if.ar_id,instr_if.ar_id}),          // input wire [29 : 0] s_axi_arid
  .s_axi_araddr({bypass_if.ar_addr,data_if.ar_addr,instr_if.ar_addr}),      // input wire [191 : 0] s_axi_araddr
  .s_axi_arlen({bypass_if.ar_len,data_if.ar_len,instr_if.ar_len}),        // input wire [23 : 0] s_axi_arlen
  .s_axi_arsize({bypass_if.ar_size,data_if.ar_size,instr_if.ar_size}),      // input wire [8 : 0] s_axi_arsize
  .s_axi_arburst({bypass_if.ar_burst,data_if.ar_burst,instr_if.ar_burst}),    // input wire [5 : 0] s_axi_arburst
  .s_axi_arlock({bypass_if.ar_lock,data_if.ar_lock,instr_if.ar_lock}),      // input wire [2 : 0] s_axi_arlock
  .s_axi_arcache({bypass_if.ar_cache,data_if.ar_cache,instr_if.ar_cache}),    // input wire [11 : 0] s_axi_arcache
  .s_axi_arprot({bypass_if.ar_prot,data_if.ar_prot,instr_if.ar_prot}),      // input wire [8 : 0] s_axi_arprot
  .s_axi_arqos({bypass_if.ar_qos,data_if.ar_qos,instr_if.ar_qos}),        // input wire [11 : 0] s_axi_arqos
  .s_axi_aruser({bypass_if.ar_user,data_if.ar_user,instr_if.ar_user}),      // input wire [2 : 0] s_axi_aruser
  .s_axi_arvalid({bypass_if.ar_valid,data_if.ar_valid,instr_if.ar_valid}),    // input wire [2 : 0] s_axi_arvalid
  .s_axi_arready({bypass_if.ar_ready,data_if.ar_ready,instr_if.ar_ready}),    // output wire [2 : 0] s_axi_arready
  .s_axi_rid({bypass_if.r_id,data_if.r_id,instr_if.r_id}),            // output wire [29 : 0] s_axi_rid
  .s_axi_rdata({bypass_if.r_data,data_if.r_data,instr_if.r_data}),        // output wire [191 : 0] s_axi_rdata
  .s_axi_rresp({bypass_if.r_resp,data_if.r_resp,instr_if.r_resp}),        // output wire [5 : 0] s_axi_rresp
  .s_axi_rlast({bypass_if.r_last,data_if.r_last,instr_if.r_last}),        // output wire [2 : 0] s_axi_rlast
  .s_axi_ruser({bypass_if.r_user,data_if.r_user,instr_if.r_user}),        // output wire [2 : 0] s_axi_ruser
  .s_axi_rvalid({bypass_if.r_valid,data_if.r_valid,instr_if.r_valid}),      // output wire [2 : 0] s_axi_rvalid
  .s_axi_rready({bypass_if.r_ready,data_if.r_ready,instr_if.r_ready}),      // input wire [2 : 0] s_axi_rready
  .m_axi_awid({master1_if.aw_id,master0_if.aw_id}),          // input wire [29 : 0] s_axi_awid
  .m_axi_awaddr({master1_if.aw_addr,master0_if.aw_addr}),      // input wire [191 : 0] s_axi_awaddr
  .m_axi_awlen({master1_if.aw_len,master0_if.aw_len}),        // input wire [23 : 0] s_axi_awlen
  .m_axi_awsize({master1_if.aw_size,master0_if.aw_size}),      // input wire [8 : 0] s_axi_awsize
  .m_axi_awburst({master1_if.aw_burst,master0_if.aw_burst}),    // input wire [5 : 0] s_axi_awburst
  .m_axi_awlock({master1_if.aw_lock,master0_if.aw_lock}),      // input wire [2 : 0] s_axi_awlock
  .m_axi_awcache({master1_if.aw_cache,master0_if.aw_cache}),    // input wire [11 : 0] s_axi_awcache
  .m_axi_awprot({master1_if.aw_prot,master0_if.aw_prot}),      // input wire [8 : 0] s_axi_awprot
  .m_axi_awqos({master1_if.aw_qos,master0_if.aw_qos}),        // input wire [11 : 0] s_axi_awqos
  .m_axi_awuser({master1_if.aw_user,master0_if.aw_user}),      // input wire [2 : 0] s_axi_awuser
  .m_axi_awvalid({master1_if.aw_valid,master0_if.aw_valid}),    // input wire [2 : 0] s_axi_awvalid
  .m_axi_awready({master1_if.aw_ready,master0_if.aw_ready}),    // output wire [2 : 0] s_axi_awready
  .m_axi_wdata({master1_if.w_data,master0_if.w_data}),        // input wire [191 : 0] s_axi_wdata
  .m_axi_wstrb({master1_if.w_strb,master0_if.w_strb}),        // input wire [23 : 0] s_axi_wstrb
  .m_axi_wlast({master1_if.w_last,master0_if.w_last}),        // input wire [2 : 0] s_axi_wlast
  .m_axi_wuser({master1_if.w_user,master0_if.w_user}),        // input wire [2 : 0] s_axi_wuser
  .m_axi_wvalid({master1_if.w_valid,master0_if.w_valid}),      // input wire [2 : 0] s_axi_wvalid
  .m_axi_wready({master1_if.w_ready,master0_if.w_ready}),      // output wire [2 : 0] s_axi_wready
  .m_axi_bid({master1_if.b_id,master0_if.b_id}),            // output wire [29 : 0] s_axi_bid
  .m_axi_bresp({master1_if.b_resp,master0_if.b_resp}),        // output wire [5 : 0] s_axi_bresp
  .m_axi_buser({master1_if.b_user,master0_if.b_user}),        // output wire [2 : 0] s_axi_buser
  .m_axi_bvalid({master1_if.b_valid,master0_if.b_valid}),      // output wire [2 : 0] s_axi_bvalid
  .m_axi_bready({master1_if.b_ready,master0_if.b_ready}),      // input wire [2 : 0] s_axi_bready
  .m_axi_arid({master1_if.ar_id,master0_if.ar_id}),          // input wire [29 : 0] s_axi_arid
  .m_axi_araddr({master1_if.ar_addr,master0_if.ar_addr}),      // input wire [191 : 0] s_axi_araddr
  .m_axi_arlen({master1_if.ar_len,master0_if.ar_len}),        // input wire [23 : 0] s_axi_arlen
  .m_axi_arsize({master1_if.ar_size,master0_if.ar_size}),      // input wire [8 : 0] s_axi_arsize
  .m_axi_arburst({master1_if.ar_burst,master0_if.ar_burst}),    // input wire [5 : 0] s_axi_arburst
  .m_axi_arlock({master1_if.ar_lock,master0_if.ar_lock}),      // input wire [2 : 0] s_axi_arlock
  .m_axi_arcache({master1_if.ar_cache,master0_if.ar_cache}),    // input wire [11 : 0] s_axi_arcache
  .m_axi_arprot({master1_if.ar_prot,master0_if.ar_prot}),      // input wire [8 : 0] s_axi_arprot
  .m_axi_arqos({master1_if.ar_qos,master0_if.ar_qos}),        // input wire [11 : 0] s_axi_arqos
  .m_axi_aruser({master1_if.ar_user,master0_if.ar_user}),      // input wire [2 : 0] s_axi_aruser
  .m_axi_arvalid({master1_if.ar_valid,master0_if.ar_valid}),    // input wire [2 : 0] s_axi_arvalid
  .m_axi_arready({master1_if.ar_ready,master0_if.ar_ready}),    // output wire [2 : 0] s_axi_arready
  .m_axi_rid({master1_if.r_id,master0_if.r_id}),            // output wire [29 : 0] s_axi_rid
  .m_axi_rdata({master1_if.r_data,master0_if.r_data}),        // output wire [191 : 0] s_axi_rdata
  .m_axi_rresp({master1_if.r_resp,master0_if.r_resp}),        // output wire [5 : 0] s_axi_rresp
  .m_axi_rlast({master1_if.r_last,master0_if.r_last}),        // output wire [2 : 0] s_axi_rlast
  .m_axi_ruser({master1_if.r_user,master0_if.r_user}),        // output wire [2 : 0] s_axi_ruser
  .m_axi_rvalid({master1_if.r_valid,master0_if.r_valid}),      // output wire [2 : 0] s_axi_rvalid
  .m_axi_rready({master1_if.r_ready,master0_if.r_ready})      // input wire [2 : 0] s_axi_rready
);

    axi2mem #(
        .AXI_ID_WIDTH   ( AXI_ID_WIDTH      ),
        .AXI_ADDR_WIDTH ( AXI_ADDRESS_WIDTH ),
        .AXI_DATA_WIDTH ( AXI_DATA_WIDTH    ),
        .AXI_USER_WIDTH ( AXI_USER_WIDTH    )
    ) i_master0 (
        .clk_i  ( clk_i          ),
        .rst_ni ( rst_ni         ),
        .slave  ( master0_if      ),
        .req_o  ( master0_req     ),
        .we_o   ( master0_we      ),
        .addr_o ( master0_address ),
        .be_o   ( master0_be      ),
        .data_o ( master0_wdata   ),
        .data_i ( master0_rdata   )
    );
    
    axi2mem #(
        .AXI_ID_WIDTH   ( AXI_ID_WIDTH      ),
        .AXI_ADDR_WIDTH ( AXI_ADDRESS_WIDTH ),
        .AXI_DATA_WIDTH ( AXI_DATA_WIDTH    ),
        .AXI_USER_WIDTH ( AXI_USER_WIDTH    )
    ) i_master1 (
        .clk_i  ( clk_i        ),
        .rst_ni ( rst_ni       ),
        .slave  ( master1_if      ),
        .req_o  ( master1_req     ),
        .we_o   ( master1_we      ),
        .addr_o ( master1_address ),
        .be_o   ( master1_be      ),
        .data_o ( master1_wdata   ),
        .data_i ( master1_rdata   )
    );

infer_bram  #(
        .BRAM_SIZE(14),
        .BYTE_WIDTH(8))
        my_master1_ram (
      .ram_clk(clk_i),    // input wire clka
      .ram_en(master1_req),      // input wire ena
      .ram_we(master1_we ? master1_be : 8'b0),   // input wire [31 : 0] wea
      .ram_addr(master1_address[16:3]),  // input wire [8: 0] addra
      .ram_wrdata(master1_wdata),  // input wire [255 : 0] dina
      .ram_rddata(master1_rdata)  // output wire [255 : 0] douta
      );

always @*
        begin      
        sharedmem_en = 8'h0; debug_blocksel_i = 1'b0;
        casez(debug_addr[23:20])
            4'h8: begin sharedmem_en = 8'hff; debug_dout = sharedmem_dout; end
            4'hf: begin debug_blocksel_i = &debug_addr[31:24]; debug_dout = debug_rdata_o; end
            default: debug_dout = 64'hDEADBEEF;
            endcase
        end

jtag_dummy jtag1(
    .DBG({debug_unused[1:0],debug_fetch_disable,debug_req}),
    .WREN(debug_we_i),
    .FROM_MEM(debug_dout),
    .ADDR(debug_addr),
    .TO_MEM(debug_wdata_i),
    .TCK(debug_clk),
    .TCK2(),
    .RESET(debug_reset),
    .RUNTEST(debug_runtest));

   genvar r;

   logic        ce_d;
   logic        we_d;

   wire [7:0] m_enb = (we_d ? master0_be : 8'hFF);
   wire m_web = ce_d & shared_sel & we_d;
   logic i_emdio, o_emdio, oe_emdio, o_emdclk, sync, cooked, tx_enable_old, loopback, loopback2;
   logic [10:0] rx_addr;
   logic [7:0] rx_data;
   logic rx_ena, rx_wea;

   generate for (r = 0; r < 8; r=r+1)
     RAMB16_S9_S9
     RAMB16_S9_S9_inst
       (
        .CLKA   ( debug_clk                ),     // Port A Clock
        .DOA    ( sharedmem_dout[r*8 +: 8] ),     // Port A 1-bit Data Output
        .DOPA   (                          ),
        .ADDRA  ( debug_addr[13:3]         ),     // Port A 14-bit Address Input
        .DIA    ( debug_wdata_i[r*8 +:8]   ),     // Port A 1-bit Data Input
        .DIPA   ( 1'b0                     ),
        .ENA    ( sharedmem_en[r]          ),     // Port A RAM Enable Input
        .SSRA   ( 1'b0                     ),     // Port A Synchronous Set/Reset Input
        .WEA    ( debug_we_i               ),     // Port A Write Enable Input
        .CLKB   ( clk_i                    ),     // Port B Clock
        .DOB    ( master0_rdata[r*8 +: 8]   ),     // Port B 1-bit Data Output
        .DOPB   (                          ),
        .ADDRB  ( master0_address[13:3]     ),     // Port B 14-bit Address Input
        .DIB    ( master0_wdata[r*8 +: 8]   ),     // Port B 1-bit Data Input
        .DIPB   ( 1'b0                     ),
        .ENB    ( m_enb[r]                 ),     // Port B RAM Enable Input
        .SSRB   ( 1'b0                     ),     // Port B Synchronous Set/Reset Input
        .WEB    ( m_web                    )      // Port B Write Enable Input
        );
   endgenerate

endmodule


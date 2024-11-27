// (C) 2001-2024 Intel Corporation. All rights reserved.
// Your use of Intel Corporation's design tools, logic functions and other 
// software and tools, and its AMPP partner logic functions, and any output 
// files from any of the foregoing (including device programming or simulation 
// files), and any associated documentation or information are expressly subject 
// to the terms and conditions of the Intel Program License Subscription 
// Agreement, Intel FPGA IP License Agreement, or other applicable 
// license agreement, including, without limitation, that your use is for the 
// sole purpose of programming logic devices manufactured by Intel and sold by 
// Intel or its authorized distributors.  Please refer to the applicable 
// agreement for further details.


// AXI Bridge
//
// Convert "incomplete" AXI3/4 slave-side interface to
// a "complete" AXI4 master-side interface
//
// Adapts between an AXI master and slave that 
// are almost symmetric, with the following
// exceptions:
//
// the master's address width >= the slave's address width
// the master's id width <= the slave's id width
// -----------------------------------------
`timescale 1 ns / 1 ns

module cva6_intel_axi_bridge_0_altera_axi_bridge_1940_72stfyq 
#( 
    // ----------------
    // Interface parameters
    // ----------------
    parameter S0_ID_WIDTH           = 4,
              M0_ID_WIDTH           = 8,
              ADDR_WIDTH            = 32,
              DATA_WIDTH            = 32,
              WRITE_ADDR_USER_WIDTH = 64,
              READ_ADDR_USER_WIDTH  = 64,
              WRITE_DATA_USER_WIDTH = 64,
              WRITE_RESP_USER_WIDTH = 64,
              READ_DATA_USER_WIDTH  = 64,
              AXI_VERSION           = "AXI4",
              USE_PIPELINE          = 0,
              LOCK_WIDTH            = 1,
              BURST_LENGTH_WIDTH    = 8,
              SYNC_RESET            = 0,
   // ---------------
   // Master parameters
   // ---------------
              USE_M0_AWID          = 1,
              USE_M0_AWREGION      = 1,
              USE_M0_AWLEN         = 1,
              USE_M0_AWSIZE        = 1,
              USE_M0_AWBURST       = 1,
              USE_M0_AWLOCK        = 1,
              USE_M0_AWCACHE       = 1,
              USE_M0_AWQOS         = 1,

              USE_M0_ARID          = 1,
              USE_M0_ARREGION      = 1,
              USE_M0_ARLEN         = 1,
              USE_M0_ARSIZE        = 1,
              USE_M0_ARBURST       = 1,
              USE_M0_ARLOCK        = 1,
              USE_M0_ARCACHE       = 1,
              USE_M0_ARQOS         = 1, 

              USE_M0_WSTRB         = 1,
   
              USE_M0_BID           = 1,
              USE_M0_BRESP         = 1,
   
              USE_M0_RID           = 1,
              USE_M0_RRESP         = 1,
              USE_M0_RLAST         = 1,

              USE_M0_ARUSER        = 0,
              USE_M0_AWUSER        = 0,
              USE_M0_WUSER         = 0,
              USE_M0_RUSER         = 0,
              USE_M0_BUSER         = 0,
   //-----------------
   // Slave parameters
   //-----------------
              USE_S0_AWREGION      = 1,
              USE_S0_AWLOCK        = 1,
              USE_S0_AWCACHE       = 1,
              USE_S0_AWQOS         = 1,
              USE_S0_AWPROT        = 1,

              USE_S0_ARREGION      = 1,
              USE_S0_ARLOCK        = 1,
              USE_S0_ARCACHE       = 1,
              USE_S0_ARQOS         = 1,
              USE_S0_ARPROT        = 1,   

              USE_S0_WLAST         = 1,

              USE_S0_BRESP         = 1,

              USE_S0_RRESP         = 1,

              USE_S0_AWUSER        = 0,
              USE_S0_ARUSER        = 0,
              USE_S0_WUSER         = 0,
              USE_S0_RUSER         = 0,
              USE_S0_BUSER         = 0,
    
    // ----------------
    // Derived parameters
    // ----------------
              STROBE_WIDTH      = DATA_WIDTH / 8,
              BURST_SIZE        = $clog2(STROBE_WIDTH),

              ACE_LITE_SUPPORT  = 0,
              BACKPRESSURE_DURING_RESET = 0

)
(
    // ----------------
    // Clock & reset
    // ----------------
    input                                          aclk,
    input                                          aresetn,
                         

    // ----------------
    // Master-side AXI interface
    // ----------------
    output reg [M0_ID_WIDTH-1:0]                   m0_awid,
    output [ADDR_WIDTH-1:0]                        m0_awaddr,
    output reg [BURST_LENGTH_WIDTH-1:0]            m0_awlen,
    output reg [2:0]                               m0_awsize,
    output reg [1:0]                               m0_awburst,
    output reg [LOCK_WIDTH-1:0]                    m0_awlock,
    output reg [3:0]                               m0_awcache,
    output reg [2:0]                               m0_awprot,
    output [WRITE_ADDR_USER_WIDTH-1:0]             m0_awuser,
    output reg [3:0]                               m0_awqos,
    output reg [3:0]                               m0_awregion,
    output                                         m0_awvalid,
    input                                          m0_awready,

    output reg [M0_ID_WIDTH-1:0]                   m0_wid,
    output [DATA_WIDTH-1:0]                        m0_wdata,
    output reg [STROBE_WIDTH-1:0]                  m0_wstrb,
    output reg                                     m0_wlast,
    output                                         m0_wvalid,
    output [WRITE_DATA_USER_WIDTH-1:0]             m0_wuser,
    input                                          m0_wready,

    input [M0_ID_WIDTH-1:0]                        m0_bid,
    input [1:0]                                    m0_bresp,
    input [WRITE_RESP_USER_WIDTH-1:0]              m0_buser,
    input                                          m0_bvalid,
    output                                         m0_bready,

    output reg [M0_ID_WIDTH-1:0]                   m0_arid,
    output [ADDR_WIDTH-1:0]                        m0_araddr,
    output reg [BURST_LENGTH_WIDTH-1:0]            m0_arlen,
    output reg [2:0]                               m0_arsize,
    output reg [1:0]                               m0_arburst,
    output reg [LOCK_WIDTH-1:0]                    m0_arlock,
    output reg [3:0]                               m0_arcache,
    output reg [2:0]                               m0_arprot,
    output [READ_ADDR_USER_WIDTH-1:0]              m0_aruser,
    output reg [3:0]                               m0_arqos,
    output reg [3:0]                               m0_arregion,
    output                                         m0_arvalid,
    input                                          m0_arready,

    input [M0_ID_WIDTH-1:0]                        m0_rid,
    input [DATA_WIDTH-1:0]                         m0_rdata,
    input [1:0]                                    m0_rresp,
    input [READ_DATA_USER_WIDTH-1:0]               m0_ruser,
    input                                          m0_rlast,
    input                                          m0_rvalid,
    output                                         m0_rready,  
   
    output [1:0]                                   m0_ardomain, 
    output [3:0]                                   m0_arsnoop,  
    output [1:0]                                   m0_arbar,   
 
    output [1:0]                                   m0_awdomain, 
    output [2:0]                                   m0_awsnoop,  
    output [1:0]                                   m0_awbar,    
    output                                         m0_awunique,

 

    // ----------------
    // Slave-side AXI interface
    // ----------------
    input [S0_ID_WIDTH-1:0]                        s0_awid,
    input [ADDR_WIDTH-1:0]                         s0_awaddr,
    input [BURST_LENGTH_WIDTH-1:0]                 s0_awlen, 
    input [2:0]                                    s0_awsize,
    input [1:0]                                    s0_awburst,
    input [LOCK_WIDTH-1:0]                         s0_awlock,
    input [3:0]                                    s0_awcache,
    input [2:0]                                    s0_awprot,
    input [WRITE_ADDR_USER_WIDTH-1:0]              s0_awuser,
    input [3:0]                                    s0_awqos,
    input [3:0]                                    s0_awregion, 
    input                                          s0_awvalid,
    output                                         s0_awready,

    input [S0_ID_WIDTH-1:0]                        s0_wid,
    input [DATA_WIDTH-1:0]                         s0_wdata,
    input [STROBE_WIDTH-1:0]                       s0_wstrb,
    input                                          s0_wlast,
    input [WRITE_DATA_USER_WIDTH-1:0]              s0_wuser,
    input                                          s0_wvalid,
    output                                         s0_wready,

    output reg [S0_ID_WIDTH-1:0]                   s0_bid,
    output reg [1:0]                               s0_bresp,
    output [WRITE_RESP_USER_WIDTH-1:0]             s0_buser, 
    output                                         s0_bvalid,
    input                                          s0_bready, 

    input [S0_ID_WIDTH-1:0]                        s0_arid,
    input [ADDR_WIDTH-1:0]                         s0_araddr,
    input [BURST_LENGTH_WIDTH-1:0]                 s0_arlen,
    input [2:0]                                    s0_arsize,
    input [1:0]                                    s0_arburst,
    input [LOCK_WIDTH-1:0]                         s0_arlock,
    input [3:0]                                    s0_arcache,
    input [2:0]                                    s0_arprot,
    input [READ_ADDR_USER_WIDTH-1:0]               s0_aruser,
    input [3:0]                                    s0_arqos,
    input [3:0]                                    s0_arregion,
    input                                          s0_arvalid,
    output                                         s0_arready,

    output reg [S0_ID_WIDTH-1:0]                   s0_rid,
    output [DATA_WIDTH-1:0]                        s0_rdata,
    output reg [1:0]                               s0_rresp,
    output reg                                     s0_rlast,
    output [READ_DATA_USER_WIDTH-1:0]              s0_ruser,
    output                                         s0_rvalid,
    input                                          s0_rready,

    input [1:0]                                    s0_ardomain, 
    input [3:0]                                    s0_arsnoop,  
    input [1:0]                                    s0_arbar,   
 
    input [1:0]                                    s0_awdomain, 
    input [2:0]                                    s0_awsnoop,  
    input [1:0]                                    s0_awbar,    
    input                                          s0_awunique
);


    localparam AX_WIDTH         =   (AXI_VERSION == "AXI3")? 
                                        M0_ID_WIDTH+ADDR_WIDTH+BURST_LENGTH_WIDTH+3+2+LOCK_WIDTH+4+3+WRITE_ADDR_USER_WIDTH : 
                                        M0_ID_WIDTH+ADDR_WIDTH+BURST_LENGTH_WIDTH+3+2+LOCK_WIDTH+4+3+WRITE_ADDR_USER_WIDTH+4+4 ;
    localparam W_WIDTH          =   (AXI_VERSION == "AXI3")?
                                        M0_ID_WIDTH+DATA_WIDTH+ADDR_WIDTH+STROBE_WIDTH+1 :
                                        M0_ID_WIDTH+DATA_WIDTH+ADDR_WIDTH+STROBE_WIDTH+1+WRITE_DATA_USER_WIDTH ;

    localparam B_WIDTH          =   (AXI_VERSION == "AXI3")?
                                        M0_ID_WIDTH+2 : 
                                        M0_ID_WIDTH+2+WRITE_DATA_USER_WIDTH;

    localparam R_WIDTH          =   (AXI_VERSION == "AXI3")?
                                        M0_ID_WIDTH+DATA_WIDTH+2+1 :
                                        M0_ID_WIDTH+DATA_WIDTH+2+1+READ_DATA_USER_WIDTH;

    localparam ACE_W            = (ACE_LITE_SUPPORT == 1) ? 8 : 0;
    localparam ACE_R            = (ACE_LITE_SUPPORT == 1) ? 8 : 0;

    localparam PKT_AXPROT_L     = 0;
    localparam PKT_AXPROT_H     = PKT_AXPROT_L + 3 - 1;
    localparam PKT_AXCACHE_L    = PKT_AXPROT_H + 1;
    localparam PKT_AXCACHE_H    = PKT_AXCACHE_L + 4 -1;
    localparam PKT_AXLOCK_L     = PKT_AXCACHE_H + 1;
    localparam PKT_AXLOCK_H     = PKT_AXLOCK_L + LOCK_WIDTH - 1;
    localparam PKT_AXBURST_L    = PKT_AXLOCK_H + 1;
    localparam PKT_AXBURST_H    = PKT_AXBURST_L + 2 -1;
    localparam PKT_AXSIZE_L     = PKT_AXBURST_H + 1;
    localparam PKT_AXSIZE_H     = PKT_AXSIZE_L + 3 -1;
    localparam PKT_AXLEN_L      = PKT_AXSIZE_H + 1;
    localparam PKT_AXLEN_H      = PKT_AXLEN_L + BURST_LENGTH_WIDTH -1;
    localparam PKT_AXADDR_L     = PKT_AXLEN_H + 1;
    localparam PKT_AXADDR_H     = PKT_AXADDR_L + ADDR_WIDTH -1;
    localparam PKT_AXID_L       = PKT_AXADDR_H + 1;
    localparam PKT_AXID_H       = PKT_AXID_L + M0_ID_WIDTH -1;
    localparam PKT_AXUSER_L     = PKT_AXID_H + 1;
    localparam PKT_AXUSER_H     = PKT_AXUSER_L + WRITE_ADDR_USER_WIDTH -1;
    localparam PKT_AXREGION_L   = PKT_AXUSER_H + 1;
    localparam PKT_AXREGION_H   = PKT_AXREGION_L + 4 -1;
    localparam PKT_AXQOS_L      = PKT_AXREGION_H + 1;
    localparam PKT_AXQOS_H      = PKT_AXQOS_L + 4 - 1; 

    localparam PKT_WLAST_L      = 0;
    localparam PKT_WLAST_H      = PKT_WLAST_L +1 -1;
    localparam PKT_WSTRB_L      = PKT_WLAST_H + 1;
    localparam PKT_WSTRB_H      = PKT_WSTRB_L + STROBE_WIDTH -1;
    localparam PKT_WDATA_L      = PKT_WSTRB_H + 1;
    localparam PKT_WDATA_H      = PKT_WDATA_L + DATA_WIDTH -1;
    localparam PKT_WID_L        = PKT_WDATA_H + 1;
    localparam PKT_WID_H        = PKT_WID_L + M0_ID_WIDTH -1;
    localparam PKT_WUSER_L      = PKT_WID_H + 1;
    localparam PKT_WUSER_H      = PKT_WUSER_L + WRITE_DATA_USER_WIDTH -1;

    localparam PKT_BRESP_L      = 0;
    localparam PKT_BRESP_H      = PKT_BRESP_L + 2 -1;
    localparam PKT_BID_L        = PKT_BRESP_H + 1;
    localparam PKT_BID_H        = PKT_BID_L + M0_ID_WIDTH -1;
    localparam PKT_BUSER_L      = PKT_BID_H + 1;
    localparam PKT_BUSER_H      = PKT_BUSER_L + WRITE_DATA_USER_WIDTH -1;

    localparam PKT_RLAST        = 0;
    localparam PKT_RRESP_L      = 1;
    localparam PKT_RRESP_H      = PKT_RRESP_L + 2 -1;
    localparam PKT_RDATA_L      = PKT_RRESP_H + 1;
    localparam PKT_RDATA_H      = PKT_RDATA_L + DATA_WIDTH -1;
    localparam PKT_RID_L        = PKT_RDATA_H + 1;
    localparam PKT_RID_H        = PKT_RID_L + M0_ID_WIDTH -1;
    localparam PKT_RUSER_L      = PKT_RID_H + 1;
    localparam PKT_RUSER_H      = PKT_RUSER_L + READ_DATA_USER_WIDTH -1;

    reg [M0_ID_WIDTH-1:0]                       s0_pipe_awid;
    reg [ADDR_WIDTH-1:0]                        s0_pipe_awaddr;
    reg [BURST_LENGTH_WIDTH-1:0]                s0_pipe_awlen;
    reg [2:0]                                   s0_pipe_awsize;
    reg [1:0]                                   s0_pipe_awburst;
    reg [LOCK_WIDTH-1:0]                        s0_pipe_awlock;
    reg [3:0]                                   s0_pipe_awcache;
    reg [2:0]                                   s0_pipe_awprot;
    reg [WRITE_ADDR_USER_WIDTH-1:0]             s0_pipe_awuser;
    reg [3:0]                                   s0_pipe_awqos;
    reg [3:0]                                   s0_pipe_awregion;
    wire                                        s0_pipeout_awvalid;
    wire                                        s0_pipe_awready;   

    reg [M0_ID_WIDTH-1:0]                       s0_pipe_arid;
    reg [ADDR_WIDTH-1:0]                        s0_pipe_araddr;
    reg [BURST_LENGTH_WIDTH-1:0]                s0_pipe_arlen;
    reg [2:0]                                   s0_pipe_arsize;
    reg [1:0]                                   s0_pipe_arburst;
    reg [LOCK_WIDTH-1:0]                        s0_pipe_arlock;
    reg [3:0]                                   s0_pipe_arcache;
    reg [2:0]                                   s0_pipe_arprot;
    reg [WRITE_ADDR_USER_WIDTH-1:0]             s0_pipe_aruser;
    reg [3:0]                                   s0_pipe_arqos;
    reg [3:0]                                   s0_pipe_arregion;
    wire                                        s0_pipeout_arvalid;
    wire                                        s0_pipe_arready;   
    
    reg [M0_ID_WIDTH-1:0]                       s0_pipe_wid;
    reg [DATA_WIDTH-1:0]                        s0_pipe_wdata;
    reg [STROBE_WIDTH-1:0]                      s0_pipe_wstrb;
    reg [0:0]                                   s0_pipe_wlast;
    reg [WRITE_DATA_USER_WIDTH-1:0]             s0_pipe_wuser;
    reg                                         s0_pipeout_wvalid;
    reg                                         s0_pipe_wvalid;
    reg                                         s0_pipe_wready;

    reg [M0_ID_WIDTH-1:0]                        m0_pipe_bid;
    reg [1:0]                                    m0_pipe_bresp;
    reg [WRITE_RESP_USER_WIDTH-1:0]              m0_pipe_buser;
    reg                                          m0_pipeout_bvalid;
    reg                                          m0_pipe_bready;

    reg [M0_ID_WIDTH-1:0]                        m0_pipe_rid;
    reg [DATA_WIDTH-1:0]                         m0_pipe_rdata;
    reg [1:0]                                    m0_pipe_rresp;
    reg                                          m0_pipe_rlast;
    reg [WRITE_RESP_USER_WIDTH-1:0]              m0_pipe_ruser;
    reg                                          m0_pipeout_rvalid;
    reg                                          m0_pipe_rready;   
    

    reg [AX_WIDTH-1:0] pipein_aw;
    reg [AX_WIDTH-1:0] pipeout_aw;
    reg [W_WIDTH-1:0]  pipein_w;
    reg [W_WIDTH-1:0]  pipeout_w;
    reg [AX_WIDTH-1:0] pipein_ar;
    reg [AX_WIDTH-1:0] pipeout_ar;  
    reg [B_WIDTH-1:0]  pipein_b;
    reg [B_WIDTH-1:0]  pipeout_b;
    reg [R_WIDTH-1:0]  pipein_r;
    reg [R_WIDTH-1:0]  pipeout_r;

    generate if(ACE_LITE_SUPPORT == 1) begin 
       wire [ACE_W - 1:0]  pipein_ace_w;
       wire [ACE_W - 1:0]  pipeout_ace_w;
       wire [ACE_R - 1:0]  pipein_ace_r;
       wire [ACE_R - 1:0]  pipeout_ace_r;

       assign pipein_ace_w =  { s0_awdomain, 
                                s0_awsnoop,  
                                s0_awbar,    
                                s0_awunique
                              };
 
       assign pipein_ace_r =  { s0_ardomain, 
                                s0_arsnoop,  
                                s0_arbar 
                              };


       if(USE_PIPELINE == 1) begin
          altera_avalon_st_pipeline_base #(
              .SYMBOLS_PER_BEAT (1),
              .BITS_PER_SYMBOL  (ACE_W),
              .PIPELINE_READY (1),
              .SYNC_RESET (SYNC_RESET),
              .BACKPRESSURE_DURING_RESET (BACKPRESSURE_DURING_RESET)
          ) ace_w_pipeline (
              .clk (aclk),
              .reset (~aresetn),
              .in_valid (s0_wvalid),
              .in_ready (),
              .in_data  (pipein_ace_w),
              .out_valid (),
              .out_ready (m0_wready),
              .out_data (pipeout_ace_w)
          );

          altera_avalon_st_pipeline_base #(
              .SYMBOLS_PER_BEAT (1),
              .BITS_PER_SYMBOL  (ACE_W),
              .PIPELINE_READY (1),
              .SYNC_RESET (SYNC_RESET),
              .BACKPRESSURE_DURING_RESET (BACKPRESSURE_DURING_RESET)
          ) ace_r_pipeline (
              .clk (aclk),
              .reset (~aresetn),
              .in_valid (s0_arvalid),
              .in_ready (),
              .in_data  (pipein_ace_r),
              .out_valid (),
              .out_ready (m0_arready),
              .out_data (pipeout_ace_r)
          );

       end
       else begin
           assign pipeout_ace_r = pipein_ace_r;
           assign pipeout_ace_w = pipein_ace_w;
       end

       assign {m0_awdomain, m0_awsnoop, m0_awbar, m0_awunique} = pipeout_ace_w;
       assign {m0_ardomain, m0_arsnoop, m0_arbar} = pipeout_ace_r;
    end
    endgenerate

//==================================================================
// AW Channel signal propagation
// AXI4 has optional signals. Propagate a default value to the master-side interface if the slave-side interface does not have the signal.
//======================================================================
    always_comb
    begin
        if (AXI_VERSION == "AXI3") begin
            s0_pipe_awid = s0_awid[M0_ID_WIDTH-1:0];
            s0_pipe_awaddr = s0_awaddr;
            s0_pipe_awlen = s0_awlen;
            s0_pipe_awsize = s0_awsize;
            s0_pipe_awburst = s0_awburst;
            s0_pipe_awlock = s0_awlock;
            s0_pipe_awcache = s0_awcache;
            s0_pipe_awprot = s0_awprot;
            s0_pipe_awuser = s0_awuser[WRITE_ADDR_USER_WIDTH-1:0];
        end else begin
            if (!USE_S0_AWREGION)
                s0_pipe_awregion = '0;
            else
                s0_pipe_awregion = s0_awregion;
            if (!USE_S0_AWLOCK)
                s0_pipe_awlock = '0;
            else
                s0_pipe_awlock = s0_awlock;
            if (!USE_S0_AWCACHE)
                s0_pipe_awcache = '0;
            else
                s0_pipe_awcache = s0_awcache;
            if (!USE_S0_AWQOS)
                s0_pipe_awqos = '0;
            else
                s0_pipe_awqos = s0_awqos;
            if (!USE_S0_AWPROT)
                s0_pipe_awprot = '0;
            else
                s0_pipe_awprot = s0_awprot;
            if (!USE_S0_AWUSER)
                s0_pipe_awuser = '0;
            else
                s0_pipe_awuser = s0_awuser[WRITE_ADDR_USER_WIDTH-1:0];

            // non-optional signals for slave-side interface -propagate these to master-side interface
            s0_pipe_awid = s0_awid[M0_ID_WIDTH-1:0];
            s0_pipe_awaddr = s0_awaddr;
            s0_pipe_awlen = s0_awlen;
            s0_pipe_awsize = s0_awsize;
            s0_pipe_awburst = s0_awburst;
        end
    end

    generate if (AXI_VERSION == "AXI3") begin
        assign pipein_aw = {s0_pipe_awuser,s0_pipe_awid,s0_pipe_awaddr,s0_pipe_awlen,s0_pipe_awsize,s0_pipe_awburst,s0_pipe_awlock,s0_pipe_awcache,s0_pipe_awprot};
    end else begin
        assign pipein_aw = {s0_pipe_awqos,s0_pipe_awregion,s0_pipe_awuser,s0_pipe_awid,s0_pipe_awaddr,s0_pipe_awlen,s0_pipe_awsize,s0_pipe_awburst,s0_pipe_awlock,s0_pipe_awcache,s0_pipe_awprot};
    end
    endgenerate

    generate if (USE_PIPELINE) begin
        altera_avalon_st_pipeline_base #(
            .SYMBOLS_PER_BEAT (1),
            .BITS_PER_SYMBOL  (AX_WIDTH),
            .PIPELINE_READY (1),
            .SYNC_RESET (SYNC_RESET),
            .BACKPRESSURE_DURING_RESET (BACKPRESSURE_DURING_RESET)
        ) aw_channel_pipeline (
            .clk (aclk),
            .reset (~aresetn),
            .in_valid (s0_awvalid),
            .in_ready (s0_pipe_awready),
            .in_data  (pipein_aw),
            .out_valid (s0_pipeout_awvalid),
            .out_ready (m0_awready),
            .out_data (pipeout_aw)
        );
        assign m0_awvalid = s0_pipeout_awvalid;
        assign s0_awready = s0_pipe_awready;

    end else begin
        assign pipeout_aw = pipein_aw;
        assign m0_awvalid      =     s0_awvalid;
        assign s0_awready      =     m0_awready;  
    end
    endgenerate

    assign m0_awuser    = pipeout_aw[PKT_AXUSER_H:PKT_AXUSER_L];
    assign m0_awid      = pipeout_aw[PKT_AXID_H:PKT_AXID_L];
    assign m0_awaddr    = pipeout_aw[PKT_AXADDR_H:PKT_AXADDR_L];
    assign m0_awlen     = pipeout_aw[PKT_AXLEN_H:PKT_AXLEN_L];
    assign m0_awsize    = pipeout_aw[PKT_AXSIZE_H:PKT_AXSIZE_L];
    assign m0_awburst   = pipeout_aw[PKT_AXBURST_H:PKT_AXBURST_L];
    assign m0_awlock    = pipeout_aw[PKT_AXLOCK_H:PKT_AXLOCK_L];
    assign m0_awcache   = pipeout_aw[PKT_AXCACHE_H:PKT_AXCACHE_L];
    assign m0_awprot    = pipeout_aw[PKT_AXPROT_H:PKT_AXPROT_L];
    generate if (AXI_VERSION == "AXI4") begin
        assign m0_awqos     = pipeout_aw[PKT_AXQOS_H:PKT_AXQOS_L];
        assign m0_awregion  = pipeout_aw[PKT_AXREGION_H:PKT_AXREGION_L];
    end
    endgenerate     

//==================================================================
// W Channel signal propagation
// AXI4 has optional signals. Propagate a default value to the master-side interface if the slave-side interface does not have the signal.
//======================================================================   

    always_comb
    begin
        if (AXI_VERSION == "AXI3") begin
            s0_pipe_wid = s0_wid[M0_ID_WIDTH-1:0];
            s0_pipe_wdata = s0_wdata;
            s0_pipe_wstrb = s0_wstrb;
            s0_pipe_wlast = s0_wlast;
        end else begin
            if (!USE_S0_WLAST)
                s0_pipe_wlast = '1;
            else
                s0_pipe_wlast = s0_wlast;
            if (!USE_S0_WUSER)
                s0_pipe_wuser = '0;
            else
                s0_pipe_wuser = s0_wuser[WRITE_DATA_USER_WIDTH-1:0];   
            // non-optional signals for slave-side interface -propagate these to master-side interface
            s0_pipe_wid = s0_wid[M0_ID_WIDTH-1:0];
            s0_pipe_wdata = s0_wdata;
            s0_pipe_wstrb = s0_wstrb;    
        end
    end

    generate if (AXI_VERSION == "AXI3") begin
        assign pipein_w = {s0_pipe_wid,s0_pipe_wdata,s0_pipe_wstrb,s0_pipe_wlast};
    end else begin
        assign pipein_w = {s0_pipe_wuser,s0_pipe_wid,s0_pipe_wdata,s0_pipe_wstrb,s0_pipe_wlast};
    end
    endgenerate

    generate if (USE_PIPELINE) begin
        altera_avalon_st_pipeline_base #(
            .SYMBOLS_PER_BEAT (1),
            .BITS_PER_SYMBOL  (W_WIDTH),
            .PIPELINE_READY (1),
            .SYNC_RESET (SYNC_RESET),
            .BACKPRESSURE_DURING_RESET (BACKPRESSURE_DURING_RESET)
        ) w_channel_pipeline (
            .clk (aclk),
            .reset (~aresetn),
            .in_valid (s0_wvalid),
            .in_ready (s0_pipe_wready),
            .in_data  (pipein_w),
            .out_valid (s0_pipeout_wvalid),
            .out_ready (m0_wready),
            .out_data (pipeout_w)
        );
        assign m0_wvalid = s0_pipeout_wvalid;
        assign s0_wready = s0_pipe_wready;

    end else begin
        assign pipeout_w = pipein_w;
        assign m0_wvalid      =     s0_wvalid;
        assign s0_wready      =     m0_wready;
    end
    endgenerate   

    assign m0_wid       = pipeout_w[PKT_WID_H:PKT_WID_L];
    assign m0_wdata     = pipeout_w[PKT_WDATA_H:PKT_WDATA_L];
    assign m0_wstrb     = pipeout_w[PKT_WSTRB_H:PKT_WSTRB_L];
    assign m0_wlast     = pipeout_w[PKT_WLAST_H:PKT_WLAST_L];
    generate if (AXI_VERSION == "AXI4") begin
        assign m0_wuser     = pipeout_w[PKT_WUSER_H:PKT_WUSER_L];
    end
    endgenerate

//==================================================================
// B Channel signal propagation
// AXI4 has optional signals. Propagate a default value to the slave-side interface if the master-side interface does not have the signal.
//======================================================================   

    always_comb
    begin
        if (AXI_VERSION == "AXI3") begin
            m0_pipe_bid = m0_bid;
            m0_pipe_bresp = m0_bresp;
        end else begin
            if (!USE_M0_BID)
                m0_pipe_bid = '0;
            else
                m0_pipe_bid = m0_bid;
            if (!USE_M0_BRESP)
                m0_pipe_bresp = '0;
            else
                m0_pipe_bresp = m0_bresp;
            if (!USE_M0_BUSER)
                m0_pipe_buser = '0;
            else
                m0_pipe_buser = m0_buser;
        end
    end

    generate if (AXI_VERSION == "AXI3") begin
         assign pipein_b = {m0_pipe_bid,m0_pipe_bresp};
    end else begin
         assign pipein_b = {m0_pipe_buser,m0_pipe_bid,m0_pipe_bresp};
    end 
    endgenerate
    
    generate if (USE_PIPELINE) begin
        altera_avalon_st_pipeline_base #(
            .SYMBOLS_PER_BEAT (1),
            .BITS_PER_SYMBOL  (B_WIDTH),
            .PIPELINE_READY (1),
            .SYNC_RESET (SYNC_RESET),
            .BACKPRESSURE_DURING_RESET (BACKPRESSURE_DURING_RESET)
        ) b_channel_pipeline (
            .clk (aclk),
            .reset (~aresetn),
            .in_valid (m0_bvalid),
            .in_ready (m0_pipe_bready),
            .in_data  (pipein_b),
            .out_valid (m0_pipeout_bvalid),
            .out_ready (s0_bready),
            .out_data (pipeout_b)
        );
        assign s0_bvalid = m0_pipeout_bvalid;
        assign m0_bready = m0_pipe_bready;

    end else begin
        assign pipeout_b = pipein_b;
        assign s0_bvalid      =     m0_bvalid;
        assign m0_bready      =     s0_bready;
    end
    endgenerate   

    assign s0_bid       = pipeout_b[PKT_BID_H:PKT_BID_L];
    assign s0_bresp     = pipeout_b[PKT_BRESP_H:PKT_BRESP_L];
    generate if (AXI_VERSION == "AXI4") begin
        assign s0_buser     = pipeout_b[PKT_BUSER_H:PKT_BUSER_L];
    end
    endgenerate


//==================================================================
// AR Channel signal propagation
// AXI4 has optional signals. Propagate a default value to the master-side interface if the slave-side interface does not have the signal.
//======================================================================
    always_comb
    begin
        if (AXI_VERSION == "AXI3") begin
            s0_pipe_arid = s0_arid[M0_ID_WIDTH-1:0];
            s0_pipe_araddr = s0_araddr;
            s0_pipe_arlen = s0_arlen;
            s0_pipe_arsize = s0_arsize;
            s0_pipe_arburst = s0_arburst;
            s0_pipe_arlock = s0_arlock;
            s0_pipe_arcache = s0_arcache;
            s0_pipe_arprot = s0_arprot;
            s0_pipe_aruser = s0_aruser; // addded user signal to support HPS. This is not within AXI3 spec.
        end else begin
            if (!USE_S0_ARREGION)
                s0_pipe_arregion = '0;
            else
                s0_pipe_arregion = s0_arregion;
            if (!USE_S0_ARLOCK)
                s0_pipe_arlock = '0;
            else
                s0_pipe_arlock = s0_arlock;
            if (!USE_S0_ARCACHE)
                s0_pipe_arcache = '0;
            else
                s0_pipe_arcache = s0_arcache;
            if (!USE_S0_ARQOS)
                s0_pipe_arqos = '0;
            else
                s0_pipe_arqos = s0_arqos;
            if (!USE_S0_ARPROT)
                s0_pipe_arprot = '0;
            else
                s0_pipe_arprot = s0_arprot;
            if (!USE_S0_ARUSER)
                s0_pipe_aruser = '0;
            else
                s0_pipe_aruser = s0_aruser[READ_ADDR_USER_WIDTH-1:0];

            // non-optional signals for slave-side interface -propagate these to master-side interface
            s0_pipe_arid = s0_arid[M0_ID_WIDTH-1:0];
            s0_pipe_araddr = s0_araddr;
            s0_pipe_arlen = s0_arlen;
            s0_pipe_arsize = s0_arsize;
            s0_pipe_arburst = s0_arburst;
        end
    end

    generate if (AXI_VERSION == "AXI3") begin
        assign pipein_ar = {s0_pipe_aruser,s0_pipe_arid,s0_pipe_araddr,s0_pipe_arlen,s0_pipe_arsize,s0_pipe_arburst,s0_pipe_arlock,s0_pipe_arcache,s0_pipe_arprot};
    end else begin
        assign pipein_ar = {s0_pipe_arqos,s0_pipe_arregion,s0_pipe_aruser,s0_pipe_arid,s0_pipe_araddr,s0_pipe_arlen,s0_pipe_arsize,s0_pipe_arburst,s0_pipe_arlock,s0_pipe_arcache,s0_pipe_arprot};
    end
    endgenerate

    generate if (USE_PIPELINE) begin
        altera_avalon_st_pipeline_base #(
            .SYMBOLS_PER_BEAT (1),
            .BITS_PER_SYMBOL  (AX_WIDTH),
            .PIPELINE_READY (1), 
            .SYNC_RESET (SYNC_RESET),
            .BACKPRESSURE_DURING_RESET (BACKPRESSURE_DURING_RESET)
        ) ar_channel_pipeline (
            .clk (aclk),
            .reset (~aresetn),
            .in_valid (s0_arvalid),
            .in_ready (s0_pipe_arready),
            .in_data  (pipein_ar),
            .out_valid (s0_pipeout_arvalid),
            .out_ready (m0_arready),
            .out_data (pipeout_ar)
        );
        assign m0_arvalid = s0_pipeout_arvalid;
        assign s0_arready = s0_pipe_arready;

    end else begin
        assign pipeout_ar = pipein_ar;
        assign m0_arvalid      =     s0_arvalid;
        assign s0_arready      =     m0_arready;
    end
    endgenerate

    assign m0_aruser    = pipeout_ar[PKT_AXUSER_H:PKT_AXUSER_L];
    assign m0_arid      = pipeout_ar[PKT_AXID_H:PKT_AXID_L];
    assign m0_araddr    = pipeout_ar[PKT_AXADDR_H:PKT_AXADDR_L];
    assign m0_arlen     = pipeout_ar[PKT_AXLEN_H:PKT_AXLEN_L];
    assign m0_arsize    = pipeout_ar[PKT_AXSIZE_H:PKT_AXSIZE_L];
    assign m0_arburst   = pipeout_ar[PKT_AXBURST_H:PKT_AXBURST_L];
    assign m0_arlock    = pipeout_ar[PKT_AXLOCK_H:PKT_AXLOCK_L];
    assign m0_arcache   = pipeout_ar[PKT_AXCACHE_H:PKT_AXCACHE_L];
    assign m0_arprot    = pipeout_ar[PKT_AXPROT_H:PKT_AXPROT_L];
    generate if (AXI_VERSION == "AXI4") begin
        assign m0_arqos     = pipeout_ar[PKT_AXQOS_H:PKT_AXQOS_L];
        assign m0_arregion  = pipeout_ar[PKT_AXREGION_H:PKT_AXREGION_L];
    end
    endgenerate   

//==================================================================
// R Channel signal propagation
// AXI4 has optional signals. Propagate a default value to the slave-side interface if the master-side interface does not have the signal.
//======================================================================

    always_comb
    begin
        if (AXI_VERSION == "AXI3") begin
            m0_pipe_rid = m0_rid;
            m0_pipe_rresp = m0_rresp;
            m0_pipe_rlast = m0_rlast;
        end else begin
            if (!USE_M0_RID)
                m0_pipe_rid = '0;
            else
                m0_pipe_rid = m0_rid;
            if (!USE_M0_RRESP)
                m0_pipe_rresp = '0;
            else
                m0_pipe_rresp = m0_rresp;
            if (!USE_M0_RLAST)
                m0_pipe_rlast = '0;
            else
                m0_pipe_rlast = m0_rlast;   
            if (!USE_M0_RUSER)
                m0_pipe_ruser = '0;
            else
                m0_pipe_ruser = m0_ruser;
        end
        //non-optional signals
        m0_pipe_rdata = m0_rdata;
    end

    generate if (AXI_VERSION == "AXI3") begin
         assign pipein_r = {m0_pipe_rid,m0_pipe_rdata,m0_pipe_rresp,m0_pipe_rlast};
    end else begin
         assign pipein_r = {m0_pipe_ruser,m0_pipe_rid,m0_pipe_rdata,m0_pipe_rresp,m0_pipe_rlast};
    end
    endgenerate

    generate if (USE_PIPELINE) begin
        altera_avalon_st_pipeline_base #(
            .SYMBOLS_PER_BEAT (1),
            .BITS_PER_SYMBOL  (R_WIDTH),
            .PIPELINE_READY (1),
            .SYNC_RESET (SYNC_RESET),
            .BACKPRESSURE_DURING_RESET (BACKPRESSURE_DURING_RESET)
        ) r_channel_pipeline (
            .clk (aclk),
            .reset (~aresetn),
            .in_valid (m0_rvalid),
            .in_ready (m0_pipe_rready),
            .in_data  (pipein_r),
            .out_valid (m0_pipeout_rvalid),
            .out_ready (s0_rready),
            .out_data (pipeout_r)
        );
        assign s0_rvalid = m0_pipeout_rvalid;
        assign m0_rready = m0_pipe_rready;

    end else begin
        assign pipeout_r = pipein_r;
        assign s0_rvalid      =     m0_rvalid;
        assign m0_rready      =     s0_rready;
    end
    endgenerate

    assign s0_rid       = pipeout_r[PKT_RID_H:PKT_RID_L];
    assign s0_rdata     = pipeout_r[PKT_RDATA_H:PKT_RDATA_L];
    assign s0_rresp     = pipeout_r[PKT_RRESP_H:PKT_RRESP_L];
    assign s0_rlast     = pipeout_r[PKT_RLAST];
    generate if (AXI_VERSION == "AXI4") begin
        assign s0_ruser     = pipeout_r[PKT_RUSER_H:PKT_RUSER_L];
    end
    endgenerate    

/*
    generate if (AXI_VERSION == "AXI3") begin
        assign {m0_awid,m0_awaddr,m0_awlen,m0_awsize,m0_awburst,m0_awlock,m0_awcache,m0_awprot} = pipeout_aw;
    end else begin
        //assign {m0_awuser,m0_awqos,m0_awregion,m0_awid,m0_awaddr,m0_awlen,m0_awsize,m0_awburst,m0_awlock,m0_awcache,m0_awprot} = pipeout_aw;
        assign {m0_awid,m0_awaddr,m0_awlen,m0_awsize,m0_awburst,m0_awlock,m0_awcache,m0_awprot} = pipeout_aw;
    end
    endgenerate
*/
        
endmodule


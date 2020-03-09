// Copyright 2014-2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the “License”); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an “AS IS” BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// `timescale 1ns/1ps
// `define SOD 0.5

`define log2(VALUE) ((VALUE) < ( 1 ) ? 0 : (VALUE) < ( 2 ) ? 1 : (VALUE) < ( 4 ) ? 2 : (VALUE) < ( 8 ) ? 3 : (VALUE) < ( 16 )  ? 4 : (VALUE) < ( 32 )  ? 5 : (VALUE) < ( 64 )  ? 6 : (VALUE) < ( 128 ) ? 7 : (VALUE) < ( 256 ) ? 8 : (VALUE) < ( 512 ) ? 9 : (VALUE) < ( 1024 ) ? 10 : (VALUE) < ( 2048 ) ? 11 : (VALUE) < ( 4096 ) ? 12 : (VALUE) < ( 8192 ) ? 13 : (VALUE) < ( 16384 ) ? 14 : (VALUE) < ( 32768 ) ? 15 : (VALUE) < ( 65536 ) ? 16 : (VALUE) < ( 131072 ) ? 17 : (VALUE) < ( 262144 ) ? 18 : (VALUE) < ( 524288 ) ? 19 : (VALUE) < ( 1048576 ) ? 20 : (VALUE) < ( 1048576 * 2 ) ? 21 : (VALUE) < ( 1048576 * 4 ) ? 22 : (VALUE) < ( 1048576 * 8 ) ? 23 : (VALUE) < ( 1048576 * 16 ) ? 24 : 25)

`define OKAY   2'b00
`define EXOKAY 2'b01
`define SLVERR 2'b10
`define DECERR 2'b11

module   axi_mem_if_var_latency
#(
    parameter AXI4_ADDRESS_WIDTH = 32,
    parameter AXI4_RDATA_WIDTH   = 64,
    parameter AXI4_WDATA_WIDTH   = 64,
    parameter AXI4_ID_WIDTH      = 16,
    parameter AXI4_USER_WIDTH    = 10,
    parameter AXI_NUMBYTES       = AXI4_WDATA_WIDTH/8,
    parameter MEM_ADDR_WIDTH     = 13,
    parameter BUFF_DEPTH_SLAVE   = 4,

    parameter LATENCY_AW         = 50,
    parameter LATENCY_AR         = 50,
    parameter LATENCY_R          = 50,
    parameter LATENCY_B          = 50,
    parameter LATENCY_W          = 50
)
(
    input logic                                     ACLK,
    input logic                                     ARESETn,
    // ---------------------------------------------------------
    // AXI TARG Port Declarations ------------------------------
    // ---------------------------------------------------------
    //AXI write address bus -------------- // USED// -----------
    input  logic [AXI4_ID_WIDTH-1:0]                AWID_i     ,
    input  logic [AXI4_ADDRESS_WIDTH-1:0]           AWADDR_i   ,
    input  logic [ 7:0]                             AWLEN_i    ,
    input  logic [ 2:0]                             AWSIZE_i   ,
    input  logic [ 1:0]                             AWBURST_i  ,
    input  logic                                    AWLOCK_i   ,
    input  logic [ 3:0]                             AWCACHE_i  ,
    input  logic [ 2:0]                             AWPROT_i   ,
    input  logic [ 3:0]                             AWREGION_i ,
    input  logic [ AXI4_USER_WIDTH-1:0]             AWUSER_i   ,
    input  logic [ 3:0]                             AWQOS_i    ,
    input  logic                                    AWVALID_i  ,
    output logic                                    AWREADY_o  ,
    // ---------------------------------------------------------

    //AXI write data bus -------------- // USED// --------------
    input  logic [AXI_NUMBYTES-1:0][7:0]            WDATA_i    ,
    input  logic [AXI_NUMBYTES-1:0]                 WSTRB_i    ,
    input  logic                                    WLAST_i    ,
    input  logic [AXI4_USER_WIDTH-1:0]              WUSER_i    ,
    input  logic                                    WVALID_i   ,
    output logic                                    WREADY_o   ,
    // ---------------------------------------------------------

    //AXI write response bus -------------- // USED// ----------
    output logic   [AXI4_ID_WIDTH-1:0]              BID_o      ,
    output logic   [ 1:0]                           BRESP_o    ,
    output logic                                    BVALID_o   ,
    output logic   [AXI4_USER_WIDTH-1:0]            BUSER_o    ,
    input  logic                                    BREADY_i   ,
    // ---------------------------------------------------------

    //AXI read address bus -------------------------------------
    input  logic [AXI4_ID_WIDTH-1:0]                ARID_i     ,
    input  logic [AXI4_ADDRESS_WIDTH-1:0]           ARADDR_i   ,
    input  logic [ 7:0]                             ARLEN_i    ,
    input  logic [ 2:0]                             ARSIZE_i   ,
    input  logic [ 1:0]                             ARBURST_i  ,
    input  logic                                    ARLOCK_i   ,
    input  logic [ 3:0]                             ARCACHE_i  ,
    input  logic [ 2:0]                             ARPROT_i   ,
    input  logic [ 3:0]                             ARREGION_i ,
    input  logic [ AXI4_USER_WIDTH-1:0]             ARUSER_i   ,
    input  logic [ 3:0]                             ARQOS_i    ,
    input  logic                                    ARVALID_i  ,
    output logic                                    ARREADY_o  ,
    // ---------------------------------------------------------

    //AXI read data bus ----------------------------------------
    output  logic [AXI4_ID_WIDTH-1:0]               RID_o      ,
    output  logic [AXI4_RDATA_WIDTH-1:0]            RDATA_o    ,
    output  logic [ 1:0]                            RRESP_o    ,
    output  logic                                   RLAST_o    ,
    output  logic [AXI4_USER_WIDTH-1:0]             RUSER_o    ,
    output  logic                                   RVALID_o   ,
    input   logic                                   RREADY_i   ,
    // ---------------------------------------------------------

    output logic                                    CEN        ,
    output logic                                    WEN        ,
    output logic  [MEM_ADDR_WIDTH-1:0]              A          ,
    output logic  [AXI4_WDATA_WIDTH-1:0]            D          ,
    output logic  [AXI_NUMBYTES-1:0]                BE         ,
    input  logic  [AXI4_RDATA_WIDTH-1:0]            Q
);


  // -----------------------------------------------------------
  // AXI TARG Port Declarations --------------------------------
  // -----------------------------------------------------------
  //AXI write address bus --------------------------------------
  logic [LATENCY_AW-1:0][AXI4_ID_WIDTH-1:0]             AWID       ;
  logic [LATENCY_AW-1:0][AXI4_ADDRESS_WIDTH-1:0]        AWADDR     ;
  logic [LATENCY_AW-1:0][ 7:0]                          AWLEN      ;
  logic [LATENCY_AW-1:0][ 2:0]                          AWSIZE     ;
  logic [LATENCY_AW-1:0][ 1:0]                          AWBURST    ;
  logic [LATENCY_AW-1:0]                                AWLOCK     ;
  logic [LATENCY_AW-1:0][ 3:0]                          AWCACHE    ;
  logic [LATENCY_AW-1:0][ 2:0]                          AWPROT     ;
  logic [LATENCY_AW-1:0][ 3:0]                          AWREGION   ;
  logic [LATENCY_AW-1:0][ AXI4_USER_WIDTH-1:0]          AWUSER     ;
  logic [LATENCY_AW-1:0][ 3:0]                          AWQOS      ;
  logic [LATENCY_AW-1:0]                                AWVALID    ;
  logic                                                 AWREADY    ;
  logic                                                 AWREADY_int;
  // -----------------------------------------------------------

  //AXI write data bus -----------------------------------------
  logic [LATENCY_W-1:0][AXI_NUMBYTES-1:0][7:0]          WDATA      ;
  logic [LATENCY_W-1:0][AXI_NUMBYTES-1:0]               WSTRB      ;
  logic [LATENCY_W-1:0]                                 WLAST      ;
  logic [LATENCY_W-1:0][AXI4_USER_WIDTH-1:0]            WUSER      ;
  logic [LATENCY_W-1:0]                                 WVALID     ;
  logic                                                 WREADY     ;
  logic                                                 WREADY_int ;
  // -----------------------------------------------------------

  //AXI write response bus -------------------------------------
  logic [LATENCY_B-1:0][AXI4_ID_WIDTH-1:0]             BID         ;
  logic [LATENCY_B-1:0][ 1:0]                          BRESP       ;
  logic [LATENCY_B-1:0]                                BVALID      ;
  logic [LATENCY_B-1:0] [AXI4_USER_WIDTH-1:0]          BUSER       ;
  logic                                                BREADY      ;

  logic [AXI4_ID_WIDTH-1:0]                            BID_int     ;
  logic [ 1:0]                                         BRESP_int   ;
  logic                                                BVALID_int  ;
  logic [AXI4_USER_WIDTH-1:0]                          BUSER_int   ;

  // -----------------------------------------------------------

  //AXI read address bus ---------------------------------------
  logic [LATENCY_AR-1:0][AXI4_ID_WIDTH-1:0]            ARID       ;
  logic [LATENCY_AR-1:0][AXI4_ADDRESS_WIDTH-1:0]       ARADDR     ;
  logic [LATENCY_AR-1:0][ 7:0]                         ARLEN      ;
  logic [LATENCY_AR-1:0][ 2:0]                         ARSIZE     ;
  logic [LATENCY_AR-1:0][ 1:0]                         ARBURST    ;
  logic [LATENCY_AR-1:0]                               ARLOCK     ;
  logic [LATENCY_AR-1:0][ 3:0]                         ARCACHE    ;
  logic [LATENCY_AR-1:0][ 2:0]                         ARPROT     ;
  logic [LATENCY_AR-1:0][ 3:0]                         ARREGION   ;
  logic [LATENCY_AR-1:0][ AXI4_USER_WIDTH-1:0]         ARUSER     ;
  logic [LATENCY_AR-1:0][ 3:0]                         ARQOS      ;
  logic [LATENCY_AR-1:0]                               ARVALID    ;
  logic                                                ARREADY    ;
  logic                                                ARREADY_int;
  // -----------------------------------------------------------

  //AXI read data bus ------------------------------------------
  logic [LATENCY_R-1:0][AXI4_ID_WIDTH-1:0]             RID        ;
  logic [LATENCY_R-1:0][AXI4_RDATA_WIDTH-1:0]          RDATA      ;
  logic [LATENCY_R-1:0][ 1:0]                          RRESP      ;
  logic [LATENCY_R-1:0]                                RLAST      ;
  logic [LATENCY_R-1:0][AXI4_USER_WIDTH-1:0]           RUSER      ;
  logic [LATENCY_R-1:0]                                RVALID     ;
  logic                                                RREADY     ;

  logic [AXI4_ID_WIDTH-1:0]                            RID_int    ;
  logic [AXI4_RDATA_WIDTH-1:0]                         RDATA_int  ;
  logic [ 1:0]                                         RRESP_int  ;
  logic                                                RLAST_int  ;
  logic [AXI4_USER_WIDTH-1:0]                          RUSER_int  ;
  logic                                                RVALID_int ;
  // -----------------------------------------------------------


  //PIPELINE
  //AR PIPE
  int unsigned i,j,k,l,m;

    always_ff @(posedge ACLK, negedge ARESETn)
    begin
      if(ARESETn == 1'b0)
      begin
           for(i=0;i<LATENCY_AW;i++)
           begin
              AWID[i]    <= '0;
              AWADDR[i]  <= '0;
              AWLEN[i]   <= '0;
              AWSIZE[i]  <= '0;
              AWBURST[i] <= '0;
              AWLOCK[i]  <= '0;
              AWCACHE[i] <= '0;
              AWPROT[i]  <= '0;
              AWREGION[i]<= '0;
              AWUSER[i]  <= '0;
              AWQOS[i]   <= '0;
              AWVALID[i] <= '0;
           end
      end
      else
      begin
           if(AWREADY)
           begin
              AWID[0]    <=   AWID_i    ;
              AWADDR[0]  <=   AWADDR_i  ;
              AWLEN[0]   <=   AWLEN_i   ;
              AWSIZE[0]  <=   AWSIZE_i  ;
              AWBURST[0] <=   AWBURST_i ;
              AWLOCK[0]  <=   AWLOCK_i  ;
              AWCACHE[0] <=   AWCACHE_i ;
              AWPROT[0]  <=   AWPROT_i  ;
              AWREGION[0]<=   AWREGION_i;
              AWUSER[0]  <=   AWUSER_i  ;
              AWQOS[0]   <=   AWQOS_i   ;
              AWVALID[0] <=   AWVALID_i ;

              AWID[LATENCY_AW-1:1]    <=   AWID[LATENCY_AW-2:0]    ;
              AWADDR[LATENCY_AW-1:1]  <=   AWADDR[LATENCY_AW-2:0]  ;
              AWLEN[LATENCY_AW-1:1]   <=   AWLEN[LATENCY_AW-2:0]   ;
              AWSIZE[LATENCY_AW-1:1]  <=   AWSIZE[LATENCY_AW-2:0]  ;
              AWBURST[LATENCY_AW-1:1] <=   AWBURST[LATENCY_AW-2:0] ;
              AWLOCK[LATENCY_AW-1:1]  <=   AWLOCK[LATENCY_AW-2:0]  ;
              AWCACHE[LATENCY_AW-1:1] <=   AWCACHE[LATENCY_AW-2:0] ;
              AWPROT[LATENCY_AW-1:1]  <=   AWPROT[LATENCY_AW-2:0]  ;
              AWREGION[LATENCY_AW-1:1]<=   AWREGION[LATENCY_AW-2:0];
              AWUSER[LATENCY_AW-1:1]  <=   AWUSER[LATENCY_AW-2:0]  ;
              AWQOS[LATENCY_AW-1:1]   <=   AWQOS[LATENCY_AW-2:0]   ;
              AWVALID[LATENCY_AW-1:1] <=   AWVALID[LATENCY_AW-2:0] ;
           end
      end
    end


    always_ff @(posedge ACLK, negedge ARESETn)
    begin
      if(ARESETn == 1'b0)
      begin
           for(j=0;j<LATENCY_AR;j++)
           begin
              ARID[j]    <= '0;
              ARADDR[j]  <= '0;
              ARLEN[j]   <= '0;
              ARSIZE[j]  <= '0;
              ARBURST[j] <= '0;
              ARLOCK[j]  <= '0;
              ARCACHE[j] <= '0;
              ARPROT[j]  <= '0;
              ARREGION[j]<= '0;
              ARUSER[j]  <= '0;
              ARQOS[j]   <= '0;
              ARVALID[j] <= '0;
           end
      end
      else
      begin
           if(ARREADY)
           begin
              ARID[0]    <=   ARID_i    ;
              ARADDR[0]  <=   ARADDR_i  ;
              ARLEN[0]   <=   ARLEN_i   ;
              ARSIZE[0]  <=   ARSIZE_i  ;
              ARBURST[0] <=   ARBURST_i ;
              ARLOCK[0]  <=   ARLOCK_i  ;
              ARCACHE[0] <=   ARCACHE_i ;
              ARPROT[0]  <=   ARPROT_i  ;
              ARREGION[0]<=   ARREGION_i;
              ARUSER[0]  <=   ARUSER_i  ;
              ARQOS[0]   <=   ARQOS_i   ;
              ARVALID[0] <=   ARVALID_i ;

              ARID[LATENCY_AR-1:1]    <=   ARID[LATENCY_AR-2:0]    ;
              ARADDR[LATENCY_AR-1:1]  <=   ARADDR[LATENCY_AR-2:0]  ;
              ARLEN[LATENCY_AR-1:1]   <=   ARLEN[LATENCY_AR-2:0]   ;
              ARSIZE[LATENCY_AR-1:1]  <=   ARSIZE[LATENCY_AR-2:0]  ;
              ARBURST[LATENCY_AR-1:1] <=   ARBURST[LATENCY_AR-2:0] ;
              ARLOCK[LATENCY_AR-1:1]  <=   ARLOCK[LATENCY_AR-2:0]  ;
              ARCACHE[LATENCY_AR-1:1] <=   ARCACHE[LATENCY_AR-2:0] ;
              ARPROT[LATENCY_AR-1:1]  <=   ARPROT[LATENCY_AR-2:0]  ;
              ARREGION[LATENCY_AR-1:1]<=   ARREGION[LATENCY_AR-2:0];
              ARUSER[LATENCY_AR-1:1]  <=   ARUSER[LATENCY_AR-2:0]  ;
              ARQOS[LATENCY_AR-1:1]   <=   ARQOS[LATENCY_AR-2:0]   ;
              ARVALID[LATENCY_AR-1:1] <=   ARVALID[LATENCY_AR-2:0] ;
           end
      end
    end

    assign RID_o    = RID   [LATENCY_R-1];
    assign RDATA_o  = RDATA [LATENCY_R-1];
    assign RRESP_o  = RRESP [LATENCY_R-1];
    assign RLAST_o  = RLAST [LATENCY_R-1];
    assign RUSER_o  = RUSER [LATENCY_R-1];
    assign RVALID_o = RVALID[LATENCY_R-1];

    // READ RESP
    always_ff @(posedge ACLK, negedge ARESETn)
    begin
      if(ARESETn == 1'b0)
      begin
           for(k=0;k<LATENCY_R;k++)
           begin
              RID[k]    <= '0;
              RDATA[k]  <= '0;
              RRESP[k]  <= '0;
              RLAST[k]  <= '0;
              RUSER[k]  <= '0;
              RVALID[k] <= '0;
           end
      end
      else
      begin
           if(RREADY)
           begin
              RID[0]    <= RID_int    ;
              RDATA[0]  <= RDATA_int  ;
              RRESP[0]  <= RRESP_int  ;
              RLAST[0]  <= RLAST_int  ;
              RUSER[0]  <= RUSER_int  ;
              RVALID[0] <= RVALID_int ;

              RID[LATENCY_R-1:1]      <= RID[LATENCY_R-2:0]   ;
              RDATA[LATENCY_R-1:1]    <= RDATA[LATENCY_R-2:0] ;
              RRESP[LATENCY_R-1:1]    <= RRESP[LATENCY_R-2:0] ;
              RLAST[LATENCY_R-1:1]    <= RLAST[LATENCY_R-2:0] ;
              RUSER[LATENCY_R-1:1]    <= RUSER[LATENCY_R-2:0] ;
              RVALID[LATENCY_R-1:1]   <= RVALID[LATENCY_R-2:0];
           end
      end
    end


    assign BID_o    = BID   [LATENCY_B-1];
    assign BRESP_o  = BRESP [LATENCY_B-1];
    assign BUSER_o  = BUSER [LATENCY_B-1];
    assign BVALID_o = BVALID[LATENCY_B-1];

    // READ RESP
    always_ff @(posedge ACLK, negedge ARESETn)
    begin
      if(ARESETn == 1'b0)
      begin
           for(l=0;l<LATENCY_B;l++)
           begin
              BID[l]    <= '0;
              BRESP[l]  <= '0;
              BUSER[l]  <= '0;
              BVALID[l] <= '0;
           end
      end
      else
      begin
           if(BREADY)
           begin
              BID[0]    <=  BID_int;
              BRESP[0]  <=  BRESP_int;
              BUSER[0]  <=  BUSER_int;
              BVALID[0] <=  BVALID_int;

              BID[LATENCY_B-1:1]      <= BID[LATENCY_B-2:0]   ;
              BRESP[LATENCY_B-1:1]    <= BRESP[LATENCY_B-2:0] ;
              BUSER[LATENCY_B-1:1]    <= BUSER[LATENCY_B-2:0] ;
              BVALID[LATENCY_B-1:1]   <= BVALID[LATENCY_B-2:0];
           end
      end
    end


    // WRITE
    /*
  //AXI write data bus -----------------------------------------
  logic [LATENCY_W-1:0][AXI_NUMBYTES-1:0][7:0]          WDATA      ;
  logic [LATENCY_W-1:0][AXI_NUMBYTES-1:0]               WSTRB      ;
  logic [LATENCY_W-1:0]                                 WLAST      ;
  logic [LATENCY_W-1:0][AXI4_USER_WIDTH-1:0]            WUSER      ;
  logic [LATENCY_W-1:0]                                 WVALID     ;
  logic                                                 WREADY     ;
    */
    always_ff @(posedge ACLK, negedge ARESETn)
    begin
      if(ARESETn == 1'b0)
      begin
           for(m=0;m<LATENCY_W;m++)
           begin
              WDATA[m]   <= '0;
              WSTRB[m]   <= '0;
              WLAST[m]   <= '0;
              WUSER[m]   <= '0;
              WVALID[m]  <= '0;

           end
      end
      else
      begin
           if(WREADY)
           begin
              WDATA[0]   <= WDATA_i ;
              WSTRB[0]   <= WSTRB_i ;
              WLAST[0]   <= WLAST_i ;
              WUSER[0]   <= WUSER_i ;
              WVALID[0]  <= WVALID_i;

              WDATA [LATENCY_W-1:1]  <= WDATA [LATENCY_W-2:0];
              WSTRB [LATENCY_W-1:1]  <= WSTRB [LATENCY_W-2:0];
              WLAST [LATENCY_W-1:1]  <= WLAST [LATENCY_W-2:0];
              WUSER [LATENCY_W-1:1]  <= WUSER [LATENCY_W-2:0];
              WVALID[LATENCY_W-1:1]  <= WVALID[LATENCY_W-2:0];
           end
      end
    end




    assign  AWREADY    =   AWREADY_int | ~AWVALID[LATENCY_AW-1];
    assign  ARREADY    =   ARREADY_int | ~ARVALID[LATENCY_AR-1];
    assign  WREADY     =   WREADY_int  | ~WVALID[LATENCY_W-1];

    assign  AWREADY_o =   AWREADY;
    assign  ARREADY_o =   ARREADY;
    assign  RREADY    =   RREADY_i | ~RVALID[LATENCY_R-1];
    assign  BREADY    =   BREADY_i | ~BVALID[LATENCY_B-1];
    assign  WREADY_o  =   WREADY;

    axi_mem_if
    #(
        .AXI4_ADDRESS_WIDTH(AXI4_ADDRESS_WIDTH),
        .AXI4_RDATA_WIDTH(AXI4_RDATA_WIDTH),
        .AXI4_WDATA_WIDTH(AXI4_WDATA_WIDTH),
        .AXI4_ID_WIDTH(AXI4_ID_WIDTH),
        .AXI4_USER_WIDTH(AXI4_USER_WIDTH),
        .MEM_ADDR_WIDTH(MEM_ADDR_WIDTH),
        .BUFF_DEPTH_SLAVE(BUFF_DEPTH_SLAVE)
    )
    axi_mem_if_i
    (
        .ACLK(ACLK),
        .ARESETn(ARESETn),

        .AWVALID_i  ( AWVALID[LATENCY_AW-1]  ),
        .AWADDR_i   ( AWADDR[LATENCY_AW-1]   ),
        .AWPROT_i   ( AWPROT[LATENCY_AW-1]   ),
        .AWREGION_i ( AWREGION[LATENCY_AW-1] ),
        .AWLEN_i    ( AWLEN[LATENCY_AW-1]    ),
        .AWSIZE_i   ( AWSIZE[LATENCY_AW-1]   ),
        .AWBURST_i  ( AWBURST[LATENCY_AW-1]  ),
        .AWLOCK_i   ( AWLOCK[LATENCY_AW-1]   ),
        .AWCACHE_i  ( AWCACHE[LATENCY_AW-1]  ),
        .AWQOS_i    ( AWQOS[LATENCY_AW-1]    ),
        .AWID_i     ( AWID[LATENCY_AW-1]     ),
        .AWUSER_i   ( AWUSER[LATENCY_AW-1]   ),
        .AWREADY_o  ( AWREADY_int            ),

        .ARVALID_i  ( ARVALID[LATENCY_AR-1]  ),
        .ARADDR_i   ( ARADDR[LATENCY_AR-1]   ),
        .ARPROT_i   ( ARPROT[LATENCY_AR-1]   ),
        .ARREGION_i ( ARREGION[LATENCY_AR-1] ),
        .ARLEN_i    ( ARLEN[LATENCY_AR-1]    ),
        .ARSIZE_i   ( ARSIZE[LATENCY_AR-1]   ),
        .ARBURST_i  ( ARBURST[LATENCY_AR-1]  ),
        .ARLOCK_i   ( ARLOCK[LATENCY_AR-1]   ),
        .ARCACHE_i  ( ARCACHE[LATENCY_AR-1]  ),
        .ARQOS_i    ( ARQOS[LATENCY_AR-1]    ),
        .ARID_i     ( ARID[LATENCY_AR-1]     ),
        .ARUSER_i   ( ARUSER[LATENCY_AR-1]   ),
        .ARREADY_o  ( ARREADY_int            ),

        .RVALID_o   ( RVALID_int             ),
        .RDATA_o    ( RDATA_int              ),
        .RRESP_o    ( RRESP_int              ),
        .RLAST_o    ( RLAST_int              ),
        .RID_o      ( RID_int                ),
        .RUSER_o    ( RUSER_int              ),
        .RREADY_i   ( RREADY                 ),

        .WVALID_i   ( WVALID[LATENCY_W-1]    ),
        .WDATA_i    ( WDATA[LATENCY_W-1]     ),
        .WSTRB_i    ( WSTRB[LATENCY_W-1]     ),
        .WLAST_i    ( WLAST[LATENCY_W-1]     ),
        .WUSER_i    ( WUSER[LATENCY_W-1]     ),
        .WREADY_o   ( WREADY_int             ),

        .BVALID_o  ( BVALID_int              ),
        .BRESP_o   ( BRESP_int               ),
        .BID_o     ( BID_int                 ),
        .BUSER_o   ( BUSER_int               ),
        .BREADY_i  ( BREADY                  ),

        .CEN       ( CEN                     ),
        .WEN       ( WEN                     ),
        .A         ( A                       ),
        .D         ( D                       ),
        .BE        ( BE                      ),
        .Q         ( Q                       )
    );

 endmodule

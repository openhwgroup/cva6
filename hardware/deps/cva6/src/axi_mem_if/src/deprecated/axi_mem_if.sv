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

`define OKAY   2'b00
`define EXOKAY 2'b01
`define SLVERR 2'b10
`define DECERR 2'b11

module axi_mem_if
#(
    parameter int unsigned AXI4_ADDRESS_WIDTH = 64,
    parameter int unsigned AXI4_RDATA_WIDTH   = 64,
    parameter int unsigned AXI4_WDATA_WIDTH   = 64,
    parameter int unsigned AXI4_ID_WIDTH      = 16,
    parameter int unsigned AXI4_USER_WIDTH    = 10,
    parameter int unsigned AXI_NUMBYTES       = AXI4_WDATA_WIDTH/8,
    parameter int unsigned BUFF_DEPTH_SLAVE   = 4
)
(
    input logic                                     ACLK,
    input logic                                     ARESETn,
    input logic                                     test_en_i,
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
    //AXI write data bus -------------- // USED// --------------
    input  logic [AXI_NUMBYTES-1:0][7:0]            WDATA_i    ,
    input  logic [AXI_NUMBYTES-1:0]                 WSTRB_i    ,
    input  logic                                    WLAST_i    ,
    input  logic [AXI4_USER_WIDTH-1:0]              WUSER_i    ,
    input  logic                                    WVALID_i   ,
    output logic                                    WREADY_o   ,
    //AXI write response bus -------------- // USED// ----------
    output logic   [AXI4_ID_WIDTH-1:0]              BID_o      ,
    output logic   [ 1:0]                           BRESP_o    ,
    output logic                                    BVALID_o   ,
    output logic   [AXI4_USER_WIDTH-1:0]            BUSER_o    ,
    input  logic                                    BREADY_i   ,
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
    output logic  [AXI4_ADDRESS_WIDTH-1:0]          A          ,
    output logic  [AXI4_WDATA_WIDTH-1:0]            D          ,
    output logic  [AXI_NUMBYTES-1:0]                BE         ,
    input  logic  [AXI4_RDATA_WIDTH-1:0]            Q
);

    // for burst reads we need to shift the address of this amount e.g.: for 64 data add 8, for 32 bit data add 4
    localparam ADDRESS_BITS= $clog2(AXI4_WDATA_WIDTH/8);

  // -----------------------------------------------------------
  // AXI TARG Port Declarations --------------------------------
  // -----------------------------------------------------------
  //AXI write address bus --------------------------------------
  logic [AXI4_ID_WIDTH-1:0]                         AWID       ;
  logic [AXI4_ADDRESS_WIDTH-1:0]                    AWADDR     ;
  logic [ 7:0]                                      AWLEN      ;
  logic [ 2:0]                                      AWSIZE     ;
  logic [ 1:0]                                      AWBURST    ;
  logic                                             AWLOCK     ;
  logic [ 3:0]                                      AWCACHE    ;
  logic [ 2:0]                                      AWPROT     ;
  logic [ 3:0]                                      AWREGION   ;
  logic [ AXI4_USER_WIDTH-1:0]                      AWUSER     ;
  logic [ 3:0]                                      AWQOS      ;
  logic                                             AWVALID    ;
  logic                                             AWREADY    ;

  //AXI write data bus ------------------------ ----------------
  logic [AXI_NUMBYTES-1:0][7:0]                     WDATA      ;
  logic [AXI_NUMBYTES-1:0]                          WSTRB      ;
  logic                                             WLAST      ;
  logic [AXI4_USER_WIDTH-1:0]                       WUSER      ;
  logic                                             WVALID     ;
  logic                                             WREADY     ;

  //AXI write response bus -------------------------------------
  logic   [AXI4_ID_WIDTH-1:0]                       BID        ;
  logic   [ 1:0]                                    BRESP      ;
  logic                                             BVALID     ;
  logic   [AXI4_USER_WIDTH-1:0]                     BUSER      ;
  logic                                             BREADY     ;

  //AXI read address bus ---------------------------------------
  logic [AXI4_ID_WIDTH-1:0]                         ARID       ;
  logic [AXI4_ADDRESS_WIDTH-1:0]                    ARADDR     ;
  logic [ 7:0]                                      ARLEN      ;
  logic [ 2:0]                                      ARSIZE     ;
  logic [ 1:0]                                      ARBURST    ;
  logic                                             ARLOCK     ;
  logic [ 3:0]                                      ARCACHE    ;
  logic [ 2:0]                                      ARPROT     ;
  logic [ 3:0]                                      ARREGION   ;
  logic [ AXI4_USER_WIDTH-1:0]                      ARUSER     ;
  logic [ 3:0]                                      ARQOS      ;
  logic                                             ARVALID    ;
  logic                                             ARREADY    ;

  //AXI read data bus ------------------------------------------
  logic [AXI4_ID_WIDTH-1:0]                         RID        ;
  logic [AXI4_RDATA_WIDTH-1:0]                      RDATA      ;
  logic [ 1:0]                                      RRESP      ;
  logic                                             RLAST      ;
  logic [AXI4_USER_WIDTH-1:0]                       RUSER      ;
  logic                                             RVALID     ;
  logic                                             RREADY     ;

  enum logic [3:0] { IDLE,
                     SINGLE_RD, BURST_RD, WRAP_RD,
                     BURST_WR, SINGLE_WR, WRAP_WR,
                     WAIT_WDATA_BURST,
                     WAIT_WDATA_SINGLE,
                     WAIT_WDATA_BURST_WRAP,
                     BURST_RESP
                    } CS , NS;

  logic [8:0]                      CountBurstCS;
  logic [8:0]                      CountBurstNS;

  logic [AXI4_ADDRESS_WIDTH-1:0]   address;
  logic [AXI4_ADDRESS_WIDTH-1:0]   address_q;

  logic                            read_req;
  logic                            sample_AR;
  logic [AXI4_ADDRESS_WIDTH-1:0]   ARADDR_Q;
  logic [7:0]                      ARLEN_Q;
  logic [63:0]                     arlen_fixed_q;

  logic                            decr_ARLEN;
  logic [AXI4_ID_WIDTH-1:0]        ARID_Q;
  logic [ AXI4_USER_WIDTH-1:0]     ARUSER_Q;

  logic                            write_req;
  logic                            sample_AW;
  logic [AXI4_ADDRESS_WIDTH-1:0]   AWADDR_Q;
  logic [7:0]                      AWLEN_Q;
  logic [63:0]                     awlen_fixed_q;

  logic                            decr_AWLEN;
  logic [AXI4_ID_WIDTH-1:0]        AWID_Q;
  logic [ AXI4_USER_WIDTH-1:0]     AWUSER_Q;

  logic                            RR_FLAG;

  logic [2:0]                      ar_size_q;
  logic [2:0]                      aw_size_q;

   // AXI WRITE ADDRESS CHANNEL BUFFER
   axi_aw_buffer #(
       .ID_WIDTH     ( AXI4_ID_WIDTH      ),
       .ADDR_WIDTH   ( AXI4_ADDRESS_WIDTH ),
       .USER_WIDTH   ( AXI4_USER_WIDTH    ),
       .BUFFER_DEPTH ( BUFF_DEPTH_SLAVE   )
   ) slave_aw_buffer_i (
      .clk_i           ( ACLK        ),
      .rst_ni          ( ARESETn     ),
      .test_en_i       ( test_en_i   ),

      .slave_valid_i   ( AWVALID_i   ),
      .slave_addr_i    ( AWADDR_i    ),
      .slave_prot_i    ( AWPROT_i    ),
      .slave_region_i  ( AWREGION_i  ),
      .slave_len_i     ( AWLEN_i     ),
      .slave_size_i    ( AWSIZE_i    ),
      .slave_burst_i   ( AWBURST_i   ),
      .slave_lock_i    ( AWLOCK_i    ),
      .slave_cache_i   ( AWCACHE_i   ),
      .slave_qos_i     ( AWQOS_i     ),
      .slave_id_i      ( AWID_i      ),
      .slave_user_i    ( AWUSER_i    ),
      .slave_ready_o   ( AWREADY_o   ),

      .master_valid_o  ( AWVALID     ),
      .master_addr_o   ( AWADDR      ),
      .master_prot_o   ( AWPROT      ),
      .master_region_o ( AWREGION    ),
      .master_len_o    ( AWLEN       ),
      .master_size_o   ( AWSIZE      ),
      .master_burst_o  ( AWBURST     ),
      .master_lock_o   ( AWLOCK      ),
      .master_cache_o  ( AWCACHE     ),
      .master_qos_o    ( AWQOS       ),
      .master_id_o     ( AWID        ),
      .master_user_o   ( AWUSER      ),
      .master_ready_i  ( AWREADY     )
   );


   // AXI WRITE ADDRESS CHANNEL BUFFER
   axi_ar_buffer #(
       .ID_WIDTH     ( AXI4_ID_WIDTH      ),
       .ADDR_WIDTH   ( AXI4_ADDRESS_WIDTH ),
       .USER_WIDTH   ( AXI4_USER_WIDTH    ),
       .BUFFER_DEPTH ( BUFF_DEPTH_SLAVE   )
   ) slave_ar_buffer_i (
      .clk_i           ( ACLK       ),
      .rst_ni          ( ARESETn    ),
      .test_en_i       ( test_en_i  ),

      .slave_valid_i   ( ARVALID_i  ),
      .slave_addr_i    ( ARADDR_i   ),
      .slave_prot_i    ( ARPROT_i   ),
      .slave_region_i  ( ARREGION_i ),
      .slave_len_i     ( ARLEN_i    ),
      .slave_size_i    ( ARSIZE_i   ),
      .slave_burst_i   ( ARBURST_i  ),
      .slave_lock_i    ( ARLOCK_i   ),
      .slave_cache_i   ( ARCACHE_i  ),
      .slave_qos_i     ( ARQOS_i    ),
      .slave_id_i      ( ARID_i     ),
      .slave_user_i    ( ARUSER_i   ),
      .slave_ready_o   ( ARREADY_o  ),

      .master_valid_o  ( ARVALID    ),
      .master_addr_o   ( ARADDR     ),
      .master_prot_o   ( ARPROT     ),
      .master_region_o ( ARREGION   ),
      .master_len_o    ( ARLEN      ),
      .master_size_o   ( ARSIZE     ),
      .master_burst_o  ( ARBURST    ),
      .master_lock_o   ( ARLOCK     ),
      .master_cache_o  ( ARCACHE    ),
      .master_qos_o    ( ARQOS      ),
      .master_id_o     ( ARID       ),
      .master_user_o   ( ARUSER     ),
      .master_ready_i  ( ARREADY    )
   );

   axi_w_buffer #(
       .DATA_WIDTH(AXI4_WDATA_WIDTH),
       .USER_WIDTH(AXI4_USER_WIDTH),
       .BUFFER_DEPTH(BUFF_DEPTH_SLAVE)
   ) slave_w_buffer_i (
        .clk_i          ( ACLK      ),
        .rst_ni         ( ARESETn   ),
        .test_en_i      ( test_en_i ),

        .slave_valid_i  ( WVALID_i  ),
        .slave_data_i   ( WDATA_i   ),
        .slave_strb_i   ( WSTRB_i   ),
        .slave_user_i   ( WUSER_i   ),
        .slave_last_i   ( WLAST_i   ),
        .slave_ready_o  ( WREADY_o  ),

        .master_valid_o ( WVALID    ),
        .master_data_o  ( WDATA     ),
        .master_strb_o  ( WSTRB     ),
        .master_user_o  ( WUSER     ),
        .master_last_o  ( WLAST     ),
        .master_ready_i ( WREADY    )
    );

   axi_r_buffer #(
        .ID_WIDTH(AXI4_ID_WIDTH),
        .DATA_WIDTH(AXI4_RDATA_WIDTH),
        .USER_WIDTH(AXI4_USER_WIDTH),
        .BUFFER_DEPTH(BUFF_DEPTH_SLAVE)
   ) slave_r_buffer_i (
        .clk_i          ( ACLK       ),
        .rst_ni         ( ARESETn    ),
        .test_en_i      ( test_en_i  ),

        .slave_valid_i  ( RVALID     ),
        .slave_data_i   ( RDATA      ),
        .slave_resp_i   ( RRESP      ),
        .slave_user_i   ( RUSER      ),
        .slave_id_i     ( RID        ),
        .slave_last_i   ( RLAST      ),
        .slave_ready_o  ( RREADY     ),

        .master_valid_o ( RVALID_o   ),
        .master_data_o  ( RDATA_o    ),
        .master_resp_o  ( RRESP_o    ),
        .master_user_o  ( RUSER_o    ),
        .master_id_o    ( RID_o      ),
        .master_last_o  ( RLAST_o    ),
        .master_ready_i ( RREADY_i   )
   );

   axi_b_buffer #(
        .ID_WIDTH(AXI4_ID_WIDTH),
        .USER_WIDTH(AXI4_USER_WIDTH),
        .BUFFER_DEPTH(BUFF_DEPTH_SLAVE)
   ) slave_b_buffer_i (
        .clk_i          ( ACLK      ),
        .rst_ni         ( ARESETn   ),
        .test_en_i      ( test_en_i ),

        .slave_valid_i  ( BVALID    ),
        .slave_resp_i   ( BRESP     ),
        .slave_id_i     ( BID       ),
        .slave_user_i   ( BUSER     ),
        .slave_ready_o  ( BREADY    ),

        .master_valid_o ( BVALID_o  ),
        .master_resp_o  ( BRESP_o   ),
        .master_id_o    ( BID_o     ),
        .master_user_o  ( BUSER_o   ),
        .master_ready_i ( BREADY_i  )
   );

    // Round Robin Flag
    always_ff @(posedge ACLK, negedge ARESETn) begin
        if (ARESETn == 1'b0)
            RR_FLAG <= 1'b0;
        else
            RR_FLAG <= ~RR_FLAG;
    end

    // Single Port Memory interface
    assign BE    = WSTRB;
    assign RDATA = Q;
    assign D     = WDATA;

    assign A   = address;
    assign WEN = (write_req) ? 1'b0 : 1'b1;

    always_comb begin
        CEN = ~(  write_req | read_req);
    end

    always_comb begin
        CountBurstNS   = CountBurstCS;
        AWREADY        = 1'b0;
        WREADY         = 1'b0;
        address        = '0;

        write_req      = 1'b0;
        sample_AW      = 1'b0;
        decr_AWLEN     = 1'b0;

        BID            = '0;
        BRESP          = `OKAY;
        BUSER          = '0;
        BVALID         = 1'b0;

        ARREADY        = 1'b0;
        read_req       = 1'b0;
        sample_AR      = 1'b0;
        decr_ARLEN     = 1'b0;

        RRESP          = `OKAY;
        RUSER          = '0;
        RLAST          = 1'b0;
        RID            = '0;
        // save address
        address        = address_q;
        NS = CS;

        case (CS)
            IDLE: begin
                case (RR_FLAG)
                    1'b0: begin // Priority on Read
                        if (ARVALID == 1'b1) begin
                            sample_AR      = 1'b1;
                            read_req       = 1'b1;
                            address        = ARADDR;
                            ARREADY        = 1'b1;

                            if (ARLEN == 0) begin
                                NS = SINGLE_RD;
                                CountBurstNS   = '0;
                            end else  begin
                                NS           = (ARBURST == 2'b01) ? BURST_RD : WRAP_RD;
                                CountBurstNS = CountBurstCS + 1'b1;
                            end
                        end else begin
                            if (AWVALID) begin
                                AWREADY   = 1'b1;
                                sample_AW = 1'b1;
                                WREADY    = 1'b1;

                                if (WVALID) begin
                                    write_req = 1'b1;
                                    address   =  AWADDR;

                                    decr_AWLEN = 1'b1;

                                    if (AWLEN == 0) begin
                                          NS            = SINGLE_WR;
                                          CountBurstNS  = 0;
                                    end else begin
                                        NS            = (AWBURST == 2'b01) ? BURST_WR : WRAP_WR;
                                        CountBurstNS  = 1;
                                    end
                                end else begin // GOT ADDRESS WRITE, not DATA

                                    write_req  = 1'b0;
                                    address    = '0;

                                    if (AWLEN == 0) begin
                                        NS           =  WAIT_WDATA_SINGLE;
                                        CountBurstNS = 0;
                                    end else begin
                                        NS           =  (AWBURST == 2'b01) ? WAIT_WDATA_BURST : WAIT_WDATA_BURST_WRAP;
                                        CountBurstNS = 0;
                                    end
                                end
                            end else begin// No requests
                                NS = IDLE;
                            end
                        end
                    end

                    1'b1: begin
                        if (AWVALID) begin
                            AWREADY         = 1'b1;
                            sample_AW       = 1'b1;
                            WREADY          = 1'b1;

                            if (WVALID) begin
                                write_req       = 1'b1;
                                address         =  AWADDR;
                                decr_AWLEN      = 1'b1;

                                if (AWLEN == 0) begin
                                    NS              = SINGLE_WR;
                                    CountBurstNS    = 0;
                                end else begin
                                    NS              = (AWBURST == 2'b01) ? BURST_WR : WRAP_WR;
                                    CountBurstNS    = 1;
                                end
                            end else begin // GOT ADDRESS WRITE, not DATA
                                write_req  = 1'b0;
                                address    = '0;

                                if (AWLEN == 0) begin
                                    NS           =  WAIT_WDATA_SINGLE;
                                    CountBurstNS = 0;
                                end else begin
                                    NS           =  (AWBURST == 2'b01) ? WAIT_WDATA_BURST : WAIT_WDATA_BURST_WRAP;
                                    CountBurstNS = 0;
                                end
                            end
                        end else if (ARVALID) begin
                            sample_AR      = 1'b1;
                            read_req       = 1'b1;
                            address        = ARADDR;
                            ARREADY        = 1'b1;

                            if (ARLEN == 0) begin
                                NS = SINGLE_RD;
                                CountBurstNS   = '0;
                            end else begin
                                NS             = (ARBURST == 2'b01) ? BURST_RD : WRAP_RD;
                                CountBurstNS   = CountBurstCS + 1'b1;
                            end
                        end else begin
                            NS = IDLE;
                        end
                    end
                endcase
            end

            SINGLE_RD: begin
                RRESP  = `OKAY;
                RID    = ARID_Q;
                RUSER  = ARUSER_Q;
                RLAST  = 1'b1;
                // we have a valid response here, waiting to be delivered
                if (RREADY) begin
                    NS             = IDLE;
                    CountBurstNS   = '0;
                end else begin// NOt ready: stay here untile RR RADY is OK
                    NS             = SINGLE_RD;
                    read_req       = 1'b1;
                    address        = ARADDR_Q;
                    CountBurstNS   = '0;
                end
            end

            BURST_RD, WRAP_RD:  begin
                automatic logic [AXI4_ADDRESS_WIDTH-1:0] aligned_address = ARADDR_Q & ~{{{AXI4_ADDRESS_WIDTH - 3}{1'b0}}, ar_size_q};
                automatic logic [AXI4_ADDRESS_WIDTH-1:0] wrap_boundary = aligned_address + (1 << ar_size_q) * (arlen_fixed_q + 1);
                automatic logic [AXI4_ADDRESS_WIDTH-1:0] addr = ARADDR_Q + (CountBurstCS << ADDRESS_BITS);

                RRESP   = `OKAY;
                RID     = ARID_Q;
                RUSER   = ARUSER_Q;
                ARREADY = 1'b0;

                if (RREADY) begin
                    if (ARLEN_Q > 0) begin
                        read_req      = 1'b1; // read the previous address

                        decr_ARLEN    = 1'b1;
                        CountBurstNS  = CountBurstCS + 1'b1;

                        address = addr;

                        if (CS == WRAP_RD) begin
                            // if we reach wrapping boundary reset counter
                            if (addr == wrap_boundary)
                                CountBurstNS = 0;
                        end
                        RLAST         = 1'b0;
                    end else begin // BURST_LAST
                        RLAST         = 1'b1;
                        NS            = IDLE;
                        CountBurstNS  = '0;
                    end
                end else begin // not Ready
                    read_req     = 1'b1; // read the previous address
                    decr_ARLEN   = 1'b0;
                    ARREADY      = 1'b0;
                    address      = address_q;
                end
            end

            SINGLE_WR: begin
                BID          = AWID_Q;
                BRESP        = `OKAY;
                BUSER        = AWUSER_Q;
                BVALID       = 1'b1;
                AWREADY      = 1'b0;
                CountBurstNS = '0;

                if (BREADY)  begin
                    NS = IDLE;
                end else begin
                    NS = SINGLE_WR;
                end
            end

            BURST_WR, WRAP_WR: begin

                automatic logic [AXI4_ADDRESS_WIDTH-1:0] aligned_address = AWADDR_Q & ~{{{AXI4_ADDRESS_WIDTH - 3}{1'b0}}, aw_size_q};
                automatic logic [AXI4_ADDRESS_WIDTH-1:0] wrap_boundary = aligned_address + (1 << aw_size_q) * (awlen_fixed_q + 1);
                automatic logic [AXI4_ADDRESS_WIDTH-1:0] addr = AWADDR_Q + (CountBurstCS << ADDRESS_BITS);

                WREADY   = 1'b1;
                AWREADY  = 1'b0;
                address = addr;

                if (CS == WRAP_WR) begin
                    // if we reach wrapping boundary reset counter
                    if (addr == wrap_boundary)
                        CountBurstNS = 0;
                end

                if (WVALID) begin
                    write_req = 1'b1; // read the previous address

                      if (AWLEN_Q > 0) begin
                          decr_AWLEN   = 1'b1;
                          CountBurstNS = CountBurstCS + 1'b1;
                      end else begin
                          decr_AWLEN   = 1'b0;
                          NS           = BURST_RESP;
                    end
                end else begin
                    write_req  = 1'b0; // read the previous address
                    decr_AWLEN = 1'b0;
                end
            end

            BURST_RESP: begin
                BVALID       = 1'b1;
                BID          = AWID_Q;
                BRESP        = `OKAY;
                BUSER        = AWUSER_Q;
                AWREADY      = 1'b0;
                CountBurstNS = '0;

                if (BREADY) begin
                    NS = IDLE;
                end else begin // ~BREADY
                    NS = BURST_RESP;
                end
            end

            WAIT_WDATA_BURST, WAIT_WDATA_BURST_WRAP: begin
                AWREADY  = 1'b0;
                WREADY   = 1'b1;
                address  =  AWADDR_Q;

                if (WVALID) begin
                    write_req    = 1'b1;
                    NS           = (CS == WAIT_WDATA_BURST) ? BURST_WR : WRAP_WR;
                    CountBurstNS = 1;
                    decr_AWLEN   = 1'b1;
                end else begin
                    write_req    = 1'b0;
                    CountBurstNS = '0;
                end
            end

            WAIT_WDATA_SINGLE: begin
                AWREADY          = 1'b0;
                WREADY           = 1'b1;
                CountBurstNS     = '0;
                decr_AWLEN       =  1'b0;
                address          =  AWADDR_Q;

                if (WVALID) begin
                    write_req        =  1'b1;
                    NS               =  BURST_RESP;
                end else begin
                    NS = WAIT_WDATA_SINGLE; // wait for data
                end
            end

            default:
              NS = CS;
        endcase
    end

    // Registers
    always_ff @(posedge ACLK, negedge ARESETn) begin
        if (ARESETn == 1'b0) begin
            CS           <= IDLE;
            CountBurstCS <= '0;

            //Read Channel
            ARLEN_Q       <= '0;
            ARADDR_Q      <= '0;
            ARID_Q        <= '0;
            ARUSER_Q      <= '0;
            ar_size_q     <= '0;
            RVALID        <= 1'b0;

            //Write Channel
            AWADDR_Q      <= '0;
            AWID_Q        <= '0;
            AWUSER_Q      <= '0;
            AWLEN_Q       <= '0;
            arlen_fixed_q <= '0;
            awlen_fixed_q <= '0;
            aw_size_q     <= '0;
            address_q     <= '0;
        end else begin
            CS           <= NS;
            address_q    <= address;
            CountBurstCS <= CountBurstNS;
            RVALID       <= read_req;
            if (sample_AR) begin
                ARLEN_Q            <=  ARLEN;
                ARID_Q             <=  ARID;
                ARADDR_Q           <=  ARADDR;
                ARUSER_Q           <=  ARUSER;
                arlen_fixed_q      <=  ARLEN;
                ar_size_q          <=  ARSIZE;
            end else begin
                if (decr_ARLEN)
                  ARLEN_Q  <=  ARLEN_Q - 1'b1;
            end

            if (sample_AW) begin
                AWADDR_Q  <=  AWADDR;
                AWID_Q    <=  AWID;
                AWUSER_Q  <=  AWUSER;
                aw_size_q <= AWSIZE;
                awlen_fixed_q <= AWLEN;
            end

            case({sample_AW,decr_AWLEN})
              2'b00: AWLEN_Q  <=  AWLEN_Q;
              2'b01: AWLEN_Q  <=  AWLEN_Q - 1'b1;
              2'b10: AWLEN_Q  <=  AWLEN;
              2'b11: AWLEN_Q  <=  AWLEN   - 1'b1;
            endcase
          end
        end
endmodule

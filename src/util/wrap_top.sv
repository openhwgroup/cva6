// Copyright 2015 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the “License”); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an “AS IS” BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

`default_nettype none

module wrap_top
(
   // UART
   input wire             rxd,
   output wire            txd,
   output wire            rts,
   input wire             cts,
   // 4-bit full SD interface
   output wire            sd_sclk,
   input wire             sd_detect,
   inout wire [3:0]  sd_dat,
   inout wire        sd_cmd,
   output wire            sd_reset,

   // LED and DIP switch
   output wire [7:0]      o_led,
   input wire [15:0]      i_dip,

   // push button array
   input wire             GPIO_SW_C,
   input wire             GPIO_SW_W,
   input wire             GPIO_SW_E,
   input wire             GPIO_SW_N,
   input wire             GPIO_SW_S,

   //keyboard
   inout wire        PS2_CLK,
   inout wire        PS2_DATA,

  // display
   output wire            VGA_HS_O,
   output wire            VGA_VS_O,
   output wire [3:0]      VGA_RED_O,
   output wire [3:0]      VGA_BLUE_O,
   output wire [3:0]      VGA_GREEN_O,

   // Ethernet PHY
   input wire [1:0]  i_erxd, // RMII receive data
   input wire        i_erx_dv, // PHY data valid
   input wire        i_erx_er, // PHY coding error
   input wire        i_emdint, // PHY interrupt in active low
   output reg        o_erefclk, // RMII clock out
   output reg [1:0]  o_etxd, // RMII transmit data
   output reg        o_etx_en, // RMII transmit enable
   output wire       o_emdc, // MDIO clock
   inout wire        io_emdio, // MDIO inout
   output wire       o_erstn, // PHY reset active low

    // 7-segment display
   output wire       CA,
   output wire       CB,
   output wire       CC,
   output wire       CD,
   output wire       CE,
   output wire       CF,
   output wire       CG,
   output wire       DP,
   output wire [7:0] AN,
  
   // JTAG signals
   input  logic        tck_i,
   input  logic        trstn_i,
   input  logic        tms_i,
   input  logic        tdi_i,
   output logic        tdo_o,

   // clock and reset
   input wire             clk_p,
   input wire             clk_n,
   input wire             rst_top
   );

   logic             clk_i, locked;          
   logic             test_en_i = 'b1; // enable all clock gates for testing
   // Core ID; Cluster ID and boot address are considered more or less static
   logic [ 3:0]      core_id_i = 'b0;
   logic [ 5:0]      cluster_id_i = 'b0;
   logic             flush_req_i = 'b0;
   logic             flushing_o;
   // Interrupt s
   logic [1:0]       irq_i = 'b0; // level sensitive IR lines; mip & sip
   logic             ipi_i = 'b0; // inter-processor interrupts
   logic             sec_lvl_o; // current privilege level oot
   // Timer facilities
   logic [63:0]      time_i = 'b0; // global time (most probably coming from an RTC)
   logic             time_irq_i = 'b0; // timer interrupt in

 // address on which to decide whether the request is cache-able or not
   parameter int                        unsigned AXI_ID_WIDTH      = 4;
   parameter int                        unsigned AXI_USER_WIDTH    = 1;
   parameter int                        unsigned AXI_ADDRESS_WIDTH = 32;
   parameter int                        unsigned AXI_DATA_WIDTH    = 64;
   
   genvar        i;

   // internal clock and reset signals
   logic  rst, rst_ni;
   assign rst = !rst_ni;

   // Debug controlled reset of the Rocket system
   logic  sys_rst, cpu_rst;

   // interrupt line
   logic [63:0]                interrupt;

   wire io_emdio_i, phy_emdio_o, phy_emdio_t, clk_rmii, clk_rmii_quad, clk_locked_wiz;
   reg phy_emdio_i, io_emdio_o, io_emdio_t;

   //clock generator
   logic mig_sys_clk, clk_pixel;
   logic clk_io_uart; // UART IO clock for debug

   clk_wiz_ariane clk_gen
     (
      .clk_in1       ( clk_p          ), // 100 MHz onboard
      .clk_out1      ( mig_sys_clk    ), // 200 MHz
      .clk_io_uart   ( clk_io_uart    ), // 60 MHz
      .clk_rmii      ( clk_rmii       ), // 50 MHz rmii
      .clk_rmii_quad ( clk_rmii_quad  ), // 50 MHz rmii quad
      .clk_pixel     ( clk_pixel      ), // 120 MHz
      .clk_i         ( clk_i          ), // 25 MHz (only if DDR not used)
      .resetn        ( rst_top        ),
      .locked        ( clk_locked_wiz )
      );
   
   assign rst_ni = clk_locked_wiz & rst_top;
   /////////////////////////////////////////////////////////////
   // HID

   logic                       hid_irq, sd_irq, eth_irq;

   wire                        hid_en;
   wire [7:0]                  hid_we;
   wire [17:0]                 hid_addr;
   wire [63:0]                 hid_wrdata,  hid_rddata;
   
   logic [1:0] eth_txd;
   logic eth_rstn, eth_refclk, eth_txen;
   assign o_erstn = eth_rstn & clk_locked_wiz;
    
   always @(posedge clk_rmii)
     begin
        phy_emdio_i <= io_emdio_i;
        io_emdio_o <= phy_emdio_o;
        io_emdio_t <= phy_emdio_t;
     end

   IOBUF #(
      .DRIVE(12), // Specify the output drive strength
      .IBUF_LOW_PWR("TRUE"),  // Low Power - "TRUE", High Performance = "FALSE" 
      .IOSTANDARD("DEFAULT"), // Specify the I/O standard
      .SLEW("SLOW") // Specify the output slew rate
   ) IOBUF_inst (
      .O(io_emdio_i),     // Buffer output
      .IO(io_emdio),   // Buffer inout port (connect directly to top-level port)
      .I(io_emdio_o),     // Buffer input
      .T(io_emdio_t)      // 3-state enable input, high=input, low=output
   );

  ODDR #(
    .DDR_CLK_EDGE("OPPOSITE_EDGE"),
    .INIT(1'b0),
    .IS_C_INVERTED(1'b0),
    .IS_D1_INVERTED(1'b0),
    .IS_D2_INVERTED(1'b0),
    .SRTYPE("SYNC")) 
    refclk_inst
       (.C(eth_refclk),
        .CE(1'b1),
        .D1(1'b1),
        .D2(1'b0),
        .Q(o_erefclk),
        .R(1'b0),
        .S( ));
    
    always @(posedge clk_rmii_quad)
        begin
        o_etxd = eth_txd;
        o_etx_en = eth_txen;
        end

   periph_soc psoc
     (
      .msoc_clk   ( clk_i           ),
      .sd_sclk    ( sd_sclk         ),
      .sd_detect  ( sd_detect       ),
      .sd_dat     ( sd_dat          ),
      .sd_cmd     ( sd_cmd          ),
      .sd_irq     ( sd_irq          ),
      .from_dip   ( i_dip           ),
      .to_led     ( o_led           ),
      .rstn       ( rst_ni          ),
      .clk_200MHz ( mig_sys_clk     ),
      .pxl_clk    ( clk_pixel       ),
      .uart_rx    ( rxd             ),
      .uart_tx    ( txd             ),
      .clk_rmii   ( clk_rmii        ),
      .locked     ( clk_locked_wiz  ),
    // SMSC ethernet PHY connections
      .eth_rstn   ( eth_rstn        ),
      .eth_crsdv  ( i_erx_dv        ),
      .eth_refclk ( eth_refclk      ),
      .eth_txd    ( eth_txd         ),
      .eth_txen   ( eth_txen        ),
      .eth_rxd    ( i_erxd          ),
      .eth_rxerr  ( i_erx_er        ),
      .eth_mdc    ( o_emdc          ),
      .phy_mdio_i ( phy_emdio_i     ),
      .phy_mdio_o ( phy_emdio_o     ),
      .phy_mdio_t ( phy_emdio_t     ),
      .eth_irq    ( eth_irq         ),
      .*
      );

    localparam int unsigned AXI_NUMBYTES = AXI_DATA_WIDTH/8;

    logic        flush_dcache_ack, flush_dcache, aresetn;
    logic        flush_dcache_q;
    logic [31:0] dbg_mstaddress;
    
    AXI_BUS #(
              .AXI_ADDR_WIDTH ( AXI_ADDRESS_WIDTH ),
              .AXI_DATA_WIDTH ( AXI_DATA_WIDTH    ),
              .AXI_ID_WIDTH   ( AXI_ID_WIDTH      ),
              .AXI_USER_WIDTH ( AXI_USER_WIDTH    )
    ) master0_if(), master1_if(), master2_if(), input_if(), output_if();
  
display_top display(.clk    (clk_i),
                 .rst       (!rst_ni),
                 .bcd_digits(dbg_mstaddress),
                 .CA        (CA),
                 .CB        (CB),
                 .CC        (CC),
                 .CD        (CD),
                 .CE        (CE),
                 .CF        (CF),
                 .CG        (CG),
                 .DP        (DP),
                 .AN        (AN),
                 .redled    ());

    assign flush_dcache = flush_dcache_q;
    assign flushing_o = flush_dcache_q;
    
    // direct store interface
    always_ff @(posedge clk_i or negedge rst_ni) begin

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

    logic        master0_req,     master1_req,     master2_req;
    logic [63:0] master0_address, master1_address, master2_address;
    logic [7:0]  master0_we,      master1_we,      master2_we;
    logic [63:0] master0_wdata,   master1_wdata,   master2_wdata;
    logic [63:0] master0_rdata,   master1_rdata,   master2_rdata;

        // Debug Interface
         logic                           debug_gnt_o;
         logic                           debug_halt_i;
         logic                           debug_resume_i;
         logic                           debug_rvalid_o;
         wire  [15:0]                    debug_addr_i;
         logic                           debug_we_i;
         logic [63:0]                    debug_wdata_i;
         logic [63:0]                    debug_rdata_o;
         logic                           debug_halted_o;
         logic                           debug_req_i;
         
        // CPU Control Signals
         wire         fetch_enable_i = 1'b1;

   crossbar_socip_test cross1(
      .slave0_if  ( input_if   ),
      .slave1_if  ( output_if  ),
      .master0_if ( master0_if ),
      .master1_if ( master1_if ),
      .master2_if ( master2_if ),
      .clk_i      ( clk_i      ),
      .rst_ni     ( rst_ni     ));

   dbg_wrap #(
      .JTAG_CHAIN_START     ( 1                 ),
      .AXI_ID_MASTER_WIDTH  ( AXI_ID_WIDTH      ),
      .AXI_ID_SLAVE_WIDTH   ( AXI_ID_WIDTH      ),
      .AXI_ADDR_WIDTH       ( AXI_ADDRESS_WIDTH ),
      .AXI_DATA_WIDTH       ( AXI_DATA_WIDTH    ),
      .AXI_USER_WIDTH       ( AXI_USER_WIDTH    )
    ) i_dbg0 (
        .clk        ( clk_i          ),
        .rst_n      ( rst_ni         ),
        .testmode_i ( 1'b0           ),
        .input_if   ( input_if       ),
        .output_if  ( output_if      ),
         // CPU signals
        .aresetn      ( aresetn        ),
        .cpu_addr_o   ( debug_addr_i   ), 
        .cpu_rdata_i  ( debug_rdata_o  ),
        .cpu_wdata_o  ( debug_wdata_i  ),
        .cpu_halted_i ( debug_halted_o ),
        .cpu_halt_o   ( debug_halt_i   ),
        .cpu_resume_o ( debug_resume_i ),
        .cpu_req_o    ( debug_req_i    ),
        .cpu_we_o     ( debug_we_i     ),
        .cpu_rvalid_i ( debug_rvalid_o ),
        .cpu_gnt_i    ( debug_gnt_o    ),
        .cpu_fetch_o  ( fetch_enable_i ),
        // Boot memory at location 'h40000000
        .boot_en(master1_req),      // input wire ena
        .boot_we(master1_we),   // input wire [7 : 0] wea
        .boot_addr(master1_address[15:0]),  // input wire [13: 0] addra
        .boot_wdata(master1_wdata),  // input wire [63 : 0] dina
        .boot_rdata(master1_rdata),  // output wire [63 : 0] douta
        // JTAG shared memory at location 'h42000000
        .wrap_en(master2_req),      // input wire ena
        .wrap_we(master2_we),   // input wire [7 : 0] wea
        .wrap_addr(master2_address[13:0]),  // input wire [13: 0] addra
        .wrap_wdata(master2_wdata),  // input wire [63 : 0] dina
        .wrap_rdata(master2_rdata),  // output wire [63 : 0] douta
        .address    ( dbg_mstaddress ),
        .i_dip      ( i_dip          ),
        .tms_i      ( 1'b0           ),
        .tck_i      ( 1'b0           ),
        .trstn_i    ( 1'b1           ),
        .tdi_i      ( 1'b0           ),
        .tdo_o      (                )
             );
                          
axi_ram_wrap  #(
        .AXI_ID_WIDTH   ( AXI_ID_WIDTH      ),
        .AXI_ADDR_WIDTH ( AXI_ADDRESS_WIDTH ),
        .AXI_DATA_WIDTH ( AXI_DATA_WIDTH    ),
        .AXI_USER_WIDTH ( AXI_USER_WIDTH    ),
        .MEM_ADDR_WIDTH ( 20                )
    ) i_master0 (
        .clk_i  ( clk_i           ),
        .rst_ni ( rst_ni          ),
        .slave  ( master0_if      ),
        .bram_en_a  ( master0_req     ),
        .bram_addr_a ( master0_address ),
        .bram_we_a   ( master0_we      ),
        .bram_wrdata_a ( master0_wdata   ),
        .bram_rddata_a ( master0_rdata   ),
        .bram_clk_a ( ),
        .bram_rst_a ( )
    ), i_master1 (
        .clk_i  ( clk_i           ),
        .rst_ni ( rst_ni          ),
        .slave  ( master1_if      ),
        .bram_en_a  ( master1_req     ),
        .bram_addr_a ( master1_address ),
        .bram_we_a   ( master1_we      ),
        .bram_wrdata_a ( master1_wdata   ),
        .bram_rddata_a ( master1_rdata   ),
        .bram_clk_a ( ),
        .bram_rst_a ( )
    ), i_master2 (
                .clk_i  ( clk_i           ),
                .rst_ni ( rst_ni          ),
                .slave  ( master2_if      ),
                .bram_en_a  ( master2_req     ),
                .bram_addr_a ( master2_address ),
                .bram_we_a   ( master2_we      ),
                .bram_wrdata_a ( master2_wdata   ),
                .bram_rddata_a ( master2_rdata   ),
                .bram_clk_a ( ),
                .bram_rst_a ( )
            );

   assign hid_we = master0_we;
   assign hid_wrdata = master0_wdata;
   assign master0_rdata = hid_rddata;
   assign hid_addr = master0_address[17:0];
   assign hid_en = master0_req;

endmodule

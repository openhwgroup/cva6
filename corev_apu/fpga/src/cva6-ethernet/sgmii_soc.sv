// sgmii_soc.sv — SGMII Ethernet adapter for VC707
//
// Drop-in replacement for rgmii_soc: same AXI-stream + FCS interface
// to framing_top, but uses Xilinx gig_ethernet_pcs_pma IP for SGMII.
//
// Clock domains:
//   clk_int (free-running)   — independent clock for PCS/PMA IP
//   userclk2 (125 MHz)       — from Xilinx PCS/PMA IP, runs the MAC
//   eth_clk  (= userclk2)    — exposed to framing_top as its clk_int
//
// The Xilinx IP handles GTX transceiver, 8b/10b, PCS, and SGMII autoneg.
// Forencich eth_mac_1g converts GMII <-> AXI-stream with FCS.

`default_nettype none

module sgmii_soc (
    // Free-running clock for PCS/PMA IP
    input wire          clk_int,
    input wire          rst_int,

    // 125 MHz MAC clock output (connect to framing_top clk_int)
    output wire         eth_clk,

    // SGMII serial pins
    input wire          sgmii_rxp,
    input wire          sgmii_rxn,
    output wire         sgmii_txp,
    output wire         sgmii_txn,

    // SGMII 125 MHz reference clock (differential)
    input wire          sgmii_refclk_p,
    input wire          sgmii_refclk_n,

    // PHY reset (active-low to 88E1111)
    output wire         phy_reset_n,

    output wire         mac_gmii_tx_en,

    // AXI-stream TX input (from framing_top, eth_clk domain)
    input wire          tx_axis_tvalid,
    input wire          tx_axis_tlast,
    input wire [7:0]    tx_axis_tdata,
    output wire         tx_axis_tready,
    input wire          tx_axis_tuser,

    // AXI-stream RX output (to framing_top, eth_clk domain)
    output wire         rx_clk,
    output wire [7:0]   rx_axis_tdata,
    output wire         rx_axis_tvalid,
    output wire         rx_axis_tlast,
    output wire         rx_axis_tuser,

    // FCS registers (for framing_top status readback)
    output wire [31:0]  rx_fcs_reg,
    output wire [31:0]  tx_fcs_reg,

    // PCS/PMA status (for debug)
    output wire [15:0]  pcspma_status
);

    // ================================================================
    //  Xilinx gig_ethernet_pcs_pma IP
    // ================================================================
    wire        userclk2;
    wire        resetdone;
    wire        mmcm_locked;
    wire        sgmii_clk_en;

    wire [7:0]  gmii_rxd;
    wire        gmii_rx_dv;
    wire        gmii_rx_er;
    wire [7:0]  gmii_txd;
    wire        gmii_tx_en;
    wire        gmii_tx_er;

    wire [15:0] status_vector;
    wire [1:0]  pcspma_speed = status_vector[11:10];

    // Autoneg advertisement: link=1, ack=1, full-duplex, 1G, SGMII
    wire [15:0] an_adv_config_vector;
    assign an_adv_config_vector[15]    = 1'b1;    // link status
    assign an_adv_config_vector[14]    = 1'b1;    // acknowledge
    assign an_adv_config_vector[13:12] = 2'b01;   // full duplex
    assign an_adv_config_vector[11:10] = 2'b10;   // 1000 Mbps
    assign an_adv_config_vector[9:0]   = 10'b0000000001; // SGMII

    gig_ethernet_pcs_pma_0 i_pcs_pma (
        .gtrefclk_p             (sgmii_refclk_p),
        .gtrefclk_n             (sgmii_refclk_n),
        .gtrefclk_out           (),
        .gtrefclk_bufg_out      (),
        .txp                    (sgmii_txp),
        .txn                    (sgmii_txn),
        .rxp                    (sgmii_rxp),
        .rxn                    (sgmii_rxn),
        .resetdone              (resetdone),
        .userclk_out            (),
        .userclk2_out           (userclk2),
        .rxuserclk_out          (),
        .rxuserclk2_out         (),
        .independent_clock_bufg (clk_int),
        .pma_reset_out          (),
        .mmcm_locked_out        (mmcm_locked),
        .sgmii_clk_r            (),
        .sgmii_clk_f            (),
        .sgmii_clk_en           (sgmii_clk_en),
        .gmii_txd               (gmii_txd),
        .gmii_tx_en             (gmii_tx_en),
        .gmii_tx_er             (gmii_tx_er),
        .gmii_rxd               (gmii_rxd),
        .gmii_rx_dv             (gmii_rx_dv),
        .gmii_rx_er             (gmii_rx_er),
        .gmii_isolate           (),
        .configuration_vector   (5'b10000),         // [4]=AN enable
        .an_interrupt           (),
        .an_adv_config_vector   (an_adv_config_vector),
        .an_restart_config      (1'b0),
        .speed_is_10_100        (pcspma_speed != 2'b10),
        .speed_is_100           (pcspma_speed == 2'b01),
        .status_vector          (status_vector),
        .reset                  (rst_int),
        .signal_detect          (1'b1),
        .gt0_qplloutclk_out     (),
        .gt0_qplloutrefclk_out  ()
    );

    // ================================================================
    //  GMII-side reset synchronizer (in userclk2 domain)
    // ================================================================
    logic [3:0] gmii_rst_sync;
    logic       mac_rst;

    always_ff @(posedge userclk2 or negedge mmcm_locked) begin
        if (!mmcm_locked)
            gmii_rst_sync <= 4'hF;
        else
            gmii_rst_sync <= {gmii_rst_sync[2:0], ~resetdone};
    end
    assign mac_rst = gmii_rst_sync[3];

    // ================================================================
    //  Forencich eth_mac_1g — GMII <-> AXI-stream with FCS
    // ================================================================
    eth_mac_1g #(
        .ENABLE_PADDING     (1),
        .MIN_FRAME_LENGTH   (64)
    ) i_mac (
        .rx_clk             (userclk2),
        .rx_rst             (mac_rst),
        .tx_clk             (userclk2),
        .tx_rst             (mac_rst),
        .tx_axis_tdata      (tx_axis_tdata),
        .tx_axis_tvalid     (tx_axis_tvalid),
        .tx_axis_tready     (tx_axis_tready),
        .tx_axis_tlast      (tx_axis_tlast),
        .tx_axis_tuser      (tx_axis_tuser),
        .rx_axis_tdata      (rx_axis_tdata),
        .rx_axis_tvalid     (rx_axis_tvalid),
        .rx_axis_tlast      (rx_axis_tlast),
        .rx_axis_tuser      (rx_axis_tuser),
        .gmii_rxd           (gmii_rxd),
        .gmii_rx_dv         (gmii_rx_dv),
        .gmii_rx_er         (gmii_rx_er),
        .gmii_txd           (gmii_txd),
        .gmii_tx_en         (gmii_tx_en),
        .gmii_tx_er         (gmii_tx_er),
        .rx_clk_enable      (sgmii_clk_en),
        .tx_clk_enable      (sgmii_clk_en),
        .rx_mii_select      (1'b0),
        .tx_mii_select      (1'b0),
        .rx_error_bad_frame (),
        .rx_error_bad_fcs   (),
        .rx_fcs_reg         (rx_fcs_reg),
        .tx_fcs_reg         (tx_fcs_reg),
        .ifg_delay          (8'd12)
    );

    // ================================================================
    //  Output assignments
    // ================================================================
    assign phy_reset_n    = ~rst_int;
    assign mac_gmii_tx_en = gmii_tx_en;
    assign rx_clk         = userclk2;
    assign eth_clk        = userclk2;
    assign pcspma_status  = status_vector;

endmodule

`default_nettype wire

// Copyright (c) 2015-2018 Princeton University
// All rights reserved.
//
// Redistribution and use in source and binary forms, with or without
// modification, are permitted provided that the following conditions are met:
//     * Redistributions of source code must retain the above copyright
//       notice, this list of conditions and the following disclaimer.
//     * Redistributions in binary form must reproduce the above copyright
//       notice, this list of conditions and the following disclaimer in the
//       documentation and/or other materials provided with the distribution.
//     * Neither the name of Princeton University nor the
//       names of its contributors may be used to endorse or promote products
//       derived from this software without specific prior written permission.
//
// THIS SOFTWARE IS PROVIDED BY PRINCETON UNIVERSITY "AS IS" AND
// ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
// WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
// DISCLAIMED. IN NO EVENT SHALL PRINCETON UNIVERSITY BE LIABLE FOR ANY
// DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
// (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
// LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
// ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
// (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
// SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

// Simplified RGMII <-> MII converter (boldly copied from OpenPiton)
// Specific to 7-series FPGA
module rgmii_to_mii_conv_xilinx (
    // to PHY (RGMII)
    output logic        rgmii_phy_txc,
    output logic        rgmii_phy_txctl,
    output logic [3:0]  rgmii_phy_txd,
    input  logic        rgmii_phy_rxc,
    input  logic        rgmii_phy_rxctl,
    input  logic [3:0]  rgmii_phy_rxd,
    output logic        rgmii_phy_rst_n,
    inout  wire         rgmii_phy_mdio,
    output logic        rgmii_phy_mdc,
    // from MAC (MII)
    input  logic        mem_clk_i, // 200 MHz
    input  logic        net_phy_rst_n,
    input  logic        net_phy_tx_clk, // 25 MHz
    input  logic        net_phy_tx_en,
    input  logic [3:0]  net_phy_tx_data,
    output logic        net_phy_rx_clk,
    output logic        net_phy_dv,
    output logic [3:0]  net_phy_rx_data,
    output logic        net_phy_rx_er,

    input  logic        net_mdio_i,
    output logic        net_mdio_o,
    input  logic        net_mdio_t,
    input  logic        net_phy_mdc
);

    // -------------
    // MDIO
    // -------------
    IOBUF mdio_io_iobuf (.I (net_mdio_i), .IO(rgmii_phy_mdio), .O (net_mdio_o), .T (net_mdio_t));
    assign rgmii_phy_mdc = net_phy_mdc;
    assign rgmii_phy_rst_n = net_phy_rst_n;

    // -------------
    // TX
    // -------------
    // net_phy_tx_clk:  ___|------|______|------|______|------|______|
    // rgmii_phy_txc:   ---|______|------|______|------|______|------|
    // net_phy_tx_en:   -----_________________________________________
    // rgmii_phy_txctl: _____--------------___________________________

    // basically inverts the clock
    ODDR net_phy_txc_oddr (
        .C  ( net_phy_tx_clk    ), // 1-bit clock input (The CLK pin represents the clock input pin)
        .CE ( 1'b1              ), // 1-bit clock enable input (CE represents the clock enable pin. When asserted Low,
        .Q  ( rgmii_phy_txc     ), // 1-bit DDR output (ODDR register output)
                                   // this port disables the output clock on port Q.)
        .D1 ( 1'b0              ), // 1-bit data input (positive edge) (ODDR register inputs)
        .D2 ( 1'b1              ), // 1-bit data input (negative edge) (ODDR register inputs)
        // Synchronous/Asynchronous set/reset pin. Set/Reset is
        // asserted High.
        .R  ( 1'b0              ), // 1-bit reset
        .S  ( 1'b0              )  // 1-bit set
    );

    // D-FF
    FD net_phy_txctl_dff (
        .C ( net_phy_tx_clk  ),
        .D ( net_phy_tx_en   ),
        .Q ( rgmii_phy_txctl )
    );

    for (genvar i = 0; i < 4; i++) begin : gen_net_phy_txd
        FD net_phy_txd_dff (
            .C ( net_phy_tx_clk     ),
            .D ( net_phy_tx_data[i] ),
            .Q ( rgmii_phy_txd[i]   )
        );
    end

    // -------------
    // RX
    // -------------
    logic net_phy_rxc_ibufg_out;
    logic net_phy_rxc_delayed;

    logic net_phy_rx_dv_f;
    logic net_phy_rx_err_f;
    logic net_phy_rx_dv_ff;
    logic net_phy_rx_err_ff;
    logic [3:0] net_phy_rxd_f;
    logic [3:0] net_phy_rxd_ff;

    IBUFG net_phy_rxc_ibufg (
        .I ( rgmii_phy_rxc         ),
        .O ( net_phy_rxc_ibufg_out )
    );

    // Delay by RXC 31*78 (IDELAY_VALUE*tap_delay@200MHz) to put in RXD/RXCTL eye
    (* IODELAY_GROUP = "NET_PHY_RXC" *)
    IDELAYE2 #(
        .CINVCTRL_SEL          ( "FALSE"   ), // Enable dynamic clock inversion (FALSE, TRUE)
        .DELAY_SRC             ( "IDATAIN" ), // Delay input (IDATAIN, DATAIN)
        .HIGH_PERFORMANCE_MODE ( "FALSE"   ), // Reduced jitter ("TRUE"), Reduced power ("FALSE")
        .IDELAY_TYPE           ( "FIXED"   ), // FIXED, VARIABLE, VAR_LOAD, VAR_LOAD_PIPE
        .IDELAY_VALUE          ( 31        ), // Input delay tap setting (0-31)
        .PIPE_SEL              ( "FALSE"   ), // Select pipelined mode, FALSE, TRUE
        .REFCLK_FREQUENCY      ( 200.0     ), // IDELAYCTRL clock input frequency in MHz (190.0-210.0, 290.0-310.0).
        .SIGNAL_PATTERN        ( "DATA"    )  // DATA, CLOCK input signal
    ) i_idelaye2 (
        .CNTVALUEOUT (                       ), // 5-bit output: Counter value output
        .DATAOUT     ( net_phy_rxc_delayed   ), // 1-bit output: Delayed data output
        .C           ( 1'b0                  ), // 1-bit input: Clock input
        .CE          ( 1'b0                  ), // 1-bit input: Active high enable increment/decrement input
        .CINVCTRL    (                       ), // 1-bit input: Dynamic clock inversion input
        .CNTVALUEIN  ( 5'b0                  ), // 5-bit input: Counter value input
        .DATAIN      ( 1'b0                  ), // 1-bit input: Internal delay data input
        .IDATAIN     ( net_phy_rxc_ibufg_out ), // 1-bit input: Data input from the I/O
        .INC         ( 1'b0                  ), // 1-bit input: Increment / Decrement tap delay input
        .LD          ( 1'b0                  ), // 1-bit input: Load IDELAY_VALUE input
        .LDPIPEEN    ( 1'b0                  ), // 1-bit input: Enable PIPELINE register to load data input
        .REGRST      ( 1'b0                  )  // 1-bit input: Active-high reset tap-delay input
    );

    (* IODELAY_GROUP = "NET_PHY_RXC" *)
    IDELAYCTRL i_idelayctrl (
        .RDY    (           ), // 1-bit output: Ready output
        // 200-MHz for g2, clk_mmccm drives clocks through BUFG
        .REFCLK ( mem_clk_i ), // 1-bit input: Reference clock input
        .RST    ( 1'b0      )  // 1-bit input: Active high reset input
    );

    BUFG BUFG_inst (
      .I ( net_phy_rxc_delayed ),
      .O ( net_phy_rx_clk      )
    );

    // The RX_CTL signal carries RXDV (data valid) on the rising edge, and (RXDV xor RXER)
    // on the falling edge.
    // data valid is transmitted on positive edge
    always_ff @(posedge net_phy_rx_clk) begin
        if (~rgmii_phy_rst_n) begin
            net_phy_rx_dv_f <= 1'b0;
        end else begin
            net_phy_rx_dv_f <= rgmii_phy_rxctl;
        end
    end

    // data error is encoded on negative edge of rxctl
    always_ff @(negedge net_phy_rx_clk) begin
        if (~rgmii_phy_rst_n) begin
            net_phy_rx_err_f <= 1'b0;
        end else begin
            net_phy_rx_err_f <= rgmii_phy_rxctl;
        end
    end

    always_ff @(posedge net_phy_rx_clk) begin
        if (~rgmii_phy_rst_n) begin
            net_phy_rxd_f     <= '0;
            net_phy_rxd_ff    <= '0;
            net_phy_rx_dv_ff  <= 1'b0;
            net_phy_rx_err_ff <= 1'b0;
        end else begin
            net_phy_rxd_f     <= rgmii_phy_rxd;
            net_phy_rxd_ff    <= net_phy_rxd_f;
            net_phy_rx_dv_ff  <= net_phy_rx_dv_f;
            net_phy_rx_err_ff <= net_phy_rx_err_f;
        end
    end

    assign net_phy_dv = net_phy_rx_dv_ff;
    assign net_phy_rx_er = net_phy_rx_dv_ff ^ net_phy_rx_err_ff;
    assign net_phy_rx_data = net_phy_rxd_ff;

endmodule

`include "ariane_xlnx_mapper.svh"

module ariane_peripherals_wrapper#(
    parameter AXI_ID_WIDTH   = 10,
    parameter AXI_ADDR_WIDTH = 64,
    parameter AXI_DATA_WIDTH = 64,
    parameter AXI_USER_WIDTH = 1
)
(
    input logic aclk,
    input logic aresetn,
    input wire uart_irq_i,
    input wire spi_irq_i,
    input wire eth_irq_i,
    input wire[ariane_soc::NumSources-1:7] irq_i,
    `AXI_INTERFACE_MODULE_INPUT(s_axi_plic),
    `AXI_INTERFACE_MODULE_INPUT(s_axi_timer),
    output logic [1:0] irq_out
);

AXI_BUS#(
    .AXI_ADDR_WIDTH ( AXI_ADDR_WIDTH     ),
    .AXI_DATA_WIDTH ( AXI_DATA_WIDTH     ),
    .AXI_ID_WIDTH   ( AXI_ID_WIDTH ),
    .AXI_USER_WIDTH ( AXI_USER_WIDTH     )
) master[ariane_soc::NB_PERIPHERALS-1:0]();


`ASSIGN_ARIANE_INTERFACE_FROM_XLNX_STYLE_INPUTS(s_axi_plic,master[ariane_soc::PLIC])
`ASSIGN_ARIANE_INTERFACE_FROM_XLNX_STYLE_INPUTS(s_axi_timer,master[ariane_soc::Timer])


ariane_peripherals#(
    .AxiAddrWidth ( AXI_ADDR_WIDTH     ),
    .AxiDataWidth ( AXI_DATA_WIDTH     ),
    .AxiIdWidth   ( AXI_ID_WIDTH       ),
    .AxiUserWidth ( AXI_USER_WIDTH     ),
    .InclUART     ( 1'b0               ),
    .InclGPIO     ( 1'b0               ),
    .InclSPI      ( 1'b0               ),
    .InclEthernet ( 1'b0               )
) i_ariane_peripherals (
    .clk_i        ( aclk               ),
    .clk_200MHz_i ( 0                  ),
    .rst_ni       ( aresetn            ),
    .plic         ( master[ariane_soc::PLIC]     ),
    .uart         ( master[ariane_soc::UART]     ),
    .spi          ( master[ariane_soc::SPI]      ),
    .gpio         ( master[ariane_soc::GPIO]     ),
    .eth_clk_i    ( 0                            ),
    .ethernet     ( master[ariane_soc::Ethernet] ),
    .timer        ( master[ariane_soc::Timer]    ),
    .uart_irq_i   ( uart_irq_i                   ),
    .spi_irq_i    ( spi_irq_i                    ),
    .eth_irq_i    ( eth_irq_i                    ),
    .irq_i        ( irq_i                        ),
    .irq_o        ( irq_out                      ),
    .rx_i         ( 0                            ),
    .tx_o         ( /* not used*/                ),
    .eth_txck(0),
    .eth_rxck(0),
    .eth_rxctl(0),
    .eth_rxd(0),
    .eth_rst_n(0),
    .eth_txctl(0),
    .eth_txd(0),
    .eth_mdio(0),
    .eth_mdc(0),
    .phy_tx_clk_i   ( 0                    ),
    .sd_clk_i       ( 0                    ),
    .spi_clk_o      ( /* not used*/        ),
    .spi_mosi       ( 0                    ),
    .spi_miso       ( 0                    ),
    .spi_ss         ( 0                    ),
    .leds_o         ( /* not used*/        ),
    .dip_switches_i ( /* not used*/        )

);

endmodule

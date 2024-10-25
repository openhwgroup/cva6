`include "axi/assign.svh"
`include "axi/typedef.svh"

`include "ariane_xlnx_config.svh"
`include "ariane_xlnx_mapper.svh"

module clint_wrapper#(
    parameter AXI_ID_WIDTH      = 10,
    parameter AXI_ADDR_WIDTH    = 64,
    parameter AXI_DATA_WIDTH    = 64,
    parameter AXI_USER_WIDTH    = 1,
    parameter NUMBER_INTERRUPTS = 4
)
(
    input logic aclk,
    input logic aresetn,

    `AXI_INTERFACE_MODULE_INPUT(s_axi_clint),

    output logic timer_irq_o,
    output logic ipi_o
);

logic rtc;

import ariane_axi::req_t;
import ariane_axi::resp_t;

AXI_BUS #(
    .AXI_ADDR_WIDTH ( AXI_ADDR_WIDTH          ),
    .AXI_DATA_WIDTH ( AXI_DATA_WIDTH          ),
    .AXI_ID_WIDTH   ( AXI_ID_WIDTH            ),
    .AXI_USER_WIDTH ( AXI_DATA_WIDTH          )
) tmp_bus ();

// divide clock by two
always_ff @(posedge aclk or negedge aresetn) begin
  if (~aresetn) begin
    rtc <= 0;
  end else begin
    rtc <= rtc ^ 1'b1;
  end
end

req_t  axi_clint_req;
resp_t axi_clint_resp;

clint #(
    .CVA6Cfg        ( CVA6Cfg            ),
    .AXI_ADDR_WIDTH ( AXI_ADDR_WIDTH     ),
    .AXI_DATA_WIDTH ( AXI_DATA_WIDTH     ),
    .AXI_ID_WIDTH   ( AXI_ID_WIDTH       ),
    .NR_CORES       ( 1                  ),
    .axi_req_t      ( req_t              ),
    .axi_resp_t     ( resp_t             )
) i_clint (
    .clk_i       ( aclk           ),
    .rst_ni      ( aresetn        ),
    .testmode_i  ( 0              ),
    .axi_req_i   ( axi_clint_req  ),
    .axi_resp_o  ( axi_clint_resp ),
    .rtc_i       ( rtc            ),
    .timer_irq_o ( timer_irq_o      ),
    .ipi_o       ( ipi_o            )
);

`AXI_ASSIGN_TO_REQ(axi_clint_req, tmp_bus)
`AXI_ASSIGN_FROM_RESP(tmp_bus, axi_clint_resp)
`ASSIGN_ARIANE_INTERFACE_FROM_XLNX_STYLE_INPUTS(s_axi_clint,tmp_bus)
endmodule

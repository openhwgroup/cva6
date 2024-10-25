`include "ariane_xlnx_mapper.svh"
module clint_wrapper_verilog
#(
    parameter AXI_ID_WIDTH=10,
    parameter AXI_ADDR_WIDTH=64,
    parameter AXI_DATA_WIDTH=64,
    parameter AXI_USER_WIDTH=1, 
    parameter NUMBER_INTERRUPTS=4
)
(
    input wire aclk,
    input wire aresetn,


    `AXI_INTERFACE_MODULE_INPUT(s_axi_clint),


    output wire timer_irq_o,
    output wire ipi_o
    
);

clint_wrapper #(
    .AXI_ID_WIDTH(AXI_ID_WIDTH),
    .AXI_ADDR_WIDTH(AXI_ADDR_WIDTH),
    .AXI_DATA_WIDTH(AXI_DATA_WIDTH),
    .AXI_USER_WIDTH(AXI_USER_WIDTH)
)
i_clint_wrapper(
    .aclk(aclk),
    .aresetn(aresetn),
    
    `AXI_INTERFACE_FORWARD(s_axi_clint),

    .timer_irq_o(timer_irq_o),
    .ipi_o(ipi_o)
);

endmodule
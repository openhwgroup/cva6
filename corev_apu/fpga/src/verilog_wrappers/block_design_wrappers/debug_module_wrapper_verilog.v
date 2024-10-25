`include "ariane_xlnx_mapper.svh"
module debug_module_wrapper_verilog
#(
    parameter AXI_ID_WIDTH=10,
    parameter AXI_ADDR_WIDTH=64,
    parameter AXI_DATA_WIDTH=64,
    parameter AXI_USER_WIDTH=1
)
(
    input wire aclk,
    input wire aresetn,

    `AXI_INTERFACE_MODULE_INPUT(s_axi_dmi_jtag),
    `AXI_INTERFACE_MODULE_OUTPUT(m_axi_dmi_jtag),


    // jtag ports
    input  wire        jtag_trst_n,
    input  wire        jtag_tck,
    input  wire        jtag_tms,
    input  wire        jtag_tdi,
    output wire        jtag_tdo,

    // to CPU/other peripherals
    (*X_INTERFACE_INFO = "xilinx.com:signal:reset:1.0 ndmreset RST", X_INTERFACE_PARAMETER="POLARITY ACTIVE_HIGH"*)
    output wire ndmreset,
    (*X_INTERFACE_INFO = "xilinx.com:signal:interrupt:1.0 debug_req_irq INTERRUPT", X_INTERFACE_PARAMETER = "SENSITIVITY EDGE_RISING" *)
    output wire debug_req_irq
);

debug_module_wrapper
#(
    .AXI_ID_WIDTH(AXI_ID_WIDTH),
    .AXI_ADDR_WIDTH(AXI_ADDR_WIDTH),
    .AXI_DATA_WIDTH(AXI_DATA_WIDTH),
    .AXI_USER_WIDTH(AXI_USER_WIDTH)
)
i_debug_module_wrapper
(
    .aclk(aclk),
    .aresetn(aresetn),

    `AXI_INTERFACE_FORWARD(m_axi_dmi_jtag),
    `AXI_INTERFACE_FORWARD(s_axi_dmi_jtag),
    .tck(jtag_tck),
    .tms(jtag_tms),
    .tdi(jtag_tdi),
    .tdo(jtag_tdo),
    .trst_n(jtag_trst_n),
    .ndmreset(ndmreset),
    .debug_req_irq(debug_req_irq)
);

endmodule

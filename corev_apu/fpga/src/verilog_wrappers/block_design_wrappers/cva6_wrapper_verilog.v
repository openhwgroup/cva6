`include "ariane_xlnx_mapper.svh"
module cva6_wrapper_verilog #(
    parameter AXI_ID_WIDTH   = 10,
    parameter AXI_ADDR_WIDTH = 64,
    parameter AXI_DATA_WIDTH = 64,
    parameter AXI_USER_WIDTH = 1,
    parameter AXI_CUT_BYPASS = 1
) (
    input wire aclk,
    input wire aresetn,
    (*X_INTERFACE_INFO = "xilinx.com:signal:interrupt:1.0 irqs_in INTERRUPT", X_INTERFACE_PARAMETER = "SENSITIVITY EDGE_RISING" *)
    input wire [1 : 0] irqs_in,
    (*X_INTERFACE_INFO = "xilinx.com:signal:interrupt:1.0 ipi_in INTERRUPT", X_INTERFACE_PARAMETER = "SENSITIVITY EDGE_RISING" *)
    input wire ipi_in,
    (*X_INTERFACE_INFO = "xilinx.com:signal:interrupt:1.0 timer_irq_i INTERRUPT", X_INTERFACE_PARAMETER = "SENSITIVITY EDGE_RISING" *)
    input wire timer_irq_i,
    (*X_INTERFACE_INFO = "xilinx.com:signal:interrupt:1.0 debug_req_irq INTERRUPT", X_INTERFACE_PARAMETER = "SENSITIVITY EDGE_RISING" *)
    input wire debug_req_irq,


    `AXI_INTERFACE_MODULE_OUTPUT(m_axi_cpu)
);

  cva6_wrapper #(
      .AXI_ID_WIDTH  (AXI_ID_WIDTH),
      .AXI_ADDR_WIDTH(AXI_ADDR_WIDTH),
      .AXI_DATA_WIDTH(AXI_DATA_WIDTH),
      .AXI_USER_WIDTH(AXI_USER_WIDTH),
      .AXI_CUT_BYPASS(AXI_CUT_BYPASS)
  ) i_cva6_wrapper (
      .aclk(aclk),
      .aresetn(aresetn),
      .irqs_in(irqs_in),
      .ipi_in(ipi_in),
      .timer_irq_i(timer_irq_i),
      .debug_req_irq(debug_req_irq),

      `AXI_INTERFACE_FORWARD(m_axi_cpu)
  );

endmodule

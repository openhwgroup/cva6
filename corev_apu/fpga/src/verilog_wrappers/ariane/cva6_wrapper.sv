`include "register_interface/assign.svh"
`include "rvfi_types.svh"

`include "ariane_xlnx_mapper.svh"
`include "ariane_xlnx_config.svh"

import cva6_config_pkg::*;

module cva6_wrapper #(
    parameter AXI_ID_WIDTH   = 10,
    parameter AXI_ADDR_WIDTH = 64,
    parameter AXI_DATA_WIDTH = 64,
    parameter AXI_USER_WIDTH = 1,
    parameter AXI_CUT_BYPASS = 1
) (
    input logic aclk,
    input logic aresetn,
    input logic [1:0] irqs_in,
    input logic ipi_in,
    input logic timer_irq_i,
    input logic debug_req_irq,

    `AXI_INTERFACE_MODULE_OUTPUT(m_axi_cpu)
);


  ariane_axi::req_t axi_ariane_req, axi_cut_req;
  ariane_axi::resp_t axi_ariane_resp, axi_cut_resp;

  AXI_BUS #(
      .AXI_ADDR_WIDTH(AXI_ADDR_WIDTH),
      .AXI_DATA_WIDTH(AXI_DATA_WIDTH),
      .AXI_ID_WIDTH  (AXI_ID_WIDTH),
      .AXI_USER_WIDTH(AXI_DATA_WIDTH)
  )
      tmp_bus (), cpu_bus ();

  import axi_pkg::BURST_FIXED;
  import axi_pkg::BURST_INCR;
  import axi_pkg::BURST_WRAP;

  import axi_pkg::RESP_OKAY;
  import axi_pkg::RESP_EXOKAY;
  import axi_pkg::RESP_DECERR;
  import axi_pkg::RESP_SLVERR;

  localparam type rvfi_probes_instr_t = `RVFI_PROBES_INSTR_T(CVA6Cfg);
  localparam type rvfi_probes_csr_t = `RVFI_PROBES_CSR_T(CVA6Cfg);
  localparam type rvfi_probes_t = struct packed {
    logic csr;
    logic instr;
  };


  ariane #(
      .CVA6Cfg(CVA6Cfg),
      .rvfi_probes_instr_t(rvfi_probes_instr_t),
      .rvfi_probes_csr_t(rvfi_probes_csr_t),
      .rvfi_probes_t(rvfi_probes_t)
  ) i_ariane (
      .clk_i        (aclk),
      .rst_ni       (aresetn),
      .boot_addr_i  (ariane_soc::ROMBase),  // start fetching from ROM
      .hart_id_i    ('0),
      .irq_i        (irqs_in),
      .ipi_i        (ipi_in),
      .time_irq_i   (timer_irq_i),
      .rvfi_probes_o(  /* open */),
      .debug_req_i  (debug_req_irq),
      .noc_req_o    (axi_ariane_req),
      .noc_resp_i   (axi_ariane_resp)
  );

  `AXI_ASSIGN_FROM_REQ(cpu_bus, axi_ariane_req)
  `AXI_ASSIGN_TO_RESP(axi_ariane_resp, cpu_bus)

  axi_cut_intf #(
      .ADDR_WIDTH(AXI_ADDR_WIDTH),
      .DATA_WIDTH(AXI_DATA_WIDTH),
      .ID_WIDTH(AXI_ID_WIDTH),
      .USER_WIDTH(AXI_USER_WIDTH),
      .BYPASS(AXI_CUT_BYPASS)
  ) i_axi_cut (
      .clk_i(aclk),
      .rst_ni(aresetn),
      .in(cpu_bus),
      .out(tmp_bus)
  );

  `ASSIGN_XLNX_INTERFACE_FROM_ARIANE_STYLE_INPUTS(m_axi_cpu, tmp_bus)
endmodule

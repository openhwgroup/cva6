`include "register_interface/typedef.svh"
`include "register_interface/assign.svh"
`include "axi/typedef.svh"
`include "axi/assign.svh"

/// Interface wrapper.
module axi_lite_to_reg_intf #(
  /// The width of the address.
  parameter int ADDR_WIDTH = -1,
  /// The width of the data.
  parameter int DATA_WIDTH = -1,
  /// Buffer depth (how many outstanding transactions do we allow)
  parameter int BUFFER_DEPTH = 2,
  /// Whether the AXI-Lite W channel should be decoupled with a register. This
  /// can help break long paths at the expense of registers.
  parameter bit DECOUPLE_W = 1
) (
  input  logic   clk_i  ,
  input  logic   rst_ni ,
  AXI_LITE.Slave axi_i  ,
  REG_BUS.out    reg_o
);

  typedef logic [ADDR_WIDTH-1:0] addr_t;
  typedef logic [DATA_WIDTH-1:0] data_t;
  typedef logic [DATA_WIDTH/8-1:0] strb_t;

  `REG_BUS_TYPEDEF_REQ(reg_req_t, addr_t, data_t, strb_t)
  `REG_BUS_TYPEDEF_RSP(reg_rsp_t, data_t)

  `AXI_LITE_TYPEDEF_AW_CHAN_T(aw_chan_t, addr_t)
  `AXI_LITE_TYPEDEF_W_CHAN_T(w_chan_t, data_t, strb_t)
  `AXI_LITE_TYPEDEF_B_CHAN_T(b_chan_t)
  `AXI_LITE_TYPEDEF_AR_CHAN_T(ar_chan_t, addr_t)
  `AXI_LITE_TYPEDEF_R_CHAN_T(r_chan_t, data_t)
  `AXI_LITE_TYPEDEF_REQ_T(axi_req_t, aw_chan_t, w_chan_t, ar_chan_t)
  `AXI_LITE_TYPEDEF_RESP_T(axi_resp_t, b_chan_t, r_chan_t)

  axi_req_t  axi_req;
  axi_resp_t axi_resp;
  reg_req_t reg_req;
  reg_rsp_t reg_rsp;

  `AXI_LITE_ASSIGN_TO_REQ(axi_req, axi_i)
  `AXI_LITE_ASSIGN_FROM_RESP(axi_i, axi_resp)

  `REG_BUS_ASSIGN_FROM_REQ(reg_o, reg_req)
  `REG_BUS_ASSIGN_TO_RSP(reg_rsp, reg_o)

  axi_lite_to_reg #(
    .ADDR_WIDTH (ADDR_WIDTH),
    .DATA_WIDTH (DATA_WIDTH),
    .BUFFER_DEPTH (BUFFER_DEPTH),
    .DECOUPLE_W (DECOUPLE_W),
    .axi_lite_req_t (axi_req_t),
    .axi_lite_rsp_t (axi_resp_t),
    .reg_req_t (reg_req_t),
    .reg_rsp_t (reg_rsp_t)
  ) i_axi_lite_to_reg (
    .clk_i (clk_i),
    .rst_ni (rst_ni),
    .axi_lite_req_i (axi_req),
    .axi_lite_rsp_o (axi_resp),
    .reg_req_o (reg_req),
    .reg_rsp_i (reg_rsp)
  );

endmodule
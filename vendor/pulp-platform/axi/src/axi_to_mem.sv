// Copyright 2020 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Authors:
// - Michael Rogenmoser <michaero@iis.ee.ethz.ch>
// - Thomas Benz <tbenz@iis.ee.ethz.ch>

`include "common_cells/registers.svh"
/// AXI4+ATOP slave module which translates AXI bursts into a memory stream.
/// If both read and write channels of the AXI4+ATOP are active, both will have an
/// utilization of 50%.
module axi_to_mem #(
  /// AXI4+ATOP request type. See `include/axi/typedef.svh`.
  parameter type         axi_req_t  = logic,
  /// AXI4+ATOP response type. See `include/axi/typedef.svh`.
  parameter type         axi_resp_t = logic,
  /// Address width, has to be less or equal than the width off the AXI address field.
  /// Determines the width of `mem_addr_o`. Has to be wide enough to emit the memory region
  /// which should be accessible.
  parameter int unsigned AddrWidth  = 0,
  /// AXI4+ATOP data width.
  parameter int unsigned DataWidth  = 0,
  /// AXI4+ATOP ID width.
  parameter int unsigned IdWidth    = 0,
  /// Number of banks at output, must evenly divide `DataWidth`.
  parameter int unsigned NumBanks   = 0,
  /// Depth of memory response buffer. This should be equal to the memory response latency.
  parameter int unsigned BufDepth   = 1,
  /// Hide write requests if the strb == '0
  parameter bit          HideStrb   = 1'b0,
  /// Depth of output fifo/fall_through_register. Increase for asymmetric backpressure (contention) on banks.
  parameter int unsigned OutFifoDepth = 1,
  /// Dependent parameter, do not override. Memory address type.
  localparam type addr_t     = logic [AddrWidth-1:0],
  /// Dependent parameter, do not override. Memory data type.
  localparam type mem_data_t = logic [DataWidth/NumBanks-1:0],
  /// Dependent parameter, do not override. Memory write strobe type.
  localparam type mem_strb_t = logic [DataWidth/NumBanks/8-1:0]
) (
  /// Clock input.
  input  logic                           clk_i,
  /// Asynchronous reset, active low.
  input  logic                           rst_ni,
  /// The unit is busy handling an AXI4+ATOP request.
  output logic                           busy_o,
  /// AXI4+ATOP slave port, request input.
  input  axi_req_t                       axi_req_i,
  /// AXI4+ATOP slave port, response output.
  output axi_resp_t                      axi_resp_o,
  /// Memory stream master, request is valid for this bank.
  output logic           [NumBanks-1:0]  mem_req_o,
  /// Memory stream master, request can be granted by this bank.
  input  logic           [NumBanks-1:0]  mem_gnt_i,
  /// Memory stream master, byte address of the request.
  output addr_t          [NumBanks-1:0]  mem_addr_o,
  /// Memory stream master, write data for this bank. Valid when `mem_req_o`.
  output mem_data_t      [NumBanks-1:0]  mem_wdata_o,
  /// Memory stream master, byte-wise strobe (byte enable).
  output mem_strb_t      [NumBanks-1:0]  mem_strb_o,
  /// Memory stream master, `axi_pkg::atop_t` signal associated with this request.
  output axi_pkg::atop_t [NumBanks-1:0]  mem_atop_o,
  /// Memory stream master, write enable. Then asserted store of `mem_w_data` is requested.
  output logic           [NumBanks-1:0]  mem_we_o,
  /// Memory stream master, response is valid. This module expects always a response valid for a
  /// request regardless if the request was a write or a read.
  input  logic           [NumBanks-1:0]  mem_rvalid_i,
  /// Memory stream master, read response data.
  input  mem_data_t      [NumBanks-1:0]  mem_rdata_i
);

  axi_to_detailed_mem #(
    .axi_req_t    ( axi_req_t    ),
    .axi_resp_t   ( axi_resp_t   ),
    .AddrWidth    ( AddrWidth    ),
    .DataWidth    ( DataWidth    ),
    .IdWidth      ( IdWidth      ),
    .UserWidth    ( 1            ),
    .NumBanks     ( NumBanks     ),
    .BufDepth     ( BufDepth     ),
    .HideStrb     ( HideStrb     ),
    .OutFifoDepth ( OutFifoDepth )
  ) i_axi_to_detailed_mem (
    .clk_i,
    .rst_ni,
    .busy_o,
    .axi_req_i    ( axi_req_i     ),
    .axi_resp_o   ( axi_resp_o    ),
    .mem_req_o    ( mem_req_o     ),
    .mem_gnt_i    ( mem_gnt_i     ),
    .mem_addr_o   ( mem_addr_o    ),
    .mem_wdata_o  ( mem_wdata_o   ),
    .mem_strb_o   ( mem_strb_o    ),
    .mem_atop_o   ( mem_atop_o    ),
    .mem_lock_o   (),
    .mem_we_o     ( mem_we_o      ),
    .mem_id_o     (),
    .mem_user_o   (),
    .mem_cache_o  (),
    .mem_prot_o   (),
    .mem_qos_o    (),
    .mem_region_o (),
    .mem_rvalid_i ( mem_rvalid_i ),
    .mem_rdata_i  ( mem_rdata_i   ),
    .mem_err_i    ('0),
    .mem_exokay_i ('0)
  );

endmodule


`include "axi/assign.svh"
`include "axi/typedef.svh"
/// Interface wrapper for module `axi_to_mem`.
module axi_to_mem_intf #(
  /// See `axi_to_mem`, parameter `AddrWidth`.
  parameter int unsigned ADDR_WIDTH     = 32'd0,
  /// See `axi_to_mem`, parameter `DataWidth`.
  parameter int unsigned DATA_WIDTH     = 32'd0,
  /// AXI4+ATOP ID width.
  parameter int unsigned ID_WIDTH       = 32'd0,
  /// AXI4+ATOP user width.
  parameter int unsigned USER_WIDTH     = 32'd0,
  /// See `axi_to_mem`, parameter `NumBanks`.
  parameter int unsigned NUM_BANKS      = 32'd0,
  /// See `axi_to_mem`, parameter `BufDepth`.
  parameter int unsigned BUF_DEPTH      = 32'd1,
  /// Hide write requests if the strb == '0
  parameter bit          HIDE_STRB      = 1'b0,
  /// Depth of output fifo/fall_through_register. Increase for asymmetric backpressure (contention) on banks.
  parameter int unsigned OUT_FIFO_DEPTH = 32'd1,
  /// Dependent parameter, do not override. See `axi_to_mem`, parameter `addr_t`.
  localparam type addr_t     = logic [ADDR_WIDTH-1:0],
  /// Dependent parameter, do not override. See `axi_to_mem`, parameter `mem_data_t`.
  localparam type mem_data_t = logic [DATA_WIDTH/NUM_BANKS-1:0],
  /// Dependent parameter, do not override. See `axi_to_mem`, parameter `mem_strb_t`.
  localparam type mem_strb_t = logic [DATA_WIDTH/NUM_BANKS/8-1:0]
) (
  /// Clock input.
  input  logic                            clk_i,
  /// Asynchronous reset, active low.
  input  logic                            rst_ni,
  /// See `axi_to_mem`, port `busy_o`.
  output logic                            busy_o,
  /// AXI4+ATOP slave interface port.
  AXI_BUS.Slave                           slv,
  /// See `axi_to_mem`, port `mem_req_o`.
  output logic           [NUM_BANKS-1:0]  mem_req_o,
  /// See `axi_to_mem`, port `mem_gnt_i`.
  input  logic           [NUM_BANKS-1:0]  mem_gnt_i,
  /// See `axi_to_mem`, port `mem_addr_o`.
  output addr_t          [NUM_BANKS-1:0]  mem_addr_o,
  /// See `axi_to_mem`, port `mem_wdata_o`.
  output mem_data_t      [NUM_BANKS-1:0]  mem_wdata_o,
  /// See `axi_to_mem`, port `mem_strb_o`.
  output mem_strb_t      [NUM_BANKS-1:0]  mem_strb_o,
  /// See `axi_to_mem`, port `mem_atop_o`.
  output axi_pkg::atop_t [NUM_BANKS-1:0]  mem_atop_o,
  /// See `axi_to_mem`, port `mem_we_o`.
  output logic           [NUM_BANKS-1:0]  mem_we_o,
  /// See `axi_to_mem`, port `mem_rvalid_i`.
  input  logic           [NUM_BANKS-1:0]  mem_rvalid_i,
  /// See `axi_to_mem`, port `mem_rdata_i`.
  input  mem_data_t      [NUM_BANKS-1:0]  mem_rdata_i
);
  typedef logic [ID_WIDTH-1:0]     id_t;
  typedef logic [DATA_WIDTH-1:0]   data_t;
  typedef logic [DATA_WIDTH/8-1:0] strb_t;
  typedef logic [USER_WIDTH-1:0]   user_t;
  `AXI_TYPEDEF_AW_CHAN_T(aw_chan_t, addr_t, id_t, user_t)
  `AXI_TYPEDEF_W_CHAN_T(w_chan_t, data_t, strb_t, user_t)
  `AXI_TYPEDEF_B_CHAN_T(b_chan_t, id_t, user_t)
  `AXI_TYPEDEF_AR_CHAN_T(ar_chan_t, addr_t, id_t, user_t)
  `AXI_TYPEDEF_R_CHAN_T(r_chan_t, data_t, id_t, user_t)
  `AXI_TYPEDEF_REQ_T(req_t, aw_chan_t, w_chan_t, ar_chan_t)
  `AXI_TYPEDEF_RESP_T(resp_t, b_chan_t, r_chan_t)
  req_t   req;
  resp_t  resp;
  `AXI_ASSIGN_TO_REQ(req, slv)
  `AXI_ASSIGN_FROM_RESP(slv, resp)
  axi_to_mem #(
    .axi_req_t    ( req_t          ),
    .axi_resp_t   ( resp_t         ),
    .AddrWidth    ( ADDR_WIDTH     ),
    .DataWidth    ( DATA_WIDTH     ),
    .IdWidth      ( ID_WIDTH       ),
    .NumBanks     ( NUM_BANKS      ),
    .BufDepth     ( BUF_DEPTH      ),
    .HideStrb     ( HIDE_STRB      ),
    .OutFifoDepth ( OUT_FIFO_DEPTH )
  ) i_axi_to_mem (
    .clk_i,
    .rst_ni,
    .busy_o,
    .axi_req_i  ( req  ),
    .axi_resp_o ( resp ),
    .mem_req_o,
    .mem_gnt_i,
    .mem_addr_o,
    .mem_wdata_o,
    .mem_strb_o,
    .mem_atop_o,
    .mem_we_o,
    .mem_rvalid_i,
    .mem_rdata_i
  );
endmodule

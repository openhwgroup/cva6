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
// - Wolfgang Rönninger <wroennin@iis.ee.ethz.ch>
// - Michael Rogenmoser <michaero@iis.ee.ethz.ch>

/// AXI4+ATOP to banked SRAM memory slave. Allows for parallel read and write transactions.
/// Has higher throughput than `axi_to_mem`, however needs more hardware.
///
/// The used address space starts at 0x0 and ends at the capacity of all memory banks combined.
/// The higher address bits are ignored for accesses.
module axi_to_mem_banked #(
  /// AXI4+ATOP ID width
  parameter int unsigned                  AxiIdWidth    = 32'd0,
  /// AXI4+ATOP address width
  parameter int unsigned                  AxiAddrWidth  = 32'd0,
  /// AXI4+ATOP data width
  parameter int unsigned                  AxiDataWidth  = 32'd0,
  /// AXI4+ATOP AW channel struct
  parameter type                          axi_aw_chan_t = logic,
  /// AXI4+ATOP  W channel struct
  parameter type                          axi_w_chan_t  = logic,
  /// AXI4+ATOP  B channel struct
  parameter type                          axi_b_chan_t  = logic,
  /// AXI4+ATOP AR channel struct
  parameter type                          axi_ar_chan_t = logic,
  /// AXI4+ATOP  R channel struct
  parameter type                          axi_r_chan_t  = logic,
  /// AXI4+ATOP request struct
  parameter type                          axi_req_t     = logic,
  /// AXI4+ATOP response struct
  parameter type                          axi_resp_t    = logic,
  /// Number of memory banks / macros
  /// Has to satisfy:
  /// - MemNumBanks >= 2 * AxiDataWidth / MemDataWidth
  /// - MemNumBanks is a power of 2.
  parameter int unsigned                  MemNumBanks   = 32'd4,
  /// Address width of an individual memory bank. This is treated as a word address.
  parameter int unsigned                  MemAddrWidth  = 32'd11,
  /// Data width of the memory macros.
  /// Has to satisfy:
  /// - AxiDataWidth % MemDataWidth = 0
  parameter int unsigned                  MemDataWidth  = 32'd32,
  /// Read latency of the connected memory in cycles
  parameter int unsigned                  MemLatency    = 32'd1,
  /// Hide write requests if the strb == '0
  parameter bit                           HideStrb      = 1'b0,
  /// Depth of output fifo/fall_through_register. Increase for asymmetric backpressure (contention) on banks.
  parameter int unsigned                  OutFifoDepth = 1,
  /// DEPENDENT PARAMETER, DO NOT OVERWRITE! Address type of the memory request.
  parameter type mem_addr_t = logic [MemAddrWidth-1:0],
  /// DEPENDENT PARAMETER, DO NOT OVERWRITE! Atomic operation type for the memory request.
  parameter type mem_atop_t = axi_pkg::atop_t,
  /// DEPENDENT PARAMETER, DO NOT OVERWRITE! Data type for the memory request.
  parameter type mem_data_t = logic [MemDataWidth-1:0],
  /// DEPENDENT PARAMETER, DO NOT OVERWRITE! Byte strobe/enable signal for the memory request.
  parameter type mem_strb_t = logic [MemDataWidth/8-1:0]
) (
  /// Clock
  input  logic                        clk_i,
  /// Asynchronous reset, active low
  input  logic                        rst_ni,
  /// Testmode enable
  input  logic                        test_i,
  /// AXI4+ATOP slave port, request struct
  input  axi_req_t                    axi_req_i,
  /// AXI4+ATOP slave port, response struct
  output axi_resp_t                   axi_resp_o,
  /// Memory bank request
  output logic      [MemNumBanks-1:0] mem_req_o,
  /// Memory request grant
  input  logic      [MemNumBanks-1:0] mem_gnt_i,
  /// Request address
  output mem_addr_t [MemNumBanks-1:0] mem_add_o,
  /// Write request enable, active high
  output logic      [MemNumBanks-1:0] mem_we_o,
  /// Write data
  output mem_data_t [MemNumBanks-1:0] mem_wdata_o,
  /// Write data byte enable, active high
  output mem_strb_t [MemNumBanks-1:0] mem_be_o,
  /// Atomic operation
  output mem_atop_t [MemNumBanks-1:0] mem_atop_o,
  /// Read data response
  input  mem_data_t [MemNumBanks-1:0] mem_rdata_i,
  /// Status output, busy flag of `axi_to_mem`
  output logic      [1:0]             axi_to_mem_busy_o
);
  /// This specifies the number of banks needed to have the full data bandwidth of one
  /// AXI data channel.
  localparam int unsigned BanksPerAxiChannel = AxiDataWidth / MemDataWidth;
  /// Offset of the byte address from AXI to determine, where the selection signal for the
  /// memory bank should start.
  localparam int unsigned BankSelOffset = $clog2(MemDataWidth / 32'd8);
  /// Selection signal width of the xbar. This is the reason for power of two banks, otherwise
  /// There are holes in the address mapping.
  localparam int unsigned BankSelWidth  = cf_math_pkg::idx_width(MemNumBanks);
  typedef logic [BankSelWidth-1:0] xbar_sel_t;

  // Typedef for defining the channels
  typedef enum logic {
    ReadAccess  = 1'b0,
    WriteAccess = 1'b1
  } access_type_e;
  typedef logic [AxiAddrWidth-1:0] axi_addr_t;

  /// Payload definition which is sent over the xbar between the macros and the read/write unit.
  typedef struct packed {
    /// Address for the memory access
    mem_addr_t addr;
    /// Write enable, active high
    logic      we;
    /// Write data
    mem_data_t wdata;
    /// Strobe signal, byte enable
    mem_strb_t wstrb;
    /// Atomic operation, from AXI
    mem_atop_t atop;
  } xbar_payload_t;

  /// Read data definition for the shift register, which samples the read response data
  typedef struct packed {
    /// Selection signal for response routing
    xbar_sel_t sel;
    /// Selection is valid
    logic      valid;
  } read_sel_t;

  axi_req_t  [1:0] mem_axi_reqs;
  axi_resp_t [1:0] mem_axi_resps;

  // Fixed select `axi_demux` to split reads and writes to the two `axi_to_mem`
  axi_demux #(
    .AxiIdWidth  ( AxiIdWidth    ),
    .AtopSupport ( 1'b1          ),
    .aw_chan_t   ( axi_aw_chan_t ),
    .w_chan_t    ( axi_w_chan_t  ),
    .b_chan_t    ( axi_b_chan_t  ),
    .ar_chan_t   ( axi_ar_chan_t ),
    .r_chan_t    ( axi_r_chan_t  ),
    .axi_req_t   ( axi_req_t     ),
    .axi_resp_t  ( axi_resp_t    ),
    .NoMstPorts  ( 32'd2         ),
    .MaxTrans    ( MemLatency+2  ), // allow multiple Ax vectors to not starve W channel
    .AxiLookBits ( 32'd1         ), // select is fixed, do not need it
    .UniqueIds   ( 1'b0          ),
    .SpillAw     ( 1'b1          ),
    .SpillW      ( 1'b1          ),
    .SpillB      ( 1'b1          ),
    .SpillAr     ( 1'b1          ),
    .SpillR      ( 1'b1          )
  ) i_axi_demux (
    .clk_i,
    .rst_ni,
    .test_i,
    .slv_req_i       ( axi_req_i     ),
    .slv_aw_select_i ( WriteAccess   ),
    .slv_ar_select_i ( ReadAccess    ),
    .slv_resp_o      ( axi_resp_o    ),
    .mst_reqs_o      ( mem_axi_reqs  ),
    .mst_resps_i     ( mem_axi_resps )
  );

  xbar_payload_t [1:0][BanksPerAxiChannel-1:0] inter_payload;
  xbar_sel_t     [1:0][BanksPerAxiChannel-1:0] inter_sel;
  logic          [1:0][BanksPerAxiChannel-1:0] inter_valid,   inter_ready;

  // axi_to_mem protocol converter
  for (genvar i = 0; i < 2; i++) begin : gen_axi_to_mem
    axi_addr_t [BanksPerAxiChannel-1:0] req_addr;  // This is a byte address
    mem_data_t [BanksPerAxiChannel-1:0] req_wdata, res_rdata;
    mem_strb_t [BanksPerAxiChannel-1:0] req_wstrb;
    mem_atop_t [BanksPerAxiChannel-1:0] req_atop;

    logic      [BanksPerAxiChannel-1:0] req_we,    res_valid;

    // Careful, request / grant
    // Only assert grant, if there is a ready
    axi_to_mem #(
      .axi_req_t    ( axi_req_t          ),
      .axi_resp_t   ( axi_resp_t         ),
      .AddrWidth    ( AxiAddrWidth       ),
      .DataWidth    ( AxiDataWidth       ),
      .IdWidth      ( AxiIdWidth         ),
      .NumBanks     ( BanksPerAxiChannel ),
      .BufDepth     ( MemLatency         ),
      .HideStrb     ( HideStrb           ),
      .OutFifoDepth ( OutFifoDepth       )
    ) i_axi_to_mem (
      .clk_i,
      .rst_ni,
      .busy_o       ( axi_to_mem_busy_o[i]            ),
      .axi_req_i    ( mem_axi_reqs[i]                 ),
      .axi_resp_o   ( mem_axi_resps[i]                ),
      .mem_req_o    ( inter_valid[i]                  ),
      .mem_gnt_i    ( inter_ready[i] & inter_valid[i] ), // convert valid/ready to req/gnt
      .mem_addr_o   ( req_addr                        ),
      .mem_wdata_o  ( req_wdata                       ),
      .mem_strb_o   ( req_wstrb                       ),
      .mem_atop_o   ( req_atop                        ),
      .mem_we_o     ( req_we                          ),
      .mem_rvalid_i ( res_valid                       ),
      .mem_rdata_i  ( res_rdata                       )
    );
    // Pack the payload data together
    for (genvar j = 0; unsigned'(j) < BanksPerAxiChannel; j++) begin : gen_response_mux
      // Cut out the bank selection signal.
      assign inter_sel[i][j] = req_addr[j][BankSelOffset+:BankSelWidth];

      // Assign the xbar payload.
      assign inter_payload[i][j] = xbar_payload_t'{
        // Cut out the word address for the banks.
        addr:    req_addr[j][(BankSelOffset+BankSelWidth)+:MemAddrWidth],
        we:      req_we[j],
        wdata:   req_wdata[j],
        wstrb:   req_wstrb[j],
        atop:    req_atop[j],
        default: '0
      };

      // Cut out the portion of the address for the bank selection, each bank is word addressed!
      read_sel_t r_shift_inp, r_shift_oup;
      // Pack the selection into the shift register
      assign r_shift_inp = read_sel_t'{
        sel:     inter_sel[i][j],                       // Selection for response multiplexer
        valid:   inter_valid[i][j] & inter_ready[i][j], // Valid when req to SRAM
        default: '0
      };

      // Select the right read response data.
      // Writes should also generate a `response`.
      assign res_valid[j] = r_shift_oup.valid;
      assign res_rdata[j] = mem_rdata_i[r_shift_oup.sel];

      // Connect for the response data `MemLatency` cycles after a request was made to the xbar.
      shift_reg #(
        .dtype ( read_sel_t ),
        .Depth ( MemLatency )
      ) i_shift_reg_rdata_mux (
        .clk_i,
        .rst_ni,
        .d_i    ( r_shift_inp ),
        .d_o    ( r_shift_oup )
      );
    end
  end

  // Xbar to arbitrate data over the different memory banks
  xbar_payload_t [MemNumBanks-1:0] mem_payload;

  stream_xbar #(
    .NumInp      ( 32'd2 * BanksPerAxiChannel ),
    .NumOut      ( MemNumBanks                ),
    .payload_t   ( xbar_payload_t             ),
    .OutSpillReg ( 1'b0                       ),
    .ExtPrio     ( 1'b0                       ),
    .AxiVldRdy   ( 1'b1                       ),
    .LockIn      ( 1'b1                       )
  ) i_stream_xbar (
    .clk_i,
    .rst_ni,
    .flush_i ( 1'b0          ),
    .rr_i    ( '0            ),
    .data_i  ( inter_payload ),
    .sel_i   ( inter_sel     ),
    .valid_i ( inter_valid   ),
    .ready_o ( inter_ready   ),
    .data_o  ( mem_payload   ),
    .idx_o   ( /*not used*/  ),
    .valid_o ( mem_req_o     ),
    .ready_i ( mem_gnt_i     )
  );

  // Memory request output assignment
  for (genvar i = 0; unsigned'(i) < MemNumBanks; i++) begin : gen_mem_outp
    assign mem_add_o[i]   = mem_payload[i].addr;
    assign mem_we_o[i]    = mem_payload[i].we;
    assign mem_wdata_o[i] = mem_payload[i].wdata;
    assign mem_be_o[i]    = mem_payload[i].wstrb;
    assign mem_atop_o[i]  = mem_payload[i].atop;
  end

// pragma translate_off
`ifndef VERILATOR
  initial begin: p_assertions
    assert (AxiIdWidth   >= 32'd1) else $fatal(1, "AxiIdWidth must be at least 1!");
    assert (AxiAddrWidth >= 32'd1) else $fatal(1, "AxiAddrWidth must be at least 1!");
    assert (AxiDataWidth >= 32'd1) else $fatal(1, "AxiDataWidth must be at least 1!");
    assert (MemNumBanks  >= 32'd2 * AxiDataWidth / MemDataWidth) else
        $fatal(1, "MemNumBanks has to be >= 2 * AxiDataWidth / MemDataWidth");
    assert (MemLatency   >= 32'd1) else $fatal(1, "MemLatency has to be at least 1!");
    assert ($onehot(MemNumBanks))  else $fatal(1, "MemNumBanks has to be a power of 2.");
    assert (MemAddrWidth >= 32'd1) else $fatal(1, "MemAddrWidth must be at least 1!");
    assert (MemDataWidth >= 32'd1) else $fatal(1, "MemDataWidth must be at least 1!");
    assert (AxiDataWidth % MemDataWidth == 0) else
        $fatal(1, "MemDataWidth has to be a divisor of AxiDataWidth.");
  end
`endif
// pragma translate_on
endmodule

`include "axi/typedef.svh"
`include "axi/assign.svh"
/// AXI4+ATOP interface wrapper for `axi_to_mem`
module axi_to_mem_banked_intf #(
  /// AXI4+ATOP ID width
  parameter int unsigned                  AXI_ID_WIDTH   = 32'd0,
  /// AXI4+ATOP address width
  parameter int unsigned                  AXI_ADDR_WIDTH = 32'd0,
  /// AXI4+ATOP data width
  parameter int unsigned                  AXI_DATA_WIDTH = 32'd0,
  /// AXI4+ATOP user width
  parameter int unsigned                  AXI_USER_WIDTH = 32'd0,
  /// Number of memory banks / macros
  /// Has to satisfy:
  /// - MemNumBanks >= 2 * AxiDataWidth / MemDataWidth
  /// - MemNumBanks is a power of 2.
  parameter int unsigned                  MEM_NUM_BANKS  = 32'd4,
  /// Address width of an individual memory bank.
  parameter int unsigned                  MEM_ADDR_WIDTH = 32'd11,
  /// Data width of the memory macros.
  /// Has to satisfy:
  /// - AxiDataWidth % MemDataWidth = 0
  parameter int unsigned                  MEM_DATA_WIDTH = 32'd32,
  /// Read latency of the connected memory in cycles
  parameter int unsigned                  MEM_LATENCY    = 32'd1,
  /// Hide write requests if the strb == '0
  parameter bit                           HIDE_STRB      = 1'b0,
  /// Depth of output fifo/fall_through_register. Increase for asymmetric backpressure (contention) on banks.
  parameter int unsigned                  OUT_FIFO_DEPTH = 32'd1,
  // DEPENDENT PARAMETERS, DO NOT OVERWRITE!
  parameter type mem_addr_t = logic [MEM_ADDR_WIDTH-1:0],
  parameter type mem_atop_t = logic [5:0],
  parameter type mem_data_t = logic [MEM_DATA_WIDTH-1:0],
  parameter type mem_strb_t = logic [MEM_DATA_WIDTH/8-1:0]
) (
  /// Clock
  input  logic                          clk_i,
  /// Asynchronous reset, active low
  input  logic                          rst_ni,
  /// Testmode enable
  input  logic                          test_i,
  /// AXI4+ATOP slave port
  AXI_BUS.Slave                         slv,
  /// Memory bank request
  output logic      [MEM_NUM_BANKS-1:0] mem_req_o,
  /// Memory request grant
  input  logic      [MEM_NUM_BANKS-1:0] mem_gnt_i,
  /// Request address
  output mem_addr_t [MEM_NUM_BANKS-1:0] mem_add_o,
  /// Write request enable, active high
  output logic      [MEM_NUM_BANKS-1:0] mem_we_o,
  /// Write data
  output mem_data_t [MEM_NUM_BANKS-1:0] mem_wdata_o,
  /// Write data byte enable, active high
  output mem_strb_t [MEM_NUM_BANKS-1:0] mem_be_o,
  /// Atomic operation
  output mem_atop_t [MEM_NUM_BANKS-1:0] mem_atop_o,
  /// Read data response
  input  mem_data_t [MEM_NUM_BANKS-1:0] mem_rdata_i,
  /// Status output, busy flag of `axi_to_mem`
  output logic      [1:0]               axi_to_mem_busy_o
);
  typedef logic [AXI_ID_WIDTH-1:0]     id_t;
  typedef logic [AXI_ADDR_WIDTH-1:0]   addr_t;
  typedef logic [AXI_DATA_WIDTH-1:0]   data_t;
  typedef logic [AXI_DATA_WIDTH/8-1:0] strb_t;
  typedef logic [AXI_USER_WIDTH-1:0]   user_t;
  `AXI_TYPEDEF_AW_CHAN_T(aw_chan_t, addr_t, id_t, user_t)
  `AXI_TYPEDEF_W_CHAN_T(w_chan_t, data_t, strb_t, user_t)
  `AXI_TYPEDEF_B_CHAN_T(b_chan_t, id_t, user_t)
  `AXI_TYPEDEF_AR_CHAN_T(ar_chan_t, addr_t, id_t, user_t)
  `AXI_TYPEDEF_R_CHAN_T(r_chan_t, data_t, id_t, user_t)
  `AXI_TYPEDEF_REQ_T(axi_req_t, aw_chan_t, w_chan_t, ar_chan_t)
  `AXI_TYPEDEF_RESP_T(axi_resp_t, b_chan_t, r_chan_t)

  axi_req_t  mem_axi_req;
  axi_resp_t mem_axi_resp;

  `AXI_ASSIGN_TO_REQ(mem_axi_req, slv)
  `AXI_ASSIGN_FROM_RESP(slv, mem_axi_resp)

  axi_to_mem_banked #(
    .AxiIdWidth    ( AXI_ID_WIDTH               ),
    .AxiAddrWidth  ( AXI_ADDR_WIDTH             ),
    .AxiDataWidth  ( AXI_DATA_WIDTH             ),
    .axi_aw_chan_t ( aw_chan_t                  ),
    .axi_w_chan_t  (  w_chan_t                  ),
    .axi_b_chan_t  (  b_chan_t                  ),
    .axi_ar_chan_t ( ar_chan_t                  ),
    .axi_r_chan_t  (  r_chan_t                  ),
    .axi_req_t     ( axi_req_t                  ),
    .axi_resp_t    ( axi_resp_t                 ),
    .MemNumBanks   ( MEM_NUM_BANKS              ),
    .MemAddrWidth  ( MEM_ADDR_WIDTH             ),
    .MemDataWidth  ( MEM_DATA_WIDTH             ),
    .MemLatency    ( MEM_LATENCY                ),
    .HideStrb      ( HIDE_STRB                  ),
    .OutFifoDepth  ( OUT_FIFO_DEPTH             )
  ) i_axi_to_mem_banked (
    .clk_i,
    .rst_ni,
    .test_i,
    .axi_to_mem_busy_o,
    .axi_req_i      ( mem_axi_req  ),
    .axi_resp_o     ( mem_axi_resp ),
    .mem_req_o,
    .mem_gnt_i,
    .mem_add_o,
    .mem_wdata_o,
    .mem_be_o,
    .mem_atop_o,
    .mem_we_o,
    .mem_rdata_i
  );

// pragma translate_off
`ifndef VERILATOR
  initial begin: p_assertions
    assert (AXI_ADDR_WIDTH  >= 1) else $fatal(1, "AXI address width must be at least 1!");
    assert (AXI_DATA_WIDTH  >= 1) else $fatal(1, "AXI data width must be at least 1!");
    assert (AXI_ID_WIDTH    >= 1) else $fatal(1, "AXI ID   width must be at least 1!");
    assert (AXI_USER_WIDTH  >= 1) else $fatal(1, "AXI user width must be at least 1!");
  end
`endif
// pragma translate_on
endmodule


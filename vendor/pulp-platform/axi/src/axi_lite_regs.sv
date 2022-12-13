// Copyright (c) 2020 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// Authors:
// - Wolfgang Roenninger <wroennin@iis.ee.ethz.ch>
// - Andreas Kurth <akurth@iis.ee.ethz.ch>

`include "axi/typedef.svh"
`include "common_cells/registers.svh"

/// AXI4-Lite registers with optional read-only and protection features.
///
/// This module contains a parametrizable number of bytes in flip-flops (FFs) and makes them
/// accessible on two interfaces:
/// - as memory-mapped AXI4-Lite slave (ports `axi_req_i` and `axi_resp_o`), and
/// - as wires to directly attach other hardware logic (ports `reg_d_i`, `reg_load_i`, `reg_q_o`,
///   `wr_active_o`, `rd_active_o`).
///
/// ## Address Map
///
/// The address range covered by this module is defined by `RegNumBytes`.  The base address of this
/// module *must* be aligned to `RegNumBytes`.  The first byte is accessible at offset `0`, the last
/// byte is accessible at offset `RegNumBytes-1`.  The slice `[$clog2(RegNumBytes)-1:0]` of a given
/// address is used to decode the accessed byte within this module.  Address bits outside that slice
/// are ignored.  Accesses to addresses within the slice but with an offset above the last byte are
/// responded with `SLVERR`.
///
/// ## Read-Only Bytes
///
/// Any set of bytes can be configured as read-only by setting the `AxiReadOnly` parameter
/// accordingly.  A read-only byte cannot be written via the AXI interface, but it can be changed
/// from the logic interface.
///
/// When one or multiple bytes in a write transaction are read-only, they are not modified.  A write
/// transaction is responded with `OKAY` if it wrote at least one byte.  Write transactions / that
/// have `wstrb` set *only* for read-only bytes are responded with `SLVERR`.
///
/// This read-only mechanism can be used to expose constants (lookup-table data) as follows.
///
/// ### Exposing Constants
///
/// To make a byte with constant value (e.g., implemented as LUT instead of FF after synthesis)
/// readable from the AXI4-Lite port:
/// - Make the byte read-only from the AXI4-Lite port by setting its `AxiReadOnly` bit to `1`.
/// - Disable loading the byte from logic by driving its `reg_load_i` bit to `0`.
/// - Define the value of the byte by setting its `RegRstVal` entry.
///
/// ## Protection
///
/// This module can be configured to only allow *privileged* and/or *secure* accesses (see A4.7
/// of the AXI4 specification) by setting the `PrivProtOnly` and/or `SecuProtOnly` parameter,
/// respectively.
module axi_lite_regs #(
  /// The size of the register field in bytes.
  parameter int unsigned RegNumBytes = 32'd0,
  /// Address width of the AXI4-Lite port.
  ///
  /// The minimum value of this parameter is `$clog2(RegNumBytes)`.
  parameter int unsigned AxiAddrWidth = 32'd0,
  /// Data width of the AXI4-Lite port.
  parameter int unsigned AxiDataWidth = 32'd0,
  /// Only allow *privileged* accesses on the AXI4-Lite port.
  ///
  /// If this parameter is set to `1`, this module only allows reads and writes that have the
  /// `AxProt[0]` bit set.  If a transaction does not have the `AxProt[0]` bit set, this module
  /// replies with `SLVERR` and does not read or write register data.
  parameter bit PrivProtOnly = 1'b0,
  /// Only allow *secure* accesses on the AXI4-Lite port.
  ///
  /// If this parameter is set to `1`, this module only allows reads and writes that have the
  /// `AxProt[1]` bit set.  If a transaction does not have the `AxProt[1]` bit set, this module
  /// replies with `SLVERR` and does not read or write register data.
  parameter bit SecuProtOnly = 1'b0,
  /// Define individual bytes as *read-only from the AXI4-Lite port*.
  ///
  /// This parameter is an array with one bit for each byte.  If that bit is `0`, the byte can be
  /// read and written on the AXI4-Lite port; if that bit is `1`, the byte can only be read on the
  /// AXI4-Lite port.
  parameter logic [RegNumBytes-1:0] AxiReadOnly = {RegNumBytes{1'b0}},
  /// Constant (=**do not overwrite!**); type of a byte is 8 bit.
  parameter type byte_t = logic [7:0],
  /// Reset value for the whole register array.
  ///
  /// This parameter is an array with one byte value for each byte.  At reset, each byte is
  /// assigned its value from this array.
  parameter byte_t [RegNumBytes-1:0] RegRstVal = {RegNumBytes{8'h00}},
  /// Request struct of the AXI4-Lite port.
  parameter type req_lite_t = logic,
  /// Response struct of the AXI4-Lite port.
  parameter type resp_lite_t = logic
) (
  /// Rising-edge clock of all ports
  input  logic clk_i,
  /// Asynchronous reset, active low
  input  logic rst_ni,
  /// AXI4-Lite slave request
  input  req_lite_t axi_req_i,
  /// AXI4-Lite slave response
  output resp_lite_t axi_resp_o,
  /// Signals that a byte is being written from the AXI4-Lite port in the current clock cycle.  This
  /// signal is asserted regardless of the value of `AxiReadOnly` and can therefore be used by
  /// surrounding logic to react to write-on-read-only-byte errors.
  output logic [RegNumBytes-1:0] wr_active_o,
  /// Signals that a byte is being read from the AXI4-Lite port in the current clock cycle.
  output logic [RegNumBytes-1:0] rd_active_o,
  /// Input value of each byte.  If `reg_load_i` is `1` for a byte in the current clock cycle, the
  /// byte register in this module is set to the value of the byte in `reg_d_i` at the next clock
  /// edge.
  input  byte_t [RegNumBytes-1:0] reg_d_i,
  /// Load enable of each byte.
  ///
  /// If `reg_load_i` is `1` for a byte defined as non-read-only in a clock cycle, an AXI4-Lite
  /// write transaction is stalled when it tries to write the same byte.  That is, a write
  /// transaction is stalled if all of the following conditions are true for the byte at index `i`:
  /// - `AxiReadOnly[i]` is `0`,
  /// - `reg_load_i[i]` is `1`,
  /// - the bit in `axi_req_i.w.strb` that affects the byte is `1`.
  ///
  /// If unused, set this input to `'0`.
  input  logic  [RegNumBytes-1:0] reg_load_i,
  /// The registered value of each byte.
  output byte_t [RegNumBytes-1:0] reg_q_o
);

  // Define the number of register chunks needed to map all `RegNumBytes` to the AXI channel.
  // Eg: `AxiDataWidth == 32'd32`
  // AXI strb:                       3 2 1 0
  //                                 | | | |
  //             *---------*---------* | | |
  //             | *-------|-*-------|-* | |
  //             | | *-----|-|-*-----|-|-* |
  //             | | | *---|-|-|-*---|-|-|-*
  //             | | | |   | | | |   | | | |
  // Reg byte:   B A 9 8   7 6 5 4   3 2 1 0
  //           | chunk_2 | chunk_1 | chunk_0 |
  localparam int unsigned AxiStrbWidth  = AxiDataWidth / 32'd8;
  localparam int unsigned NumChunks     = cf_math_pkg::ceil_div(RegNumBytes, AxiStrbWidth);
  localparam int unsigned ChunkIdxWidth = (NumChunks > 32'd1) ? $clog2(NumChunks) : 32'd1;
  // Type of the index to identify a specific register chunk.
  typedef logic [ChunkIdxWidth-1:0] chunk_idx_t;

  // Find out how many bits of the address are applicable for this module.
  // Look at the `AddrWidth` number of LSBs to calculate the multiplexer index of the AXI.
  localparam int unsigned AddrWidth = (RegNumBytes > 32'd1) ? ($clog2(RegNumBytes)+1) : 32'd2;
  typedef logic [AddrWidth-1:0] addr_t;

  // Define the address map which maps each register chunk onto an AXI address.
  typedef struct packed {
    int unsigned idx;
    addr_t       start_addr;
    addr_t       end_addr;
  } axi_rule_t;
  axi_rule_t    [NumChunks-1:0] addr_map;
  for (genvar i = 0; i < NumChunks; i++) begin : gen_addr_map
    assign addr_map[i] = axi_rule_t'{
      idx:        i,
      start_addr: addr_t'( i   * AxiStrbWidth),
      end_addr:   addr_t'((i+1)* AxiStrbWidth)
    };
  end

  // Channel definitions for spill register
  typedef logic [AxiDataWidth-1:0] axi_data_t;
  `AXI_LITE_TYPEDEF_B_CHAN_T(b_chan_lite_t)
  `AXI_LITE_TYPEDEF_R_CHAN_T(r_chan_lite_t, axi_data_t)

  // Register array declarations
  byte_t [RegNumBytes-1:0] reg_q,        reg_d;
  logic  [RegNumBytes-1:0] reg_update;

  // Write logic
  chunk_idx_t              aw_chunk_idx;
  logic                    aw_dec_valid;
  b_chan_lite_t            b_chan;
  logic                    b_valid,      b_ready;
  logic                    aw_prot_ok;
  logic                    chunk_loaded, chunk_ro;

  // Flag for telling that the protection level is the right one.
  assign aw_prot_ok = (PrivProtOnly ? axi_req_i.aw.prot[0] : 1'b1) &
                      (SecuProtOnly ? axi_req_i.aw.prot[1] : 1'b1);
  // Have a flag which is true if any of the bytes inside a chunk are directly loaded.
  logic [AxiStrbWidth-1:0] load;
  logic [AxiStrbWidth-1:0] read_only;
  // Address of the lowest byte byte of a chunk accessed by an AXI write transaction.
  addr_t byte_w_addr;
  assign byte_w_addr = addr_t'(aw_chunk_idx * AxiStrbWidth);

  for (genvar i = 0; i < AxiStrbWidth; i++) begin : gen_load_assign
    // Indexed byte address
    addr_t reg_w_idx;
    assign reg_w_idx = byte_w_addr + addr_t'(i);
    // Only assert load flag for non read only bytes.
    assign load[i]      = (reg_w_idx < RegNumBytes) ?
        (reg_load_i[reg_w_idx] && !AxiReadOnly[reg_w_idx]) : 1'b0;
    // Flag to find out that all bytes of the chunk are read only.
    assign read_only[i] = (reg_w_idx < RegNumBytes) ? AxiReadOnly[reg_w_idx] : 1'b1;
  end
  // Only assert the loaded flag if there could be a load conflict between a strobe and load
  // signal.
  assign chunk_loaded = |(load & axi_req_i.w.strb);
  assign chunk_ro     = &read_only;


  // Register write logic.
  always_comb begin
    automatic addr_t reg_byte_idx = '0;
    // default assignments
    reg_d               = reg_q;
    reg_update          = '0;
    // Channel handshake
    axi_resp_o.aw_ready = 1'b0;
    axi_resp_o.w_ready  = 1'b0;
    // Response
    b_chan              = b_chan_lite_t'{resp: axi_pkg::RESP_SLVERR, default: '0};
    b_valid             = 1'b0;
    // write active flag
    wr_active_o         = '0;

    // Control
    // Handle all non AXI register loads.
    for (int unsigned i = 0; i < RegNumBytes; i++) begin
      if (reg_load_i[i]) begin
        reg_d[i]      = reg_d_i[i];
        reg_update[i] = 1'b1;
      end
    end

    // Handle load from AXI write.
    // `b_ready` is allowed to be a condition as it comes from a spill register.
    if (axi_req_i.aw_valid && axi_req_i.w_valid && b_ready) begin
      // The write can be performed when these conditions are true:
      // - AW decode is valid.
      // - `axi_req_i.aw.prot` has the right value.
      if (aw_dec_valid && aw_prot_ok) begin
        // Stall write as long as any direct load is going on in the current chunk.
        // Read-only bytes within a chunk have no influence on stalling.
        if (!chunk_loaded) begin
          // Go through all bytes on the W channel.
          for (int unsigned i = 0; i < AxiStrbWidth; i++) begin
            reg_byte_idx = byte_w_addr + addr_t'(i);
            // Only execute if the byte is mapped onto the register array.
            if (reg_byte_idx < RegNumBytes) begin
              // Only update the reg from an AXI write if it is not `ReadOnly`.
              // Only connect the data and load to the reg, if the byte is written from AXI.
              // This allows for simultaneous direct load onto unwritten bytes.
              if (!AxiReadOnly[reg_byte_idx] && axi_req_i.w.strb[i]) begin
                reg_d[reg_byte_idx]      = axi_req_i.w.data[8*i+:8];
                reg_update[reg_byte_idx] = 1'b1;
              end
              wr_active_o[reg_byte_idx] = axi_req_i.w.strb[i];
            end
          end
          b_chan.resp         = chunk_ro ? axi_pkg::RESP_SLVERR : axi_pkg::RESP_OKAY;
          b_valid             = 1'b1;
          axi_resp_o.aw_ready = 1'b1;
          axi_resp_o.w_ready  = 1'b1;
        end
      end else begin
        // Send default B error response on each not allowed write transaction.
        b_valid             = 1'b1;
        axi_resp_o.aw_ready = 1'b1;
        axi_resp_o.w_ready  = 1'b1;
      end
    end
  end

  // Read logic
  chunk_idx_t   ar_chunk_idx;
  logic         ar_dec_valid;
  r_chan_lite_t r_chan;
  logic         r_valid,      r_ready;
  logic         ar_prot_ok;
  assign ar_prot_ok = (PrivProtOnly ? axi_req_i.ar.prot[0] : 1'b1) &
                      (SecuProtOnly ? axi_req_i.ar.prot[1] : 1'b1);
  // Multiplexer to determine R channel
  always_comb begin
    automatic int unsigned reg_byte_idx = '0;
    // Default R channel throws an error.
    r_chan = r_chan_lite_t'{
      data: axi_data_t'(32'hBA5E1E55),
      resp: axi_pkg::RESP_SLVERR,
      default: '0
    };
    // Default nothing is reading the registers
    rd_active_o = '0;
    // Read is valid on a chunk
    if (ar_dec_valid && ar_prot_ok) begin
      // Calculate the corresponding byte index from `ar_chunk_idx`.
      for (int unsigned i = 0; i < AxiStrbWidth; i++) begin
        reg_byte_idx = unsigned'(ar_chunk_idx) * AxiStrbWidth + i;
        // Guard to not index outside the `reg_q_o` array.
        if (reg_byte_idx < RegNumBytes) begin
          r_chan.data[8*i+:8]       = reg_q_o[reg_byte_idx];
          rd_active_o[reg_byte_idx] = r_valid & r_ready;
        end else begin
          r_chan.data[8*i+:8] = 8'h00;
        end
      end
      r_chan.resp = axi_pkg::RESP_OKAY;
    end
  end

  assign r_valid             = axi_req_i.ar_valid; // to spill register
  assign axi_resp_o.ar_ready = r_ready;            // from spill register

  // Register array mapping, even read only register can be loaded over `reg_load_i`.
  for (genvar i = 0; i < RegNumBytes; i++) begin : gen_rw_regs
    `FFLARN(reg_q[i], reg_d[i], reg_update[i], RegRstVal[i], clk_i, rst_ni)
    assign reg_q_o[i] = reg_q[i];
  end

  addr_decode #(
    .NoIndices ( NumChunks  ),
    .NoRules   ( NumChunks  ),
    .addr_t    ( addr_t     ),
    .rule_t    ( axi_rule_t )
  ) i_aw_decode (
    .addr_i           ( addr_t'(axi_req_i.aw.addr) ), // Only look at the `AddrWidth` LSBs.
    .addr_map_i       ( addr_map                   ),
    .idx_o            ( aw_chunk_idx               ),
    .dec_valid_o      ( aw_dec_valid               ),
    .dec_error_o      ( /*not used*/               ),
    .en_default_idx_i ( '0                         ),
    .default_idx_i    ( '0                         )
  );

  addr_decode #(
    .NoIndices ( NumChunks  ),
    .NoRules   ( NumChunks  ),
    .addr_t    ( addr_t     ),
    .rule_t    ( axi_rule_t )
  ) i_ar_decode (
    .addr_i           ( addr_t'(axi_req_i.ar.addr) ), // Only look at the `AddrWidth` LSBs.
    .addr_map_i       ( addr_map                   ),
    .idx_o            ( ar_chunk_idx               ),
    .dec_valid_o      ( ar_dec_valid               ),
    .dec_error_o      ( /*not used*/               ),
    .en_default_idx_i ( '0                         ),
    .default_idx_i    ( '0                         )
  );

  // Add a cycle delay on AXI response, cut all comb paths between slave port inputs and outputs.
  spill_register #(
    .T      ( b_chan_lite_t ),
    .Bypass ( 1'b0          )
  ) i_b_spill_register (
    .clk_i,
    .rst_ni,
    .valid_i ( b_valid            ),
    .ready_o ( b_ready            ),
    .data_i  ( b_chan             ),
    .valid_o ( axi_resp_o.b_valid ),
    .ready_i ( axi_req_i.b_ready  ),
    .data_o  ( axi_resp_o.b       )
  );

  // Add a cycle delay on AXI response, cut all comb paths between slave port inputs and outputs.
  spill_register #(
    .T      ( r_chan_lite_t ),
    .Bypass ( 1'b0          )
  ) i_r_spill_register (
    .clk_i,
    .rst_ni,
    .valid_i ( r_valid            ),
    .ready_o ( r_ready            ),
    .data_i  ( r_chan             ),
    .valid_o ( axi_resp_o.r_valid ),
    .ready_i ( axi_req_i.r_ready  ),
    .data_o  ( axi_resp_o.r       )
  );

  // Validate parameters.
  // pragma translate_off
  `ifndef VERILATOR
    initial begin: p_assertions
      assert (RegNumBytes > 32'd0) else
          $fatal(1, "The number of bytes must be at least 1!");
      assert (AxiAddrWidth >= AddrWidth) else
          $fatal(1, "AxiAddrWidth is not wide enough, has to be at least %0d-bit wide!", AddrWidth);
      assert ($bits(axi_req_i.aw.addr) == AxiAddrWidth) else
          $fatal(1, "AddrWidth does not match req_i.aw.addr!");
      assert ($bits(axi_req_i.ar.addr) == AxiAddrWidth) else
          $fatal(1, "AddrWidth does not match req_i.ar.addr!");
      assert (AxiDataWidth == $bits(axi_req_i.w.data)) else
          $fatal(1, "AxiDataWidth has to be: AxiDataWidth == $bits(axi_req_i.w.data)!");
      assert (AxiDataWidth == $bits(axi_resp_o.r.data)) else
          $fatal(1, "AxiDataWidth has to be: AxiDataWidth == $bits(axi_resp_o.r.data)!");
      assert (RegNumBytes == $bits(AxiReadOnly)) else
          $fatal(1, "Each register needs a `ReadOnly` flag!");
    end
    default disable iff (~rst_ni);
    for (genvar i = 0; i < RegNumBytes; i++) begin
      assert property (@(posedge clk_i) (!reg_load_i[i] && AxiReadOnly[i] |=> $stable(reg_q_o[i])))
          else $fatal(1, "Read-only register at `byte_index: %0d` was changed by AXI!", i);
    end
  `endif
  // pragma translate_on
endmodule


`include "axi/assign.svh"
/// Interface variant of [`axi_lite_regs`](module.axi_lite_regs).
///
/// See the documentation of the main module for the definition of ports and parameters.
module axi_lite_regs_intf #(
  parameter type byte_t = logic [7:0],
  parameter int unsigned                REG_NUM_BYTES  = 32'd0,
  parameter int unsigned                AXI_ADDR_WIDTH = 32'd0,
  parameter int unsigned                AXI_DATA_WIDTH = 32'd0,
  parameter bit                         PRIV_PROT_ONLY = 1'd0,
  parameter bit                         SECU_PROT_ONLY = 1'd0,
  parameter logic  [REG_NUM_BYTES-1:0]  AXI_READ_ONLY = {REG_NUM_BYTES{1'b0}},
  parameter byte_t [REG_NUM_BYTES-1:0]  REG_RST_VAL = {REG_NUM_BYTES{8'h00}}
) (
  input  logic                      clk_i,
  input  logic                      rst_ni,
  AXI_LITE.Slave                    slv,
  output logic  [REG_NUM_BYTES-1:0] wr_active_o,
  output logic  [REG_NUM_BYTES-1:0] rd_active_o,
  input  byte_t [REG_NUM_BYTES-1:0] reg_d_i,
  input  logic  [REG_NUM_BYTES-1:0] reg_load_i,
  output byte_t [REG_NUM_BYTES-1:0] reg_q_o
);

  typedef logic [AXI_ADDR_WIDTH-1:0]   addr_t;
  typedef logic [AXI_DATA_WIDTH-1:0]   data_t;
  typedef logic [AXI_DATA_WIDTH/8-1:0] strb_t;
  `AXI_LITE_TYPEDEF_AW_CHAN_T(aw_chan_lite_t, addr_t)
  `AXI_LITE_TYPEDEF_W_CHAN_T(w_chan_lite_t, data_t, strb_t)
  `AXI_LITE_TYPEDEF_B_CHAN_T(b_chan_lite_t)
  `AXI_LITE_TYPEDEF_AR_CHAN_T(ar_chan_lite_t, addr_t)
  `AXI_LITE_TYPEDEF_R_CHAN_T(r_chan_lite_t, data_t)
  `AXI_LITE_TYPEDEF_REQ_T(req_lite_t, aw_chan_lite_t, w_chan_lite_t, ar_chan_lite_t)
  `AXI_LITE_TYPEDEF_RESP_T(resp_lite_t, b_chan_lite_t, r_chan_lite_t)

  req_lite_t  axi_lite_req;
  resp_lite_t axi_lite_resp;

  `AXI_LITE_ASSIGN_TO_REQ(axi_lite_req, slv)
  `AXI_LITE_ASSIGN_FROM_RESP(slv, axi_lite_resp)

  axi_lite_regs #(
    .RegNumBytes  ( REG_NUM_BYTES  ),
    .AxiAddrWidth ( AXI_ADDR_WIDTH ),
    .AxiDataWidth ( AXI_DATA_WIDTH ),
    .PrivProtOnly ( PRIV_PROT_ONLY ),
    .SecuProtOnly ( SECU_PROT_ONLY ),
    .AxiReadOnly  ( AXI_READ_ONLY  ),
    .RegRstVal    ( REG_RST_VAL    ),
    .req_lite_t   ( req_lite_t     ),
    .resp_lite_t  ( resp_lite_t    )
  ) i_axi_lite_regs (
    .clk_i,
    .rst_ni,
    .axi_req_i   ( axi_lite_req  ),
    .axi_resp_o  ( axi_lite_resp ),
    .wr_active_o,
    .rd_active_o,
    .reg_d_i,
    .reg_load_i,
    .reg_q_o
  );

  // Validate parameters.
  // pragma translate_off
  `ifndef VERILATOR
    initial begin: p_assertions
      assert (AXI_ADDR_WIDTH == $bits(slv.aw_addr))
          else $fatal(1, "AXI_ADDR_WIDTH does not match slv interface!");
      assert (AXI_DATA_WIDTH == $bits(slv.w_data))
          else $fatal(1, "AXI_DATA_WIDTH does not match slv interface!");
    end
  `endif
  // pragma translate_on
endmodule

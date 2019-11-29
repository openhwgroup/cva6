// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

////////////////////////////////////////////////////////////////////////////////
// Engineer:       Andreas Traber - atraber@iis.ee.ethz.ch                    //
//                                                                            //
// Design Name:    Fetch Fifo for 32 bit memory interface                     //
// Project Name:   RI5CY                                                      //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Buffer to store instructions.                              //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

// input port: send address one cycle before the data
// clear_i clears the FIFO for the following cycle. in_addr_i can be sent in
// this cycle already
module riscv_fetch_fifo
(
    input  logic        clk,
    input  logic        rst_n,

    // control signals
    input  logic        clear_i,          // clears the contents of the fifo

    // input port
    input  logic [31:0] in_addr_i,
    input  logic [31:0] in_rdata_i,
    input  logic        in_valid_i,
    output logic        in_ready_o,

    input  logic        in_replace2_i, // replaces second entry if there is one: "to be served after this instr"
    input  logic        in_is_hwlp_i,

    // output port
    output logic        out_valid_o,
    input  logic        out_ready_i,
    output logic [31:0] out_rdata_o,
    output logic [31:0] out_addr_o,
    output logic        unaligned_is_compressed_o,
    output logic        out_valid_stored_o, // same as out_valid_o, except that if something is incoming now it is not included. This signal is available immediately as it comes directly out of FFs
    output logic        out_is_hwlp_o
  );

  localparam DEPTH = 4; // must be 3 or greater

  // index 0 is used for output
  logic [0:DEPTH-1] [31:0]  addr_n,    addr_int,    addr_Q;
  logic [0:DEPTH-1] [31:0]  rdata_n,   rdata_int,   rdata_Q;
  logic [0:DEPTH-1]         valid_n,   valid_int,   valid_Q;
  logic [0:1      ]         is_hwlp_n, is_hwlp_int, is_hwlp_Q;

  logic             [31:0]  addr_next;
  logic             [31:0]  rdata, rdata_unaligned;
  logic                     valid, valid_unaligned;

  logic                     aligned_is_compressed, unaligned_is_compressed;
  logic                     aligned_is_compressed_st, unaligned_is_compressed_st;

  //////////////////////////////////////////////////////////////////////////////
  // output port
  //////////////////////////////////////////////////////////////////////////////


  assign rdata = (valid_Q[0]) ? rdata_Q[0] : ( in_rdata_i & {32{in_valid_i}} );
  assign valid = valid_Q[0] || in_valid_i || is_hwlp_Q[1];

  assign rdata_unaligned = (valid_Q[1]) ? {rdata_Q[1][15:0], rdata[31:16]} : {in_rdata_i[15:0], rdata[31:16]};
  // it is implied that rdata_valid_Q[0] is set
  assign valid_unaligned = (valid_Q[1] || (valid_Q[0] && in_valid_i));

  assign unaligned_is_compressed_o  = unaligned_is_compressed;

  assign unaligned_is_compressed    = rdata[17:16] != 2'b11;
  assign aligned_is_compressed      = rdata[1:0] != 2'b11;
  assign unaligned_is_compressed_st = valid_Q[0] && rdata_Q[0][17:16] != 2'b11;
  assign aligned_is_compressed_st   = valid_Q[0] && rdata_Q[0][1:0] != 2'b11;

  //////////////////////////////////////////////////////////////////////////////
  // instruction aligner (if unaligned)
  //////////////////////////////////////////////////////////////////////////////

  always_comb
  begin
    // serve the aligned case even though the output address is unaligned when
    // the next instruction will be from a hardware loop target
    // in this case the current instruction is already prealigned in element 0
    if (out_addr_o[1] && (~is_hwlp_Q[1])) begin
      // unaligned case
      out_rdata_o = rdata_unaligned;

      if (unaligned_is_compressed)
        out_valid_o = valid;
      else
        out_valid_o = valid_unaligned;
    end else begin
      // aligned case
      out_rdata_o = rdata;
      out_valid_o = valid;
    end
  end

  assign out_addr_o    = (valid_Q[0]) ? addr_Q[0] : in_addr_i;
  assign out_is_hwlp_o = (valid_Q[0]) ? is_hwlp_Q[0] : in_is_hwlp_i;

  // this valid signal must not depend on signals from outside!
  always_comb
  begin
    out_valid_stored_o = 1'b1;

    if (out_addr_o[1] && (~is_hwlp_Q[1])) begin
      if (unaligned_is_compressed_st)
        out_valid_stored_o = 1'b1;
      else
        out_valid_stored_o = valid_Q[1];
    end else begin
      out_valid_stored_o = valid_Q[0];
    end
  end


  //////////////////////////////////////////////////////////////////////////////
  // input port
  //////////////////////////////////////////////////////////////////////////////

  // we accept data as long as our fifo is not full
  // we don't care about clear here as the data will be received one cycle
  // later anyway
  assign in_ready_o = ~valid_Q[DEPTH-2];


  //////////////////////////////////////////////////////////////////////////////
  // FIFO management
  //////////////////////////////////////////////////////////////////////////////

  always_comb
  begin
    addr_int    = addr_Q;
    rdata_int   = rdata_Q;
    valid_int   = valid_Q;
    is_hwlp_int = is_hwlp_Q;

    if (in_valid_i) begin
      for(int j = 0; j < DEPTH; j++) begin
        if (~valid_Q[j]) begin
          addr_int[j]  = in_addr_i;
          rdata_int[j] = in_rdata_i;
          valid_int[j] = 1'b1;

          break;
        end
      end

      // replace 2nd entry
      if (in_replace2_i) begin
        if (valid_Q[0]) begin
          addr_int[1]          = in_addr_i;

          // if we replace the 2nd entry, let's cache the output word in case we
          // still need it and it would span two words in the FIFO
          rdata_int[0]         = out_rdata_o;
          rdata_int[1]         = in_rdata_i;
          valid_int[1]         = 1'b1;
          valid_int[2:DEPTH-1] = '0;

          // hardware loop incoming?
          is_hwlp_int[1] = in_is_hwlp_i;
        end else begin
          is_hwlp_int[0] = in_is_hwlp_i;
        end
      end
    end
  end

  assign addr_next = {addr_int[0][31:2], 2'b00} + 32'h4;

  // move everything by one step
  always_comb
  begin
    addr_n     = addr_int;
    rdata_n    = rdata_int;
    valid_n    = valid_int;
    is_hwlp_n  = is_hwlp_int;

    if (out_ready_i && out_valid_o) begin
      is_hwlp_n = {is_hwlp_int[1], 1'b0};

      if (is_hwlp_int[1]) begin
        addr_n[0] = addr_int[1][31:0];
        for (int i = 0; i < DEPTH - 1; i++)
        begin
          rdata_n[i] = rdata_int[i + 1];
        end
        rdata_n[DEPTH - 1] = 32'b0;
        valid_n   = {valid_int[1:DEPTH-1], 1'b0};
      end else begin
        if (addr_int[0][1]) begin
          // unaligned case
          if (unaligned_is_compressed) begin
            addr_n[0] = {addr_next[31:2], 2'b00};
          end else begin
            addr_n[0] = {addr_next[31:2], 2'b10};
          end
          for (int i = 0; i < DEPTH - 1; i++)
          begin
            rdata_n[i] = rdata_int[i + 1];
          end
          rdata_n[DEPTH - 1] = 32'b0;
          valid_n  = {valid_int[1:DEPTH-1], 1'b0};
        end else begin
          // aligned case
          if (aligned_is_compressed) begin
            // just increase address, do not move to next entry in FIFO
            addr_n[0] = {addr_int[0][31:2], 2'b10};
          end else begin
            // move to next entry in FIFO
            addr_n[0] = {addr_next[31:2], 2'b00};
            for (int i = 0; i < DEPTH - 1; i++)
            begin
              rdata_n[i] = rdata_int[i + 1];
            end
            rdata_n[DEPTH - 1] = 32'b0;
            valid_n   = {valid_int[1:DEPTH-1], 1'b0};
          end
        end
      end
    end
  end

  //////////////////////////////////////////////////////////////////////////////
  // registers
  //////////////////////////////////////////////////////////////////////////////

  always_ff @(posedge clk, negedge rst_n)
  begin
    if(rst_n == 1'b0)
    begin
      addr_Q    <= '{default: '0};
      rdata_Q   <= '{default: '0};
      valid_Q   <= '0;
      is_hwlp_Q <= '0;
    end
    else
    begin
      // on a clear signal from outside we invalidate the content of the FIFO
      // completely and start from an empty state
      if (clear_i) begin
        valid_Q    <= '0;
        is_hwlp_Q  <= '0;
      end else begin
        addr_Q    <= addr_n;
        rdata_Q   <= rdata_n;
        valid_Q   <= valid_n;
        is_hwlp_Q <= is_hwlp_n;
      end
    end
  end

  //----------------------------------------------------------------------------
  // Assertions
  //----------------------------------------------------------------------------

  // check for FIFO overflows
  // assert property (
  //   @(posedge clk) (in_valid_i) |-> ((valid_Q[DEPTH-1] == 1'b0) || (clear_i == 1'b1) || (in_replace2_i == 1'b1)) );

endmodule
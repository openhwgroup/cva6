////////////////////////////////////////////////////////////////////////////////
// Copyright (C) 2017 ETH Zurich, University of Bologna                       //
// All rights reserved.                                                       //
//                                                                            //
// This code is under development and not yet released to the public.         //
// Until it is released, the code is under the copyright of ETH Zurich        //
// and the University of Bologna, and may contain unpublished work.           //
// Any reuse/redistribution should only be under explicit permission.         //
//                                                                            //
// Bug fixes and contributions will eventually be released under the          //
// SolderPad open hardware license and under the copyright of ETH Zurich      //
// and the University of Bologna.                                             //
//                                                                            //
// Engineer:       Andreas Traber - atraber@iis.ee.ethz.ch                    //
//                                                                            //
// Design Name:    Fetch Fifo for 32 bit memory interface                     //
// Project Name:   zero-riscy                                                 //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Fetch fifo                                                 //
////////////////////////////////////////////////////////////////////////////////

import ariane_pkg::*;

// input port: send address one cycle before the data
// clear_i clears the FIFO for the following cycle. in_addr_i can be sent in
// this cycle already
module fetch_fifo
(
    input  logic        clk,
    input  logic        rst_n,

    // control signals
    input  logic        clear_i,          // clears the contents of the fifo

    // input port
    input  logic [63:0] in_addr_i,
    input  logic [31:0] in_rdata_i,
    input  logic        in_valid_i,
    output logic        in_ready_o,

    // output port
    output logic [63:0] out_addr_o,
    output logic [31:0] out_rdata_o,
    output logic        out_valid_o,
    input  logic        out_ready_i,

    output logic        out_valid_stored_o // same as out_valid_o, except that if something is incoming now it is not
                                           // included. This signal is available immediately as it comes directly out of FFs
  );

  localparam DEPTH = 3; // must be 3 or greater
  /* verilator lint_off LITENDIAN */
  // index 0 is used for output
  logic [0:DEPTH-1] [63:0]  addr_n,    addr_int,    addr_Q;
  logic [0:DEPTH-1] [31:0]  rdata_n,   rdata_int,   rdata_Q;
  logic [0:DEPTH-1]         valid_n,   valid_int,   valid_Q;

  logic             [63:0]  addr_next;
  logic             [31:0]  rdata, rdata_unaligned;
  logic                     valid, valid_unaligned;

  logic                     aligned_is_compressed, unaligned_is_compressed;
  logic                     aligned_is_compressed_st, unaligned_is_compressed_st;
  /* lint_on */
  //----------------------------------------------------------------------------
  // output port
  //----------------------------------------------------------------------------


  assign rdata = (valid_Q[0]) ? rdata_Q[0] : in_rdata_i;
  assign valid = valid_Q[0] || in_valid_i;

  assign rdata_unaligned = (valid_Q[1]) ? {rdata_Q[1][15:0], rdata[31:16]} : {in_rdata_i[15:0], rdata[31:16]};
  // it is implied that rdata_valid_Q[0] is set
  assign valid_unaligned = (valid_Q[1] || (valid_Q[0] && in_valid_i));

  assign unaligned_is_compressed    = rdata[17:16] != 2'b11;
  assign aligned_is_compressed      = rdata[1:0] != 2'b11;
  assign unaligned_is_compressed_st = rdata_Q[0][17:16] != 2'b11;
  assign aligned_is_compressed_st   = rdata_Q[0][1:0] != 2'b11;

  //----------------------------------------------------------------------------
  // instruction aligner (if unaligned)
  //----------------------------------------------------------------------------

  always_comb
  begin
    // serve the aligned case even though the output address is unaligned when
    // the next instruction will be from a hardware loop target
    // in this case the current instruction is already prealigned in element 0
    if (out_addr_o[1]) begin
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

  // this valid signal must not depend on signals from outside!
  always_comb
  begin
    out_valid_stored_o = 1'b1;

    if (out_addr_o[1]) begin
      if (unaligned_is_compressed_st)
        out_valid_stored_o = 1'b1;
      else
        out_valid_stored_o = valid_Q[1];
    end else begin
      out_valid_stored_o = valid_Q[0];
    end
  end


  //----------------------------------------------------------------------------
  // input port
  //----------------------------------------------------------------------------

  // we accept data as long as our fifo is not full
  // we don't care about clear here as the data will be received one cycle
  // later anyway
  assign in_ready_o = ~valid_Q[DEPTH-2];


  //----------------------------------------------------------------------------
  // FIFO management
  //----------------------------------------------------------------------------

  int j;
  always_comb
  begin
    addr_int    = addr_Q;
    rdata_int   = rdata_Q;
    valid_int   = valid_Q;


    if (in_valid_i) begin
      for(j = 0; j < DEPTH; j++) begin
        if (~valid_Q[j]) begin
          addr_int[j]  = in_addr_i;
          rdata_int[j] = in_rdata_i;
          valid_int[j] = 1'b1;

          break;
        end
      end

    end
  end

  assign addr_next = {addr_int[0][63:2], 2'b00} + 64'h4;

  // move everything by one step
  always_comb
  begin
    addr_n     = addr_int;
    rdata_n    = rdata_int;
    valid_n    = valid_int;

    if (out_ready_i && out_valid_o) begin
      begin
        if (addr_int[0][1]) begin
          // unaligned case
          if (unaligned_is_compressed) begin
            addr_n[0] = {addr_next[63:2], 2'b00};
          end else begin
            addr_n[0] = {addr_next[63:2], 2'b10};
          end

          for (int i = 0; i < DEPTH - 1; i++)
          begin
            rdata_n[i] = rdata_int[i + 1];
          end
          rdata_n[DEPTH - 1] = 32'b0;

          valid_n  = {valid_int[1:DEPTH-1], 1'b0};
        end else begin

          if (aligned_is_compressed) begin
            // just increase address, do not move to next entry in FIFO
            addr_n[0] = {addr_int[0][63:2], 2'b10};
          end else begin
            // move to next entry in FIFO
            addr_n[0] = {addr_next[63:2], 2'b00};
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

  //----------------------------------------------------------------------------
  // registers
  //----------------------------------------------------------------------------

  always_ff @(posedge clk, negedge rst_n)
  begin
    if(rst_n == 1'b0)
    begin
      addr_Q    <= '{default: '0};
      rdata_Q   <= '{default: '0};
      valid_Q   <= '0;
    end
    else
    begin
      // on a clear signal from outside we invalidate the content of the FIFO
      // completely and start from an empty state
      if (clear_i) begin
        valid_Q    <= '0;
      end else begin
        addr_Q    <= addr_n;
        rdata_Q   <= rdata_n;
        valid_Q   <= valid_n;
      end
    end
  end

  //----------------------------------------------------------------------------
  // Assertions
  //----------------------------------------------------------------------------
  `ifndef VERILATOR
  assert property (
    @(posedge clk) (in_valid_i) |-> ((valid_Q[DEPTH-1] == 1'b0) || (clear_i == 1'b1)) );
  `endif
endmodule
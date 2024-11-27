// (C) 2001-2024 Intel Corporation. All rights reserved.
// Your use of Intel Corporation's design tools, logic functions and other 
// software and tools, and its AMPP partner logic functions, and any output 
// files from any of the foregoing (including device programming or simulation 
// files), and any associated documentation or information are expressly subject 
// to the terms and conditions of the Intel Program License Subscription 
// Agreement, Intel FPGA IP License Agreement, or other applicable 
// license agreement, including, without limitation, that your use is for the 
// sole purpose of programming logic devices manufactured by Intel and sold by 
// Intel or its authorized distributors.  Please refer to the applicable 
// agreement for further details.


// (C) 2001-2017 Intel Corporation. All rights reserved.
// Your use of Intel Corporation's design tools, logic functions and other 
// software and tools, and its AMPP partner logic functions, and any output 
// files from any of the foregoing (including device programming or simulation 
// files), and any associated documentation or information are expressly subject 
// to the terms and conditions of the Intel Program License Subscription 
// Agreement, Intel FPGA IP License Agreement, or other applicable 
// license agreement, including, without limitation, that your use is for the 
// sole purpose of programming logic devices manufactured by Intel and sold by 
// Intel or its authorized distributors.  Please refer to the applicable 
// agreement for further details.


// (C) 2001-2012 Altera Corporation. All rights reserved.
// Your use of Altera Corporation's design tools, logic functions and other 
// software and tools, and its AMPP partner logic functions, and any output 
// files any of the foregoing (including device programming or simulation 
// files), and any associated documentation or information are expressly subject 
// to the terms and conditions of the Altera Program License Subscription 
// Agreement, Altera MegaCore Function License Agreement, or other applicable 
// license agreement, including, without limitation, that your use is for the 
// sole purpose of programming logic devices manufactured by Altera and sold by 
// Altera or its authorized distributors.  Please refer to the applicable 
// agreement for further details.


// $Id: //acds/rel/24.1/ip/iconnect/merlin/altera_merlin_slave_agent/altera_merlin_burst_uncompressor.sv#1 $
// $Revision: #1 $
// $Date: 2024/02/01 $

// ------------------------------------------
// Merlin Burst Uncompressor
//
// Compressed read bursts -> uncompressed
// ------------------------------------------

`timescale 1 ns / 1 ns

module altera_merlin_burst_uncompressor
#(
    parameter ADDR_W      = 16,
    parameter BURSTWRAP_W = 3,
    parameter BYTE_CNT_W  = 4,
    parameter PKT_SYMBOLS = 4,
    parameter BURST_SIZE_W = 3,
    parameter SYNC_RESET   = 0
)
(
    input clk,
    input reset,
   
    // sink ST signals
    input sink_startofpacket,
    input sink_endofpacket,
    input sink_valid,
    output sink_ready,
   
    // sink ST "data"
    input [ADDR_W - 1: 0] sink_addr,
    input [BURSTWRAP_W - 1 : 0] sink_burstwrap,
    input [BYTE_CNT_W - 1 : 0] sink_byte_cnt,
    input sink_is_compressed,
    input [BURST_SIZE_W-1 : 0] sink_burstsize,
   
    // source ST signals
    output source_startofpacket,
    output source_endofpacket,
    output source_valid,
    input source_ready,
   
    // source ST "data"
    output [ADDR_W - 1: 0] source_addr,
    output [BURSTWRAP_W - 1 : 0] source_burstwrap,
    output [BYTE_CNT_W - 1 : 0] source_byte_cnt,
   
    // Note: in the slave agent, the output should always be uncompressed.  In
    // other applications, it may be required to leave-compressed or not. How to
    // control?  Seems like a simple mux - pass-through if no uncompression is
    // required.
    output source_is_compressed,
    output [BURST_SIZE_W-1 : 0] source_burstsize
);

//----------------------------------------------------
// AXSIZE decoding
//
// Turns the axsize value into the actual number of bytes
// being transferred.
// ---------------------------------------------------
function reg[63:0] bytes_in_transfer;
    input [BURST_SIZE_W-1:0] axsize;
    case (axsize)
        4'b0000: bytes_in_transfer = 64'b0000000000000000000000000000000000000000000000000000000000000001;
        4'b0001: bytes_in_transfer = 64'b0000000000000000000000000000000000000000000000000000000000000010;
        4'b0010: bytes_in_transfer = 64'b0000000000000000000000000000000000000000000000000000000000000100;
        4'b0011: bytes_in_transfer = 64'b0000000000000000000000000000000000000000000000000000000000001000;
        4'b0100: bytes_in_transfer = 64'b0000000000000000000000000000000000000000000000000000000000010000;
        4'b0101: bytes_in_transfer = 64'b0000000000000000000000000000000000000000000000000000000000100000;
        4'b0110: bytes_in_transfer = 64'b0000000000000000000000000000000000000000000000000000000001000000;
        4'b0111: bytes_in_transfer = 64'b0000000000000000000000000000000000000000000000000000000010000000;
        4'b1000: bytes_in_transfer = 64'b0000000000000000000000000000000000000000000000000000000100000000;
        4'b1001: bytes_in_transfer = 64'b0000000000000000000000000000000000000000000000000000001000000000;
        default:bytes_in_transfer = 64'b0000000000000000000000000000000000000000000000000000000000000001;
    endcase

endfunction  

   localparam LG_PKT_SYMBOLS = $clog2(PKT_SYMBOLS);

   // num_symbols is PKT_SYMBOLS, appropriately sized.
   wire [31:0] int_num_symbols = PKT_SYMBOLS;
   wire [BYTE_CNT_W-1:0] num_symbols = int_num_symbols[BYTE_CNT_W-1:0];
  
   // def: Burst Compression.  In a merlin network, a compressed burst is one 
   // which is transmitted in a single beat.  Example: read burst.  In 
   // constrast, an uncompressed burst (example: write burst) is transmitted in
   // one beat per writedata item.
   //
   // For compressed bursts which require response packets, burst
   // uncompression is required.  Concrete example: a read burst of size 8
   // occupies one response-fifo position.  When that fifo position reaches the
   // front of the FIFO, the slave starts providing the required 8 readdatavalid
   // pulses.  The 8 return response beats must be provided in a single packet,
   // with incrementing address and decrementing byte_cnt fields.  Upon receipt
   // of the final readdata item of the burst, the response FIFO item is
   // retired.
   // Burst uncompression logic provides:
   //   a) 2-state FSM (idle, busy)
   //     reset to idle state
   //     transition to busy state for 2nd and subsequent rdv pulses
   //     - a single-cycle burst (aka non-burst read) causes no transition to
   //     busy state.
   //   b) response startofpacket/endofpacket logic.  The response FIFO item 
   //   will have sop asserted, and may have eop asserted. (In the case of
   //   multiple read bursts transmit in the command fabric in a single packet,
   //   the eop assertion will come in a later FIFO item.)  To support packet
   //   conservation, and emit a well-formed packet on the response fabric,
   //     i) response fabric startofpacket is asserted only for the first resp.
   //     beat;
   //     ii) response fabric endofpacket is asserted only for the last resp.
   //     beat.
   //   c) response address field.  The response address field contains an
   //   incrementing sequence, such that each readdata item is associated with
   //   its slave-map location.  N.b. a) computing the address correctly requires
   //   knowledge of burstwrap behavior b) there may be no clients of the address
   //   field, which makes this field a good target for optimization.  See
   //   burst_uncompress_address_counter below.
   //   d) response byte_cnt field.  The response byte_cnt field contains a
   //   decrementing sequence, such that each beat of the response contains the
   //   count of bytes to follow.  In the case of sub-bursts in a single packet,
   //   the byte_cnt field may decrement down to num_symbols, then back up to
   //   some value, multiple times in the packet.
  
   reg burst_uncompress_busy;
   reg [BYTE_CNT_W : LG_PKT_SYMBOLS] burst_uncompress_byte_counter;
   wire [BYTE_CNT_W-1:0] burst_uncompress_byte_counter_lint;
   wire first_packet_beat;
   wire last_packet_beat;

   assign first_packet_beat = sink_valid & ~burst_uncompress_busy;
   assign burst_uncompress_byte_counter_lint = {burst_uncompress_byte_counter[BYTE_CNT_W - 1 : LG_PKT_SYMBOLS], {LG_PKT_SYMBOLS{1'b0}}};

   // First cycle: burst_uncompress_byte_counter isn't ready yet, mux the input to
   // the output.
   assign source_byte_cnt =
     first_packet_beat ? sink_byte_cnt : burst_uncompress_byte_counter_lint;
   assign source_valid = sink_valid;
  
   // Last packet beat is set throughout receipt of an uncompressed read burst
   // from the response FIFO - this forces all the burst uncompression machinery
   // idle.
   assign last_packet_beat = ~sink_is_compressed |
     (
     burst_uncompress_busy ?
       (sink_valid & (burst_uncompress_byte_counter_lint == num_symbols)) :
         sink_valid & (sink_byte_cnt == num_symbols)
     );
 

  // Generation of internal reset synchronization
  reg internal_sclr;
  generate if (SYNC_RESET == 1) begin : rst_syncronizer
      always @ (posedge clk) begin
         internal_sclr <= reset;
      end
  end
  endgenerate

    generate
    if (SYNC_RESET == 0) begin : async_rst0 
      always @(posedge clk or posedge reset) begin
         if (reset) begin
            burst_uncompress_busy <= '0;
         end
         else begin
            if (source_valid & source_ready & sink_valid) begin
               // No matter what the current state, last_packet_beat leads to
               // idle.
               if (last_packet_beat) begin
                  burst_uncompress_busy <= '0;
               end
               else begin
                  burst_uncompress_busy <= 1'b1;
               end
            end
         end
      end
     end // async_rst0
     else begin // sync_rst0
      always @(posedge clk ) begin
         if (internal_sclr) begin
            burst_uncompress_busy <= '0;
         end
         else begin
            if (source_valid & source_ready & sink_valid) begin
               // No matter what the current state, last_packet_beat leads to
               // idle.
               if (last_packet_beat) begin
                  burst_uncompress_busy <= '0;
               end
               else begin
                  burst_uncompress_busy <= 1'b1;
               end
            end
         end
      end
     end // sync_rst0    
   endgenerate
   //always @ (posedge clk) begin
   //   if (source_valid & source_ready & sink_valid) begin
   //      // No matter what the current state, last_packet_beat leads to
   //      // idle.
   //      if (last_packet_beat) begin
   //         burst_uncompress_byte_counter <= '0;
   //      end
   //      else begin
   //         if (burst_uncompress_busy) begin
   //            burst_uncompress_byte_counter <= (burst_uncompress_byte_counter > 0) ? 
   //                                             (burst_uncompress_byte_counter_lint[BYTE_CNT_W-1:LG_PKT_SYMBOLS] - num_symbols[BYTE_CNT_W-1:LG_PKT_SYMBOLS]) :
   //                                             (sink_byte_cnt[BYTE_CNT_W-1:LG_PKT_SYMBOLS] - num_symbols[BYTE_CNT_W-1:LG_PKT_SYMBOLS]);
   //         end
   //         else begin // not busy, at least one more beat to go
   //            burst_uncompress_byte_counter <= sink_byte_cnt[BYTE_CNT_W-1:LG_PKT_SYMBOLS] - num_symbols[BYTE_CNT_W-1:LG_PKT_SYMBOLS];
   //             // To do: should busy go true for numsymbols-size compressed
   //            // bursts?
   //         end
   //      end
   //   end
   //end
   
   always @ (posedge clk) begin
      if (source_valid & source_ready & sink_valid) begin
         if (burst_uncompress_busy) begin
            burst_uncompress_byte_counter <= (burst_uncompress_byte_counter_lint[BYTE_CNT_W-1:LG_PKT_SYMBOLS] - num_symbols[BYTE_CNT_W-1:LG_PKT_SYMBOLS]) ;
         end
         else begin // not busy, at least one more beat to go
            burst_uncompress_byte_counter <= sink_byte_cnt[BYTE_CNT_W-1:LG_PKT_SYMBOLS] - num_symbols[BYTE_CNT_W-1:LG_PKT_SYMBOLS];
         end
      end
   end
  
   reg [ADDR_W - 1 : 0 ] burst_uncompress_address_base;
   reg [ADDR_W - 1 : 0] burst_uncompress_address_offset;

   wire [63:0] decoded_burstsize_wire;
   wire [ADDR_W-1:0] decoded_burstsize;


   localparam ADD_BURSTWRAP_W = (ADDR_W > BURSTWRAP_W) ? ADDR_W : BURSTWRAP_W;
   wire [ADD_BURSTWRAP_W-1:0] addr_width_burstwrap;
   // The input burstwrap value can be used as a mask against address values,
   // but with one caveat: the address width may be (probably is) wider than 
   // the burstwrap width.  The spec says: extend the msb of the burstwrap 
   // value out over the entire address width (but only if the address width
   // actually is wider than the burstwrap width; otherwise it's a 0-width or
   // negative range and concatenation multiplier). 
   generate
      if (ADDR_W > BURSTWRAP_W) begin : addr_sign_extend
         // Sign-extend, just wires:
            assign addr_width_burstwrap[ADDR_W - 1 : BURSTWRAP_W] =
                {(ADDR_W - BURSTWRAP_W) {sink_burstwrap[BURSTWRAP_W - 1]}};
            assign addr_width_burstwrap[BURSTWRAP_W-1:0] = sink_burstwrap [BURSTWRAP_W-1:0];
      end
      else begin
            assign addr_width_burstwrap[BURSTWRAP_W-1 : 0] = sink_burstwrap;
      end
   endgenerate

   always @(posedge clk) begin
     if (first_packet_beat & source_ready) begin
       burst_uncompress_address_base <= sink_addr & ~addr_width_burstwrap[ADDR_W-1:0];
     end
   end

   //always @(posedge clk or posedge reset) begin
   //  if (reset) begin
   //    burst_uncompress_address_base <= '0;
   //  end
   //  else if (first_packet_beat & source_ready) begin
   //    burst_uncompress_address_base <= sink_addr & ~addr_width_burstwrap[ADDR_W-1:0];
   //  end
   //end

   assign decoded_burstsize_wire = bytes_in_transfer(sink_burstsize);  //expand it to 64 bits
   assign decoded_burstsize = decoded_burstsize_wire[ADDR_W-1:0];      //then take the width that is needed

   wire [ADDR_W : 0] p1_burst_uncompress_address_offset =
   (
     (first_packet_beat ?
       sink_addr :
       burst_uncompress_address_offset) + decoded_burstsize
    ) &
    addr_width_burstwrap[ADDR_W-1:0];
    wire [ADDR_W-1:0] p1_burst_uncompress_address_offset_lint = p1_burst_uncompress_address_offset [ADDR_W-1:0];

   always @ (posedge clk) begin
       if (source_ready & source_valid) begin
         burst_uncompress_address_offset <= p1_burst_uncompress_address_offset_lint;
       end
   end

   //always @(posedge clk or posedge reset) begin
   //  if (reset) begin
   //    burst_uncompress_address_offset <= '0;
   //  end
   //  else begin
   //    if (source_ready & source_valid) begin
   //      burst_uncompress_address_offset <= p1_burst_uncompress_address_offset_lint;
   //      // if (first_packet_beat) begin
   //      //   burst_uncompress_address_offset <=
   //      //     (sink_addr + num_symbols) & addr_width_burstwrap;
   //      // end
   //      // else begin
   //      //   burst_uncompress_address_offset <=
   //      //     (burst_uncompress_address_offset + num_symbols) & addr_width_burstwrap;
   //      // end
   //    end
   //  end
   //end
  
   // On the first packet beat, send the input address out unchanged, 
   // while values are computed/registered for 2nd and subsequent beats.
   assign source_addr = first_packet_beat ? sink_addr :
       burst_uncompress_address_base | burst_uncompress_address_offset;
   assign source_burstwrap = sink_burstwrap;
   assign source_burstsize = sink_burstsize;
  
   //-------------------------------------------------------------------
   // A single (compressed) read burst will have sop/eop in the same beat.
   // A sequence of read sub-bursts emitted by a burst adapter in response to a
   // single read burst will have sop on the first sub-burst, eop on the last.
   // Assert eop only upon (sink_endofpacket & last_packet_beat) to preserve 
   // packet conservation.
   assign source_startofpacket = sink_startofpacket & ~burst_uncompress_busy;
   assign source_endofpacket   = sink_endofpacket & last_packet_beat;
   assign sink_ready = source_valid & source_ready & last_packet_beat;
  
   // This is correct for the slave agent usage, but won't always be true in the
   // width adapter.  To do: add an "please uncompress" input, and use it to
   // pass-through or modify, and set source_is_compressed accordingly.
   assign source_is_compressed = 1'b0;
endmodule

`ifdef QUESTA_INTEL_OEM
`pragma questa_oem_00 "GdrtC8041f37ha52Ko+Jde808iDyKA+ht5m5AuKQCsm3cRPQscDvF+wBgbawWOxUtCRI9a/tnC6AChwO+BxfmEV2UK9ncMFAL//YMEMfhylNbbg+DkYNRltJ3oLac/x0CKLYUz0kP213IDPHPJdDrn2XWjqkg2d8WjL/DUsL13IJgiL6ltB1LI/UYnSBUYY+yK6OwicfHT3EuyorZ8lWql/zzL2Fl1behLT6A47M1qjq5QaK5lrVaeznNRGmZ8P9UE79jfJUeYVG8OcBfWWv7r04JvcmrJAmuia+VM6d88hG4g1LocByBDgcV85uZGypigjhSB74r3yUuU7WpK/kiBJx6sW02SC/DRu0tKwLZ6v+Zz07mO1HKx8wWudw74itjkY83pu7P0/2299EwmY2LVq0vSjy1oLO08OhIy2LQEPFPD/wkff33QkBIGrwPkBZf4dfUMU8bDUs8tEuf/7BalFlS0t4lqoQEv7tUzhHfEx31BHeffcwL8RAZ6wez6ozn7wbSJEAjqq68Edp8Cbu4uYeFe4RSbK0Wsw2TQ8uGPKrsxifN80aV4PjI+YfMAkt/izOR1IbZXFpjK0sT4K1Mparp7zpAjDjP+4W0flBgx9H803Xtdj0E8AoJ1Fmk8NYC+ZGwXLoaIGky3P+RMUvbz+JV8i2MmJoVDxeZrpbbfW/p4B656VYXthkOyg/N30aZbtBQfd+AgfvA2KGii6mf4blh9aLfbvS4P/OLpL/qT0psQcITgDd6nwdliPcIgd3GkMFXD2QIz+chuv+stUhWiZbwl3WNdCciRm6F5d5NKBkI+bv6gNbCbY7wTjt/iPA/vhpbvKkldKZnbDjkmmTGjqmGoNrGBxv/WzM5ZYLeYznyBn77viXi5ivBP4SZTVQ01sDbx9rxwepSFp+9vz1Qzaku8QOD6L3g2Qb00uZpy+TUiaafb49tarpJtQmV1WxnkeRffGBrbdYWNHDPlY76Ps9w59EkUVJ2yVB7p53mz496q+HoGHxZut/Mwhmp7H/"
`endif
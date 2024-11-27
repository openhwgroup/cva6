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


// $Id: //acds/rel/24.1/ip/iconnect/merlin/altera_merlin_burst_adapter/new_source/altera_wrap_burst_converter.sv#1 $
// $Revision: #1 $
// $Date: 2024/02/01 $

// ------------------------------------------------------
// This component is specially for Wrapping Avalon slave.
// It converts burst length of input packet
// to match slave burst.
// ------------------------------------------------------

`timescale 1 ns / 1 ns

module altera_wrap_burst_converter
#(
  parameter
    // ----------------------------------------
    // Burst length Parameters
    // (real burst length value, not bytecount)
    // ----------------------------------------
    MAX_IN_LEN              = 16,
    MAX_OUT_LEN             = 4,
    ADDR_WIDTH              = 12,
    BNDRY_WIDTH             = 12,
    NUM_SYMBOLS             = 4,
    AXI_SLAVE               = 0,
    OPTIMIZE_WRITE_BURST    = 0,
    SYNC_RESET             =  0, 
    // ------------------
    // Derived Parameters
    // ------------------
    LEN_WIDTH       = log2ceil(MAX_IN_LEN) + 1,
    OUT_LEN_WIDTH   = log2ceil(MAX_OUT_LEN) + 1,
    LOG2_NUMSYMBOLS = log2ceil(NUM_SYMBOLS)
)
(
    input                           clk,
    input                           reset,
    input                           enable_write,
    input                           enable_read,

    input [LEN_WIDTH   - 1 : 0]     in_len,
    input [LEN_WIDTH   - 1 : 0]     first_len,
    input                           in_sop,

    input [ADDR_WIDTH  - 1 : 0]     in_addr,
    input [ADDR_WIDTH  - 1 : 0]     in_addr_reg,
    input [BNDRY_WIDTH - 1 : 0]     in_boundary,
    input [BNDRY_WIDTH - 1 : 0]     in_burstwrap,
    input [BNDRY_WIDTH - 1 : 0]     in_burstwrap_reg,

    // converted output length
    // out_len         : compressed burst, read
    // uncompressed_len: uncompressed, write
    output reg [LEN_WIDTH - 1 : 0]  out_len,
    output reg [LEN_WIDTH - 1 : 0]  uncompr_out_len,

    // Compressed address output
    output reg [ADDR_WIDTH - 1 : 0] out_addr,
    output reg                      new_burst_export
);

    // ------------------------------
    // Local parameters
    // ------------------------------
    localparam
        OUT_BOUNDARY        = MAX_OUT_LEN * NUM_SYMBOLS,
        ADDR_SEL            = log2ceil(OUT_BOUNDARY);

    // ----------------------------------------
    // Signals for wrapping support
    // ----------------------------------------
    reg [LEN_WIDTH - 1 : 0]        remaining_len;
    reg [LEN_WIDTH - 1 : 0]        next_out_len;
    reg [LEN_WIDTH - 1 : 0]        next_rem_len;
    reg [LEN_WIDTH - 1 : 0]        uncompr_remaining_len;
    reg                            new_burst;
    reg                            uncompr_sub_burst;
    reg [LEN_WIDTH - 1 : 0]        next_uncompr_out_len;
    reg [LEN_WIDTH - 1 : 0]        next_uncompr_sub_len;

    // Avoid QIS warning
    wire [OUT_LEN_WIDTH - 1 : 0]   max_out_length;
    assign max_out_length  = MAX_OUT_LEN[OUT_LEN_WIDTH - 1 : 0];

    // ----------------------------------------
    // Calculate aligned length for WRAP burst
    // ----------------------------------------
    reg [ADDR_WIDTH - 1 : 0]       extended_burstwrap;
    reg [ADDR_WIDTH - 1 : 0]       extended_burstwrap_reg;

    always_comb begin
        extended_burstwrap      = {{(ADDR_WIDTH - BNDRY_WIDTH) {in_burstwrap[BNDRY_WIDTH - 1]}}, in_burstwrap};
        extended_burstwrap_reg  = {{(ADDR_WIDTH - BNDRY_WIDTH) {in_burstwrap_reg[BNDRY_WIDTH - 1]}}, in_burstwrap_reg};
        new_burst_export        = new_burst;
    end

    // Generation of internal reset synchronization
   reg internal_sclr;
   generate if (SYNC_RESET == 1) begin : rst_syncronizer
      always @ (posedge clk) begin
         internal_sclr <= reset;
      end
   end
   endgenerate

    // -------------------------------------------
    // length calculation
    // -------------------------------------------
    reg [LEN_WIDTH -1 : 0] next_uncompr_remaining_len;
    always_comb begin
        // Signals name
        // *_uncompr_* --> uncompressed transaction
        // -------------------------------------------
        // Always use max_out_length as possible.
        // Else use the remaining length.
        // If in length smaller and not cross bndry or same, pass thru.

        if (in_sop) begin
            uncompr_remaining_len = in_len;
        end
        else begin
            uncompr_remaining_len = next_uncompr_remaining_len;
        end
    end // always_comb

    // compressed transactions
    always_comb begin : proc_compressed_read
        remaining_len  = in_len;
        if (!new_burst)
            remaining_len = next_rem_len;
    end

    always_comb begin
        next_uncompr_out_len = first_len;
        if (in_sop) begin
            next_uncompr_out_len = first_len;
        end
        else begin
            if (uncompr_sub_burst)
                next_uncompr_out_len = next_uncompr_sub_len;
            else begin
                if (uncompr_remaining_len < max_out_length)
                    next_uncompr_out_len = uncompr_remaining_len;
                else
                    next_uncompr_out_len = max_out_length;
            end
        end
    end

    // Compressed transaction: Always try to send MAX out_len then remaining length.
    // Seperate it as the main difference is the first out len.
    // For a WRAP burst, the first beat is the aligned length, then similar to INCR.
    always_comb begin
        if (new_burst) begin
            next_out_len = first_len;
        end
        else begin
            next_out_len = max_out_length;
            if (remaining_len < max_out_length) begin
                next_out_len = remaining_len;
            end
        end
    end // always_comb

    // --------------------------------------------------
    // Length remaining calculation : Compressed
    // --------------------------------------------------
    // length remaining for compressed transaction
    // for wrap, need special handling for first out length

    always_ff @(posedge clk) begin
        if (enable_read) begin
            if (new_burst)
                next_rem_len <= in_len - first_len;
            else
                next_rem_len <= next_rem_len - max_out_length;
        end
    end // always_ff @

    //generate
    //  if (SYNC_RESET == 0) begin : async_rst1
    //   always_ff @(posedge clk, posedge reset) begin
    //       if (reset)
    //           next_rem_len  <= 0;
    //       else if (enable_read) begin
    //           if (new_burst)
    //               next_rem_len <= in_len - first_len;
    //           else
    //               next_rem_len <= next_rem_len - max_out_length;
    //       end
    //   end // always_ff @
    // end // async_rst1
    // else begin // sync_rst1
    //   always_ff @(posedge clk) begin
    //       if (internal_sclr)
    //           next_rem_len  <= 0;
    //       else if (enable_read) begin
    //           if (new_burst)
    //               next_rem_len <= in_len - first_len;
    //           else
    //               next_rem_len <= next_rem_len - max_out_length;
    //       end
    //   end // always_ff @
    //  end // sync_rst1
    // endgenerate
    
    // --------------------------------------------------
    // Length remaining calculation : Uncompressed
    // --------------------------------------------------

    always_ff @(posedge clk) begin
        if (enable_write) begin
            if (in_sop)
                next_uncompr_remaining_len  <= in_len - first_len;
            else if (!uncompr_sub_burst)
                next_uncompr_remaining_len  <= next_uncompr_remaining_len - max_out_length;
        end
    end // always_ff @
    
    // length for each sub-burst if it needs to chop the burst
    always_ff @(posedge clk) begin
        if (enable_write) begin
            next_uncompr_sub_len  <= next_uncompr_out_len - 1'b1; // in term of length, it just reduces 1
        end
    end

   generate 
   if (SYNC_RESET == 0) begin : async_rst2
       //always_ff @(posedge clk, posedge reset) begin
       //    if (reset) begin
       //        next_uncompr_remaining_len  <= 0;
       //    end
       //    else if (enable_write) begin
       //        if (in_sop)
       //            next_uncompr_remaining_len  <= in_len - first_len;
       //        else if (!uncompr_sub_burst)
       //            next_uncompr_remaining_len  <= next_uncompr_remaining_len - max_out_length;
       //    end
       //end // always_ff @

       //// length for each sub-burst if it needs to chop the burst
       //always_ff @(posedge clk, posedge reset) begin
       //    if (reset) begin
       //        next_uncompr_sub_len  <= 0;
       //    end
       //    else if (enable_write) begin
       //        next_uncompr_sub_len  <= next_uncompr_out_len - 1'b1; // in term of length, it just reduces 1
       //    end
       //end

       // the sub-burst still active
       always_ff @(posedge clk, posedge reset) begin
           if (reset) begin
               uncompr_sub_burst <= 0;
           end
           else if (enable_write) begin
               uncompr_sub_burst <= (next_uncompr_out_len > 1'b1);
           end
       end
   end // async_rst1
   else begin // sync_rst2

       //always_ff @(posedge clk) begin
       //    if (internal_sclr) begin
       //        next_uncompr_remaining_len  <= 0;
       //    end
       //    else if (enable_write) begin
       //        if (in_sop)
       //            next_uncompr_remaining_len  <= in_len - first_len;
       //        else if (!uncompr_sub_burst)
       //            next_uncompr_remaining_len  <= next_uncompr_remaining_len - max_out_length;
       //    end
       //end // always_ff @
       //
       //// length for each sub-burst if it needs to chop the burst
       //always_ff @(posedge clk) begin
       //    if (internal_sclr) begin
       //        next_uncompr_sub_len  <= 0;
       //    end
       //    else if (enable_write) begin
       //        next_uncompr_sub_len  <= next_uncompr_out_len - 1'b1; // in term of length, it just reduces 1
       //    end
       //end

       // the sub-burst still active
       always_ff @(posedge clk) begin
           if (internal_sclr) begin
               uncompr_sub_burst <= 0;
           end
           else if (enable_write) begin
               uncompr_sub_burst <= (next_uncompr_out_len > 1'b1);
           end
       end
   end // sync_rst2
   endgenerate

    // --------------------------------------------------
    // Control signals
    // --------------------------------------------------
    wire end_compressed_sub_burst;
    assign end_compressed_sub_burst  = (remaining_len == next_out_len);

    // new_burst:
    //  the converter takes in_len for new caculation
    generate
     if (SYNC_RESET == 0) begin : async_rst3
       always_ff @(posedge clk, posedge reset) begin
           if (reset) begin
               new_burst   <= 1;
           end
           else if (enable_read) begin
               new_burst   <= end_compressed_sub_burst;
           end
       end
     end // async_rst3
     else begin // sync_rst3
       always_ff @(posedge clk) begin
           if (internal_sclr) begin
               new_burst   <= 1;
           end
           else if (enable_read) begin
               new_burst   <= end_compressed_sub_burst;
           end
       end
     end // sync_rst3
    endgenerate
    // --------------------------------------------------
    // Output length
    // --------------------------------------------------
    // register out_len for compressed trans
    always_ff @(posedge clk) begin
        if (enable_read) begin
            out_len <= next_out_len;
        end
    end

    //generate 
    // if (SYNC_RESET == 0) begin : async_rst4
    //   always_ff @(posedge clk, posedge reset) begin
    //       if (reset) begin
    //           out_len <= 0;
    //       end
    //       else if (enable_read) begin
    //           out_len <= next_out_len;
    //       end
    //   end
    //  end // async_rst4
    //  else begin // sync_rst4
    //    always_ff @(posedge clk) begin
    //       if (internal_sclr) begin
    //           out_len <= 0;
    //       end
    //       else if (enable_read) begin
    //           out_len <= next_out_len;
    //       end
    //   end
    // end // sync_rst4
    //endgenerate

    // register uncompr_out_len for uncompressed trans
    generate
        if (OPTIMIZE_WRITE_BURST) begin : optimized_write_burst_len
          always_ff @(posedge clk) begin
              if (enable_read) begin
                  uncompr_out_len <= first_len;
              end
          end

          //if (SYNC_RESET == 0) begin : async_rst5
          //  always_ff @(posedge clk, posedge reset) begin
          //      if (reset) begin
          //          uncompr_out_len <= '0;
          //      end
          //      //else if (enable_write) begin
          //      else if (enable_read) begin
          //          uncompr_out_len <= first_len;
          //      end
          //  end
          //end // async_rst5
          //else begin // sync_rst5
          //  always_ff @(posedge clk) begin
          //      if (internal_sclr) begin
          //          uncompr_out_len <= '0;
          //      end
          //      //else if (enable_write) begin
          //      else if (enable_read) begin
          //          uncompr_out_len <= first_len;
          //      end
          //  end
          //end // sync_rst5
        end
        else begin : unoptimized_write_burst_len
          always_ff @(posedge clk) begin
              if (enable_write) begin
                  uncompr_out_len <= next_uncompr_out_len;
              end
          end

          //if (SYNC_RESET == 0) begin : async_rst6
          //  always_ff @(posedge clk, posedge reset) begin
          //      if (reset) begin
          //          uncompr_out_len <= '0;
          //      end
          //      else if (enable_write) begin
          //          uncompr_out_len <= next_uncompr_out_len;
          //      end
          //  end
          // end // async_rst6
          // else begin // sync_rst6
          //  always_ff @(posedge clk) begin
          //      if (internal_sclr) begin
          //          uncompr_out_len <= '0;
          //      end
          //      else if (enable_write) begin
          //          uncompr_out_len <= next_uncompr_out_len;
          //      end
          //  end
          // end // sync_rst6
        end // else unoptimized
    endgenerate

    // --------------------------------------------------
    // Address calculation
    // --------------------------------------------------
    reg [ADDR_WIDTH - 1 : 0]        addr_incr;
    localparam [ADDR_WIDTH - 1 : 0] ADDR_INCR = MAX_OUT_LEN << LOG2_NUMSYMBOLS;
    assign addr_incr  = ADDR_INCR[ADDR_WIDTH - 1 : 0];

    reg [ADDR_WIDTH - 1 : 0]    next_out_addr;
    reg [ADDR_WIDTH - 1 : 0]    incremented_addr;
    
    always_ff @(posedge clk) begin
            if (enable_read) begin
                out_addr <=  (next_out_addr);
            end
    end // always_ff @

    //generate 
    // if (SYNC_RESET == 0) begin : async_rst7
    //   always_ff @(posedge clk, posedge reset) begin
    //       if (reset) begin
    //           out_addr <= '0;
    //       end
    //       else begin
    //           if (enable_read) begin
    //               out_addr <=  (next_out_addr);
    //           end
    //       end
    //   end // always_ff @
    //  end // async_rst7
    //  else begin // sync_rst7
    //   always_ff @(posedge clk) begin
    //       if (internal_sclr) begin
    //           out_addr <= '0;
    //       end
    //       else begin
    //           if (enable_read) begin
    //               out_addr <=  (next_out_addr);
    //           end
    //       end
    //   end // always_ff @
    //  end // sync_rst7
    // endgenerate

    // use burstwrap/burstwrap_reg to calculate address incrementing
    always_ff @(posedge clk) begin
        if (enable_read) begin
            incremented_addr <= ((next_out_addr + addr_incr) & extended_burstwrap_reg);
            if (new_burst) begin
                incremented_addr <= ((next_out_addr + (first_len << LOG2_NUMSYMBOLS)) & extended_burstwrap); //byte address
            end
        end
    end // always_ff @

    //generate
    // if (SYNC_RESET == 0) begin : async_rst8
    //   always_ff @(posedge clk, posedge reset) begin
    //       if (reset) begin
    //           incremented_addr <= '0;
    //       end
    //       else if (enable_read) begin
    //           incremented_addr <= ((next_out_addr + addr_incr) & extended_burstwrap_reg);
    //           if (new_burst) begin
    //               incremented_addr <= ((next_out_addr + (first_len << LOG2_NUMSYMBOLS)) & extended_burstwrap); //byte address
    //           end
    //       end
    //   end // always_ff @
    // end // async_rst8
    // else begin // sync_rst8
    //    always_ff @(posedge clk) begin
    //       if (internal_sclr) begin
    //           incremented_addr <= '0;
    //       end
    //       else if (enable_read) begin
    //           incremented_addr <= ((next_out_addr + addr_incr) & extended_burstwrap_reg);
    //           if (new_burst) begin
    //               incremented_addr <= ((next_out_addr + (first_len << LOG2_NUMSYMBOLS)) & extended_burstwrap); //byte address
    //           end
    //       end
    //   end // always_ff @
    // end // sync_rst8
    // endgenerate
  
    always_comb begin
        next_out_addr  = in_addr;
        if (!new_burst) begin
            next_out_addr = in_addr_reg & ~extended_burstwrap_reg | incremented_addr;
        end
    end

    // --------------------------------------------------
    // Calculates the log2ceil of the input value
    // --------------------------------------------------
    function integer log2ceil;
        input integer val;
        reg[31:0] i;

        begin
            i = 1;
            log2ceil = 0;

            while (i < val) begin
                log2ceil = log2ceil + 1;
                i = i[30:0] << 1;
            end
        end
    endfunction

endmodule
`ifdef QUESTA_INTEL_OEM
`pragma questa_oem_00 "GdrtC8041f37ha52Ko+Jde808iDyKA+ht5m5AuKQCsm3cRPQscDvF+wBgbawWOxUtCRI9a/tnC6AChwO+BxfmEV2UK9ncMFAL//YMEMfhylNbbg+DkYNRltJ3oLac/x0CKLYUz0kP213IDPHPJdDrn2XWjqkg2d8WjL/DUsL13IJgiL6ltB1LI/UYnSBUYY+yK6OwicfHT3EuyorZ8lWql/zzL2Fl1behLT6A47M1qgxLHxdiWvt4zIRH9aivTqLtrDxEJ9+CciJzaKDEoIS41DeTwt5sapLTBiV4O3s9fxo4fp7iykJU8ulQ60esa3ZCgZv3NRhvAGzQ/BZvMQI39Gzt+22MYf8ltkmReO9hCRec6M4SicNyy9RMaxIGKHZJcqH54nxpYfGm78A16M/aKdJRQKLxRdjwm3pH5wk4fL43LinTXbXmH5NZRwmpnj4WhLXP3I8YgFjoChIctno3ZxSzKEemuy+c8MANApijDAAt8jtHTLB/8wU7uD0NjLH7AD5wHAZxx01Y+hhWO3EorjFQjjBZpz970eyP+C5HE9KXLLzsC1v1HeI0QIsYksiZNZra64mgMkCr2uvEpunqk3KKVqyCxABoNcYUTB2TKrov+O145lPoc3Zovi0W/iJATjTu9l3eRo4+zkGx5quSVtIofDL8aNmXHR3Hy09LRNgfUfryRoQb+PiaqwKLCtHXkP7ys5vBpT9kRmV7VBtArirnV8daaEDH7dsHP+NujxOOe+Ws+dT/pRmhq3xJPbHKiPHdd0ro75oPjiZRlF0xtBi5g1YhOg3viXaaOMgaao/jZRlWFb5NzzvhHjT/eNczOPVYqkjWKjNrc41QxDrTydc/RV3LqxrCTvb7P3A8HTwsjXK8moBD7Rm/S90DZtYBHLN/84jN36i92eLj/mNRBq0scw6aYXm5domcvxOKAEhBDOrpqyqFNQWz2OL2espH1ERQ5meqYtlGpTzqc8guYaMEcUod5pQbby9uQ0W0fTZ6p6DnkhyHd+zlHozj/mT"
`endif
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


// $Id: //acds/rel/24.1/ip/iconnect/merlin/altera_merlin_burst_adapter/new_source/altera_incr_burst_converter.sv#1 $
// $Revision: #1 $
// $Date: 2024/02/01 $

// ----------------------------------------------------------
// This component is used for INCR Avalon slave
// (slave which only supports INCR) or AXI slave.
// It converts burst length of input packet
// to match slave burst.
// ----------------------------------------------------------

`timescale 1 ns / 1 ns

module altera_incr_burst_converter
#(
  parameter
    // ----------------------------------------
    // Burst length Parameters
    // (real burst length value, not bytecount)
    // ----------------------------------------
    MAX_IN_LEN          = 16,
    MAX_OUT_LEN         = 4,
    NUM_SYMBOLS         = 4,
    ADDR_WIDTH          = 12,
    BNDRY_WIDTH         = 12,
    BURSTSIZE_WIDTH     = 3,
    IN_NARROW_SIZE      = 0,
    PURELY_INCR_AVL_SYS = 0,
    SYNC_RESET          = 0,
    // ------------------
    // Derived Parameters
    // ------------------
    LEN_WIDTH       = log2ceil(MAX_IN_LEN) + 1,
    OUT_LEN_WIDTH   = log2ceil(MAX_OUT_LEN) + 1,
    LOG2_NUMSYMBOLS = log2ceil(NUM_SYMBOLS)
)
(
    input                               clk,
    input                               reset,
    input                               enable,

    input                               is_write,
    input [LEN_WIDTH       - 1 : 0]     in_len,
    input                               in_sop,

    input [ADDR_WIDTH      - 1 : 0]     in_addr,
    input [ADDR_WIDTH      - 1 : 0]     in_addr_reg,
    input [BNDRY_WIDTH     - 1 : 0]     in_burstwrap_reg,
    input [BURSTSIZE_WIDTH - 1 : 0]     in_size_t,
    input [BURSTSIZE_WIDTH - 1 : 0]     in_size_reg,

    // converted output length
    // out_len         : compressed burst, read
    // uncompressed_len: uncompressed, write
    output reg [LEN_WIDTH  - 1 : 0]     out_len,
    output reg [LEN_WIDTH  - 1 : 0]     uncompr_out_len,
    // Compressed address output
    output reg [ADDR_WIDTH - 1 : 0]     out_addr,
    output reg                          new_burst_export
);

    // ----------------------------------------
    // Signals for wrapping support
    // ----------------------------------------
    reg [LEN_WIDTH - 1 : 0]        remaining_len;
    reg [LEN_WIDTH - 1 : 0]        next_out_len;
    reg [LEN_WIDTH - 1 : 0]        next_rem_len;
    reg [LEN_WIDTH - 1 : 0]        uncompr_remaining_len;
    reg [LEN_WIDTH - 1 : 0]        next_uncompr_remaining_len;
    reg [LEN_WIDTH - 1 : 0]        next_uncompr_rem_len;
    reg                            new_burst;
    reg                            uncompr_sub_burst;


    // Generation of internal reset synchronization
   reg internal_sclr;
   generate if (SYNC_RESET == 1) begin : rst_syncronizer
      always @ (posedge clk) begin
         internal_sclr <= reset;
      end
   end
   endgenerate

    // Avoid QIS warning
    wire [OUT_LEN_WIDTH - 1 : 0]   max_out_length;
    assign max_out_length  = MAX_OUT_LEN[OUT_LEN_WIDTH - 1 : 0];

    always_comb begin
        new_burst_export = new_burst;
    end

    // -------------------------------------------
    // length remaining calculation
    // -------------------------------------------

    always_comb begin : proc_uncompressed_remaining_len
        if ((in_len <= max_out_length) && is_write) begin
            uncompr_remaining_len = in_len;
        end else begin
            uncompr_remaining_len = max_out_length;
        end

        if (uncompr_sub_burst)
            uncompr_remaining_len = next_uncompr_rem_len;
    end

   always_ff @(posedge clk) begin
       if (enable) begin
           next_uncompr_rem_len  <= uncompr_remaining_len - 1'b1; // in term of length, it just reduces 1
       end
   end

   //generate
   //  if (SYNC_RESET == 0) begin : async_rst1
   //    always_ff @(posedge clk, posedge reset) begin
   //        if (reset) begin
   //            next_uncompr_rem_len  <= 0;
   //        end
   //        else if (enable) begin
   //            next_uncompr_rem_len  <= uncompr_remaining_len - 1'b1; // in term of length, it just reduces 1
   //        end
   //    end
   //  end // async_rst1
   //  else begin // sync_rst1

   //    always_ff @(posedge clk) begin
   //        if (internal_sclr) begin
   //            next_uncompr_rem_len  <= 0;
   //        end
   //        else if (enable) begin
   //            next_uncompr_rem_len  <= uncompr_remaining_len - 1'b1; // in term of length, it just reduces 1
   //        end
   //    end
   //  end // sync_rst1
   //endgenerate

    always_comb begin : proc_compressed_remaining_len
       remaining_len  = in_len;
        if (!new_burst)
            remaining_len = next_rem_len;
    end

    always_ff@(posedge clk) begin : proc_next_uncompressed_remaining_len
        if (enable) begin
            if (in_sop) begin
                next_uncompr_remaining_len <= in_len - max_out_length;
            end
            else if (!uncompr_sub_burst)
                next_uncompr_remaining_len <= next_uncompr_remaining_len - max_out_length;
        end
    end

     //generate
     // if (SYNC_RESET == 0) begin : async_rst2
     //  always_ff@(posedge clk or posedge reset) begin : proc_next_uncompressed_remaining_len
     //      if(reset) begin
     //          next_uncompr_remaining_len <= '0;
     //      end
     //      else if (enable) begin
     //          if (in_sop) begin
     //              next_uncompr_remaining_len <= in_len - max_out_length;
     //          end
     //          else if (!uncompr_sub_burst)
     //              next_uncompr_remaining_len <= next_uncompr_remaining_len - max_out_length;
     //      end
     //  end
     // end // async_rst2
     // else begin // sync_rst2
     //  always_ff@(posedge clk ) begin : proc_next_uncompressed_remaining_len
     //      if(internal_sclr) begin
     //          next_uncompr_remaining_len <= '0;
     //      end
     //      else if (enable) begin
     //          if (in_sop) begin
     //              next_uncompr_remaining_len <= in_len - max_out_length;
     //          end
     //          else if (!uncompr_sub_burst)
     //              next_uncompr_remaining_len <= next_uncompr_remaining_len - max_out_length;
     //      end
     //  end
     // end // sync_rst2
     //endgenerate 

    always_comb begin
        next_out_len = max_out_length;
        if (remaining_len < max_out_length) begin
            next_out_len = remaining_len;
        end
    end // always_comb
 
    // --------------------------------------------------
    // Length remaining calculation : compressed
    // --------------------------------------------------
    // length remaining for compressed transaction
    // for wrap, need special handling for first out length

   always_ff @(posedge clk) begin
       if (enable) begin
           if (new_burst)
               next_rem_len <= in_len - max_out_length;
           else
               next_rem_len <= next_rem_len - max_out_length;
       end
   end
   
    generate 
      if (SYNC_RESET == 0) begin: async_rst3
       //always_ff @(posedge clk, posedge reset) begin
       //    if (reset)
       //        next_rem_len  <= 0;
       //    else if (enable) begin
       //        if (new_burst)
       //            next_rem_len <= in_len - max_out_length;
       //        else
       //            next_rem_len <= next_rem_len - max_out_length;
       //    end
       //end

       always_ff @(posedge clk, posedge reset) begin
           if (reset) begin
               uncompr_sub_burst <= 0;
           end
           else if (enable && is_write) begin
               uncompr_sub_burst <= (uncompr_remaining_len > 1'b1);
           end
       end
     end // async_rst3
     else begin // sync_rst3
       //always_ff @(posedge clk) begin
       //    if (internal_sclr)
       //        next_rem_len  <= 0;
       //    else if (enable) begin
       //        if (new_burst)
       //            next_rem_len <= in_len - max_out_length;
       //        else
       //            next_rem_len <= next_rem_len - max_out_length;
       //    end
       //end

       always_ff @(posedge clk) begin
           if (internal_sclr) begin
               uncompr_sub_burst <= 0;
           end
           else if (enable && is_write) begin
               uncompr_sub_burst <= (uncompr_remaining_len > 1'b1);
           end
       end
     end // sync_rst3
    endgenerate 

    // --------------------------------------------------
    // Control signals
    // --------------------------------------------------
    wire end_compressed_sub_burst;
    assign end_compressed_sub_burst  = (remaining_len == next_out_len);

    // new_burst:
    //  the converter takes in_len for new calculation
    generate
     if (SYNC_RESET == 0) begin : async_rst4
       always_ff @(posedge clk, posedge reset) begin
           if (reset)
               new_burst   <= 1;
           else if (enable)
               new_burst   <= end_compressed_sub_burst;
       end
     end // async_rst4
     else begin // sync_rst4
       always_ff @(posedge clk) begin
           if (internal_sclr)
               new_burst   <= 1;
           else if (enable)
               new_burst   <= end_compressed_sub_burst;
       end
     end
    endgenerate 
    // --------------------------------------------------
    // Output length
    // --------------------------------------------------
    // register out_len for compressed trans
       always_ff @(posedge clk) begin
           if (enable) begin
               out_len <= next_out_len;
           end
       end

       // register uncompr_out_len for uncompressed trans
       always_ff @(posedge clk) begin
           if (enable) begin
               uncompr_out_len <= uncompr_remaining_len;
           end
       end

    //generate
    //  if (SYNC_RESET == 0) begin : async_rst5
    //   always_ff @(posedge clk, posedge reset) begin
    //       if (reset) begin
    //           out_len <= 0;
    //       end
    //       else if (enable) begin
    //           out_len <= next_out_len;
    //       end
    //   end

    //   // register uncompr_out_len for uncompressed trans
    //   always_ff @(posedge clk, posedge reset) begin
    //       if (reset) begin
    //           uncompr_out_len <= '0;
    //       end
    //       else if (enable) begin
    //           uncompr_out_len <= uncompr_remaining_len;
    //       end
    //   end
    //end // async_rst5
    //else begin // sync_rst5
    //   always_ff @(posedge clk) begin
    //       if (internal_sclr) begin
    //           out_len <= 0;
    //       end
    //       else if (enable) begin
    //           out_len <= next_out_len;
    //       end
    //   end

    //   // register uncompr_out_len for uncompressed trans
    //   always_ff @(posedge clk) begin
    //       if (internal_sclr) begin
    //           uncompr_out_len <= '0;
    //       end
    //       else if (enable) begin
    //           uncompr_out_len <= uncompr_remaining_len;
    //       end
    //   end
    //end //sync_rst5
    //endgenerate 

    // --------------------------------------------------
    // Address Calculation
    // --------------------------------------------------
    reg [ADDR_WIDTH - 1 : 0]        addr_incr_sel;
    reg [ADDR_WIDTH - 1 : 0]        addr_incr_sel_reg;
    reg [ADDR_WIDTH - 1 : 0]        addr_incr_full_size;

    localparam [ADDR_WIDTH - 1 : 0] ADDR_INCR = MAX_OUT_LEN << LOG2_NUMSYMBOLS;

    generate
        if (IN_NARROW_SIZE) begin : narrow_addr_incr
            reg [ADDR_WIDTH - 1 : 0]    addr_incr_variable_size;
            reg [ADDR_WIDTH - 1 : 0]    addr_incr_variable_size_reg;

            assign addr_incr_variable_size = MAX_OUT_LEN << in_size_t;
            assign addr_incr_variable_size_reg = MAX_OUT_LEN << in_size_reg;

            assign addr_incr_sel  = addr_incr_variable_size;
            assign addr_incr_sel_reg  = addr_incr_variable_size_reg;
        end
        else begin : full_addr_incr
            assign addr_incr_full_size  = ADDR_INCR[ADDR_WIDTH - 1 : 0];
            assign addr_incr_sel  = addr_incr_full_size;
            assign addr_incr_sel_reg = addr_incr_full_size;
        end
    endgenerate


    reg [ADDR_WIDTH - 1 : 0]    next_out_addr;
    reg [ADDR_WIDTH - 1 : 0]    incremented_addr;

    always_ff @(posedge clk) begin
      if (enable) begin
          out_addr <=  (next_out_addr);
      end
    end

    //generate 
    //   if (SYNC_RESET == 0) begin : async_rst6
    //      always_ff @(posedge clk, posedge reset) begin
    //          if (reset) begin
    //              out_addr <= '0;
    //          end else begin
    //              if (enable) begin
    //                  out_addr <=  (next_out_addr);
    //              end
    //          end
    //      end
    //   end // async_rst6
    //   else begin // sync_rst6 
    //      always_ff @(posedge clk) begin
    //          if (internal_sclr) begin
    //              out_addr <= '0;
    //          end else begin
    //              if (enable) begin
    //                  out_addr <=  (next_out_addr);
    //              end
    //          end
    //      end
    //   end // sync_rst6
    // endgenerate

    generate
        if (!PURELY_INCR_AVL_SYS) begin : incremented_addr_normal
            always_ff @(posedge clk) begin
                if (enable) begin
                    if (new_burst) begin
                        incremented_addr <= (next_out_addr + addr_incr_sel);
                    end
                    else begin
                        incremented_addr <= (next_out_addr + addr_incr_sel_reg);
                    end
                end
            end // always_ff @

            //if (SYNC_RESET == 0) begin : async_rst7
            //   always_ff @(posedge clk, posedge reset) begin
            //       if (reset) begin
            //           incremented_addr <= '0;
            //       end
            //       else if (enable) begin
            //           incremented_addr <= (next_out_addr + addr_incr_sel_reg);
            //           if (new_burst) begin
            //               incremented_addr <= (next_out_addr + addr_incr_sel);
            //           end
            //       end
            //   end // always_ff @
            //end // async_rst7
            //else begin // sync_rst7
            //   always_ff @(posedge clk) begin
            //       if (internal_sclr) begin
            //           incremented_addr <= '0;
            //       end
            //       else if (enable) begin
            //           incremented_addr <= (next_out_addr + addr_incr_sel_reg);
            //           if (new_burst) begin
            //               incremented_addr <= (next_out_addr + addr_incr_sel);
            //           end
            //       end
            //   end // always_ff @
            //end // sync_rst7
          
            always_comb begin
                next_out_addr = in_addr;
                if (!new_burst) begin
                    next_out_addr = incremented_addr;
                end
            end
        end
        else begin : incremented_addr_pure_av
   
            always_ff @(posedge clk) begin
                if (enable) begin
                    incremented_addr <= (next_out_addr + addr_incr_sel_reg);
                end
            end // always_ff @

            //if (SYNC_RESET == 0) begin : async_rst8
            //   always_ff @(posedge clk, posedge reset) begin
            //   if (reset) begin
            //      incremented_addr <= '0;
            //       end
            //       else if (enable) begin
            //           incremented_addr <= (next_out_addr + addr_incr_sel_reg);
            //       end
            //   end // always_ff @
            //end // async_rst8
            //else begin // sync_rst8
            //   always_ff @(posedge clk) begin
            //   if (internal_sclr) begin
            //      incremented_addr <= '0;
            //       end
            //       else if (enable) begin
            //           incremented_addr <= (next_out_addr + addr_incr_sel_reg);
            //       end
            //   end // always_ff @
            // end // sync_rst8

  
            always_comb begin
                next_out_addr  = in_addr;
                if (!new_burst) begin
                    next_out_addr  = (incremented_addr);
                end
            end

        end
    endgenerate

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
`pragma questa_oem_00 "GdrtC8041f37ha52Ko+Jde808iDyKA+ht5m5AuKQCsm3cRPQscDvF+wBgbawWOxUtCRI9a/tnC6AChwO+BxfmEV2UK9ncMFAL//YMEMfhylNbbg+DkYNRltJ3oLac/x0CKLYUz0kP213IDPHPJdDrn2XWjqkg2d8WjL/DUsL13IJgiL6ltB1LI/UYnSBUYY+yK6OwicfHT3EuyorZ8lWql/zzL2Fl1behLT6A47M1qhxJse+dnpWPLJXuPmEnacC16KyNx00KESkh6wgw/B0jW42rAToT4xtFO/U9EtF51FY77w6hJZsInE2gH4XSl+sJNYVaIDM0wCjkDKxLAF8p2mfrUURTOxGKC8TVGZByPtRuJsCnBiQMARPZSi0XzG4p3RGBNX/vtR9PemyNCWRj3nA3p4mDNamm5AM51WGIk8jp/mq0C2wrlhGo2XiATMWL/jSqEhQ67HifuK646p0m2XQZ6hKa+qRvZOyX1u3TE9KIhb0TNdzwM8upsWnbGxpJlcCdXnRKj8xIpW+M9nXusm31cguWRJZmi37NfHNdFIIPZLb63Vv1DC8sKNBSMGWGgss93/kksBTR5mUhHdveJVq7203cUiI7A01JA+qk22kCmpUkTER1H///qVDdtyBTYHPy7HddGIZNL24mED5ESnSTD646frEWer4zOpeXCABjoR//O7VeIHGaqhAF6xgHVn7uasc2m8UZyTfDqY/cZdFp8tSKXgJ97S6JjJyKnZookIaZNSJ6hF4IiCIWgT2wTv6P5Czy4Xu73osaWx7eWvqqyTqqo7EbxfTp35AtnYKNEQuZXuq9ha9qV4EiG/8j66EIMQM4V50c8o9iRM2t+DuZmMRvFChaxadMD++ti5gxKoR0WgP1uGs5lyfhEwQ9jfKnZijsLOCOhCF+rlrbegZ2f9l1IJVA/wHvk4ek38KNRDIb6WBAydPRCaigUmXhxVccSrsQ1kR8LfzwgYoDAUQIzsmFi0LIsyHJgSmzd+fNsG8WbD3UdODn9ltXE56"
`endif
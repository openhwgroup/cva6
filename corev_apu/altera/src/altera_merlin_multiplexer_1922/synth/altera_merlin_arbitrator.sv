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


// (C) 2001-2010 Altera Corporation. All rights reserved.
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


// $Id: //acds/main/ip/merlin/altera_merlin_std_arbitrator/altera_merlin_std_arbitrator_core.sv#3 $
// $Revision: #3 $
// $Date: 2010/07/07 $

/* -----------------------------------------------------------------------
Round-robin/fixed arbitration implementation.

Q: how do you find the least-significant set-bit in an n-bit binary number, X?

A: M = X & (~X + 1)

Example: X = 101000100
 101000100 & 
 010111011 + 1 =

 101000100 &
 010111100 =
 -----------
 000000100

The method can be generalized to find the first set-bit
at a bit index no lower than bit-index N, simply by adding
2**N rather than 1.


Q: how does this relate to round-robin arbitration?
A:
Let X be the concatenation of all request signals.
Let the number to be added to X (hereafter called the
top_priority) initialize to 1, and be assigned from the
concatenation of the previous saved-grant, left-rotated
by one position, each time arbitration occurs.  The
concatenation of grants is then M.

Problem: consider this case:

top_priority            = 010000
request                 = 001001
~request + top_priority = 000110
next_grant              = 000000 <- no one is granted!

There was no "set bit at a bit index no lower than bit-index 4", so 
the result was 0.

We need to propagate the carry out from (~request + top_priority) to the LSB, so
that the sum becomes 000111, and next_grant is 000001.  This operation could be
called a "circular add". 

A bit of experimentation on the circular add reveals a significant amount of 
delay in exiting and re-entering the carry chain - this will vary with device
family.  Quartus also reports a combinational loop warning.  Finally, 
Modelsim 6.3g has trouble with the expression, evaluating it to 'X'.  But 
Modelsim _doesn't_ report a combinational loop!)

An alternate solution: concatenate the request vector with itself, and OR
corresponding bits from the top and bottom halves to determine next_grant.

Example:

top_priority                        =        010000
{request, request}                  = 001001 001001
{~request, ~request} + top_priority = 110111 000110
result of & operation               = 000001 000000
next_grant                          =        000001

Notice that if request = 0, the sum operation will overflow, but we can ignore
this; the next_grant result is 0 (no one granted), as you might expect.
In the implementation, the last-granted value must be maintained as
a non-zero value - best probably simply not to update it when no requests
occur.

----------------------------------------------------------------------- */ 

`timescale 1 ns / 1 ns

module altera_merlin_arbitrator
#(
    parameter NUM_REQUESTERS = 8,
    // --------------------------------------
    // Implemented schemes
    // "round-robin"
    // "fixed-priority"
    // "no-arb"
    // --------------------------------------
    parameter SCHEME         = "round-robin",
    parameter PIPELINE       = 0,
    parameter SYNC_RESET     = 0
)
(
    input clk,
    input reset,
   
    // --------------------------------------
    // Requests
    // --------------------------------------
    input [NUM_REQUESTERS-1:0]  request,
   
    // --------------------------------------
    // Grants
    // --------------------------------------
    output [NUM_REQUESTERS-1:0] grant,

    // --------------------------------------
    // Control Signals
    // --------------------------------------
    input                       increment_top_priority,
    input                       save_top_priority
);

    // --------------------------------------
    // Signals
    // --------------------------------------
    wire [NUM_REQUESTERS-1:0]   top_priority;
    reg  [NUM_REQUESTERS-1:0]   top_priority_reg;
    reg  [NUM_REQUESTERS-1:0]   last_grant;
    wire [2*NUM_REQUESTERS-1:0] result;

    // --------------------------------------
    // Scheme Selection
    // --------------------------------------
    generate
        if (SCHEME == "round-robin" && NUM_REQUESTERS > 1) begin
            assign top_priority = top_priority_reg;
        end
        else begin
            // Fixed arbitration (or single-requester corner case)
            assign top_priority = 1'b1;
        end
    endgenerate

    // --------------------------------------
    // Decision Logic
    // --------------------------------------
    altera_merlin_arb_adder
    #(
        .WIDTH (2 * NUM_REQUESTERS)
    ) 
    adder
    (
        .a ({ ~request, ~request }),
        .b ({{NUM_REQUESTERS{1'b0}}, top_priority}),
        .sum (result)
    );

  
    generate if (SCHEME == "no-arb") begin

        // --------------------------------------
        // No arbitration: just wire request directly to grant
        // --------------------------------------
        assign grant = request;

    end else begin
        // Do the math in double-vector domain
        wire [2*NUM_REQUESTERS-1:0] grant_double_vector;
        assign grant_double_vector = {request, request} & result;

        // --------------------------------------
        // Extract grant from the top and bottom halves
        // of the double vector.
        // --------------------------------------
        assign grant =
            grant_double_vector[NUM_REQUESTERS - 1 : 0] |
            grant_double_vector[2 * NUM_REQUESTERS - 1 : NUM_REQUESTERS];

    end
    endgenerate
    
   // Generation of internal reset synchronization
   reg internal_sclr;
   generate if (SYNC_RESET == 1) begin : rst_syncronizer
      always @ (posedge clk) begin
         internal_sclr <= reset;
      end
   end
   endgenerate  

    // --------------------------------------
    // Left-rotate the last grant vector to create top_priority.
    // --------------------------------------
   generate 
   if (SYNC_RESET == 0) begin : async_rst0
       always @(posedge clk or posedge reset) begin
           if (reset) begin
               top_priority_reg <= 1'b1;
           end
           else begin
               if (PIPELINE) begin
                   if (increment_top_priority) begin
                       top_priority_reg <= (|request) ? {grant[NUM_REQUESTERS-2:0],
                           grant[NUM_REQUESTERS-1]} : top_priority_reg;
                   end
               end else begin
                   if (increment_top_priority) begin
                       if (|request)
                           top_priority_reg <= { grant[NUM_REQUESTERS-2:0],
                               grant[NUM_REQUESTERS-1] };
                       else
                           top_priority_reg <= { top_priority_reg[NUM_REQUESTERS-2:0], top_priority_reg[NUM_REQUESTERS-1] };
                   end
                   else if (save_top_priority) begin
                       top_priority_reg <= grant; 
                   end
               end
           end
       end
   end : async_rst0

   else begin : sync_rst0
       always @(posedge clk)  begin
           if (internal_sclr) begin
               top_priority_reg <= 1'b1;
           end
           else begin
               if (PIPELINE) begin
                   if (increment_top_priority) begin
                       top_priority_reg <= (|request) ? {grant[NUM_REQUESTERS-2:0],
                           grant[NUM_REQUESTERS-1]} : top_priority_reg;
                   end
               end else begin
                   if (increment_top_priority) begin
                       if (|request)
                           top_priority_reg <= { grant[NUM_REQUESTERS-2:0],
                               grant[NUM_REQUESTERS-1] };
                       else
                           top_priority_reg <= { top_priority_reg[NUM_REQUESTERS-2:0], top_priority_reg[NUM_REQUESTERS-1] };
                   end
                   else if (save_top_priority) begin
                       top_priority_reg <= grant; 
                   end
               end
           end
       end
   end : sync_rst0
   endgenerate
endmodule

// ----------------------------------------------
// Adder for the standard arbitrator
// ----------------------------------------------
module altera_merlin_arb_adder
#(
    parameter WIDTH = 8
)
(
    input [WIDTH-1:0] a,
    input [WIDTH-1:0] b,

    output [WIDTH-1:0] sum
);

    wire [WIDTH:0] sum_lint;
    // ----------------------------------------------
    // Benchmarks indicate that for small widths, the full
    // adder has higher fmax because synthesis can merge
    // it with the mux, allowing partial decisions to be 
    // made early.
    //
    // The magic number is 4 requesters, which means an
    // 8 bit adder.
    // ----------------------------------------------
    genvar i;
    generate if (WIDTH <= 8) begin : full_adder

        wire cout[WIDTH-1:0];

        assign sum[0]  = (a[0] ^ b[0]);
        assign cout[0] = (a[0] & b[0]);

        for (i = 1; i < WIDTH; i = i+1) begin : arb

            assign sum[i] = (a[i] ^ b[i]) ^ cout[i-1];
            assign cout[i] = (a[i] & b[i]) | (cout[i-1] & (a[i] ^ b[i]));

        end

    end else begin : carry_chain

        assign sum_lint = a + b;
        assign sum = sum_lint[WIDTH-1:0];

    end
    endgenerate

endmodule
`ifdef QUESTA_INTEL_OEM
`pragma questa_oem_00 "GdrtC8041f37ha52Ko+Jde808iDyKA+ht5m5AuKQCsm3cRPQscDvF+wBgbawWOxUtCRI9a/tnC6AChwO+BxfmEV2UK9ncMFAL//YMEMfhylNbbg+DkYNRltJ3oLac/x0CKLYUz0kP213IDPHPJdDrn2XWjqkg2d8WjL/DUsL13IJgiL6ltB1LI/UYnSBUYY+yK6OwicfHT3EuyorZ8lWql/zzL2Fl1behLT6A47M1qgP5IFV8ws6yR/FRb1NQVKWjRGihWG+9HZwhXEfbLrG802XGi+l6c0JKj9HK4yMYt3KC3qqbcGBpkO0mMiiEpPH0ssmrwVRuGBVTwtt1JvtkwEJ23Ncq/X/JXsMhlfrEsasziUfc9DVUO72f8EoHIIrcp56mTw9St/kjVV9jOQoSQJlQQTVocf//eaiEeU6eMV2W1qbjCeZUBYpMRWPc5Bw8aEgbG/tTNt8MwLKD16hPzlCR0UA5vV9iPsfuRAA0fxMu4Bfkz06le9lCgyLG2M/FnJMlmEZ8ON/vMSLrAPilnK+tOJ59JGY86IU2BLyPXhFhOBpPm0U/nU116vE7CY/iia2n6kchS/Sxgm7/BwSsgKyW5lBDCnAfnWaIk9VcjLy1BQV5+toWNeF8UvARWhuhpm0dJsVZA0zTLMbBPfCLztKUlsnu0V/IW9Wy6s0WuO+IX1VCUf+bexC3p+jalm8zuVrNrDGgNfgKgCKX1dqpHVT2rRAP54aU+oQ5HV1BOB62rV2hZjfXMbKnlhPtjdPWszYgD6Q9Fe3lAZ7WerOUmmmotFCjWxOyhtl/PQifYltRuB6pEqwTUcQDlxSA6lPkwmOFpp+wOnAr8ucx9bbGF2EiDN4n8+1As2Wgag+2HSBQmTavsbIsBGu6gfh803bylSyaTfwjyd/1Yb4+awyAQ0pFhcz7Nre5n/wwhTVsKwLpI1a+mKuItUqOfaIJ2mTWVNWNwI5SG4YrNm6JqpIwTOpFD5ZV5f8cxM0Uiwb5GIag93+kj+6PLbctUUdb5Ve"
`endif
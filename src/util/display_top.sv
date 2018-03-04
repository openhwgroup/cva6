// See LICENSE for license details.
`default_nettype none

module display_top
  (   
   // clock and reset
   input wire         clk,
   input wire         rst,
   
   output wire       CA,
   output wire       CB,
   output wire       CC,
   output wire       CD,
   output wire       CE,
   output wire       CF,
   output wire       CG,
   output wire       DP,
   output wire [7:0] AN,

   input wire [31:0] bcd_digits,
   output reg   redled
   );
    
   wire [8*7-1:0] digits;
   wire           overflow;

   assign redled = 'b0;
   
   genvar i;

   generate
      for (i = 0; i < 8; i = i + 1) begin
         sevensegment
            u_seg(.in  (bcd_digits[(i+1)*4-1:i*4]),
                  .out (digits[(i+1)*7-1:i*7]));
      end
   endgenerate

   nexys4ddr_display
     #(.FREQ(25000000))
   u_display(.clk       (clk),
             .rst       (rst),
             .digits    (digits),
             .decpoints (8'b00000000),
             .CA        (CA),
             .CB        (CB),
             .CC        (CC),
             .CD        (CD),
             .CE        (CE),
             .CF        (CF),
             .CG        (CG),
             .DP        (DP),
             .AN        (AN));

endmodule // display_top
`default_nettype wire

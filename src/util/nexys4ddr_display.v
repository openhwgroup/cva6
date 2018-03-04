/* Copyright (c) 2015-2016 by the author(s)
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in
 * all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
 * THE SOFTWARE.
 *
 * =============================================================================
 *
 * Seven segment display on the Nexys4 DDR board
 * 
 * Parameters:
 *  - FREQ: The frequency of the design, to match the second
 *  - REFRESH: Refresh rate in Hz
 *
 * Author(s):
 *   Stefan Wallentowitz <stefan.wallentowitz@tum.de>
 */

module nexys4ddr_display
  #(
    parameter FREQ = 32'hx,
    parameter REFRESH = 1200
    )
   (
    input wire            clk,
    input wire            rst,
    input wire [8*7-1:0]  digits,
    input wire [7:0]      decpoints,

    output wire           CA,
    output wire           CB,
    output wire           CC,
    output wire           CD,
    output wire           CE,
    output wire           CF,
    output wire           CG,
    output wire           DP,
    output reg [7:0]      AN
    );
   
   localparam REFRESH_CLKDIV = FREQ / (REFRESH * 8);

   reg               clk_refresh;
   reg [31:0]        count_refresh;

   always @(posedge clk) begin
      if (rst) begin
         clk_refresh <= 0;
         count_refresh <= REFRESH_CLKDIV >> 1;
      end else begin
         if (count_refresh == 0) begin
            count_refresh <= REFRESH_CLKDIV >> 1;
            clk_refresh <= ~clk_refresh;
         end else begin
            count_refresh <= count_refresh - 1;
         end
      end
   end

   wire [6:0]     digits_vector [0:7];

   assign digits_vector[0] = digits[6:0];
   assign digits_vector[1] = digits[13:7];
   assign digits_vector[2] = digits[20:14];
   assign digits_vector[3] = digits[27:21];
   assign digits_vector[4] = digits[34:28];
   assign digits_vector[5] = digits[41:35];
   assign digits_vector[6] = digits[48:42];
   assign digits_vector[7] = digits[55:49];
   
   reg [2:0]      an_count;
   
   always @(*) begin
      case (an_count)
        0: AN = 8'b11111110;
        1: AN = 8'b11111101;
        2: AN = 8'b11111011;
        3: AN = 8'b11110111;
        4: AN = 8'b11101111;
        5: AN = 8'b11011111;
        6: AN = 8'b10111111;
        7: AN = 8'b01111111;
      endcase
   end

   assign CA = ~digits_vector[an_count][0];
   assign CB = ~digits_vector[an_count][1];
   assign CC = ~digits_vector[an_count][2];
   assign CD = ~digits_vector[an_count][3];
   assign CE = ~digits_vector[an_count][4];
   assign CF = ~digits_vector[an_count][5];
   assign CG = ~digits_vector[an_count][6];
   assign DP = ~decpoints[an_count];
   
   always @(posedge clk_refresh) begin
      if (rst) begin
         an_count <= 0;
      end else begin
         an_count <= an_count + 1;
      end
   end

endmodule // nexys4ddr_display

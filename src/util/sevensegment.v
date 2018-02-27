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
 * Author(s):
 *   Stefan Wallentowitz <stefan.wallentowitz@tum.de>
 */

module sevensegment
  (input wire [3:0] in,
   output reg [6:0] out);

   always @(*) begin
      case (in)
        0:  out = 7'b0111111;
        1:  out = 7'b0000110;
        2:  out = 7'b1011011;
        3:  out = 7'b1001111;
        4:  out = 7'b1100110;
        5:  out = 7'b1101101;
        6:  out = 7'b1111101;
        7:  out = 7'b0000111;
        8:  out = 7'b1111111;
        9:  out = 7'b1101111;
        10: out = 7'b1110111;
        11: out = 7'b1111100;
        12: out = 7'b0111001;
        13: out = 7'b1011110;
        14: out = 7'b1111001;
        15: out = 7'b1110001;
      endcase // case (in)
   end
endmodule

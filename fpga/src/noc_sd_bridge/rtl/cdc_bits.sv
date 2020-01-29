// ========== Copyright Header Begin ============================================
// Copyright (c) 2019 Princeton University
// All rights reserved.
//
// Redistribution and use in source and binary forms, with or without
// modification, are permitted provided that the following conditions are met:
//     * Redistributions of source code must retain the above copyright
//       notice, this list of conditions and the following disclaimer.
//     * Redistributions in binary form must reproduce the above copyright
//       notice, this list of conditions and the following disclaimer in the
//       documentation and/or other materials provided with the distribution.
//     * Neither the name of Princeton University nor the
//       names of its contributors may be used to endorse or promote products
//       derived from this software without specific prior written permission.
//
// THIS SOFTWARE IS PROVIDED BY PRINCETON UNIVERSITY "AS IS" AND
// ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
// WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
// DISCLAIMED. IN NO EVENT SHALL PRINCETON UNIVERSITY BE LIABLE FOR ANY
// DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
// (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
// LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
// ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
// (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
// SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
// ========== Copyright Header End ============================================

// Cross-domain bit(s) synchronizer
//  - if WIDTH is greater than 1, the bits are independently synced. do not use
//      this directly for bus signals.
`ifdef PITON_FPGA_SYNTH
`define USE_XILINX_XPM
`endif
module cdc_bits (
    rst,
    src_clk, src,
    dst_clk, dst
    );

    parameter WIDTH = 1;

    input  wire                 rst;

    input  wire                 src_clk;
    input  wire [WIDTH - 1:0]   src;

    input  wire                 dst_clk;
    output wire [WIDTH - 1:0]   dst;

`ifdef USE_XILINX_XPM
    xpm_cdc_array_single #(
        .DEST_SYNC_FF(4)
        ,.WIDTH(WIDTH)
        ,.SRC_INPUT_REG(1)
    ) xpm_cdc_array_single_inst (
        .src_clk(src_clk)
        ,.src_in(src)
        ,.dest_clk(dst_clk)
        ,.dest_out(dst)
        );
`else
    reg [WIDTH - 1:0]   dst_f;
    assign dst = dst_f;

    genvar i;
    generate for (i = 0; i < WIDTH; i = i + 1) begin: cdc_bit
        reg [3:0] bit_f;   // 4-stage synchronizer

        always @(posedge src_clk or posedge rst) begin
            if (rst) begin
                bit_f[0]    <=  1'b0;
            end else begin
                bit_f[0]    <=  src[i];
            end
        end

        always @(posedge dst_clk or posedge rst) begin
            if (rst) begin
                {dst_f[i], bit_f[3:1]}  <=  4'h0;
            end else begin
                {dst_f[i], bit_f[3:1]}  <=  bit_f;
            end
        end
    end endgenerate
`endif

endmodule

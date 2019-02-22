// ========== Copyright Header Begin ============================================
// Copyright (c) 2015 Princeton University
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

//==================================================================================================
//  Filename      : piton_sd_buffer.v
//  Created On    : 2017-02-18
//  Last Modified : 2017-07-20 18:02:28
//  Revision      :
//  Author        : Ang Li
//  Company       : Princeton University
//  Email         : angl@princeton.edu
//
//  Description   : A fake memory provided for the SD card controller IP core to
//                  perform DMA accesses. The module adopts the Wishbone
//                  interface. Please refer to the SD card controller
//                  documentation for more details.
//==================================================================================================

`include "sd_defines.h"
`include "piton_sd_define.vh"

module piton_sd_buffer(
    // Shared SYSCON signals.
    input               clk,
    input               rst,

    // Wishbone Interface to SD card controller IP core.
    input       [31:0]  s_wb_dat_i, // Buffer reads from SD
    output  reg [31:0]  s_wb_dat_o, // Buffer writes to SD
    input       [31:0]  s_wb_adr_i, // only [8:2] are used.
    input       [3:0]   s_wb_sel_i, // Actually not used.
    input               s_wb_we_i,  // write enable.
    input               s_wb_cyc_i, // cycle enable.
    input               s_wb_stb_i, // strobing.
    output  reg         s_wb_ack_o, // acknowledgement.

    // Buffer read/write for SD card bridge.
    input       [31:0]              buf_addr_i, // address of the 8-byte
    input       [`NOC_DATA_BITS]    buf_data_i, // 8-byte per data input
                    // unit in the 512-byte block
    input                           buf_ce_i,   // request enable
    input                           buf_we_i,   // write enable
    input       [1:0]               buf_data_sz,
    output  reg [`NOC_DATA_BITS]    buf_data_o
    );

    // ------ Signals Declaration ------ //
    reg             bram_ena;
    reg  [0:7]      bram_wea;
    reg  [8:0]      bram_addr;
    reg  [0:63]     bram_din;
    wire [0:63]     bram_dout;

    reg             buf_rd_f;
    reg             wb_rd_f;
    reg             wb_wsel_f;

    // ------ Submodule Instantiation ------ //
    // 1 cycle read latency.
    sram #(
        .DATA_WIDTH ( 64  ),
        .NUM_WORDS  ( 512 )
    ) cache_bram (
        .clk_i ( clk ),
        .rst_ni ( ~rst ),
        .req_i ( bram_ena ),
        .we_i ( bram_wea ),
        .addr_i ( bram_addr ),
        .wdata_i ( bram_din ),
        .be_i ( 8'b1111_1111 ),
        .rdata_o ( bram_dout )
    );

    // sd_cache_bram cache_bram (
    //       .clka(clk),        // input wire clka
    //       .ena(bram_ena),    // input wire ena
    //       .wea(bram_wea),    // input wire [7 : 0] wea
    //       .addra(bram_addr), // input wire [8 : 0] addra
    //       .dina(bram_din),   // input wire [63 : 0] dina
    //       .douta(bram_dout)  // output wire [63 : 0] douta
    //     );

    // ------ Combinational Logic ------ //
    always @* begin
        bram_ena    =   1'b0;
        bram_addr   =   0;
        bram_wea    =   8'h0;
        bram_din    =   64'h0;

        s_wb_ack_o  =   wb_rd_f;
        s_wb_dat_o  =   bram_dout[{wb_wsel_f,   5'b0}   +:  32];
        buf_data_o  =   bram_dout;

        if (buf_ce_i) begin
            bram_ena    =   1'b1;
            bram_addr   =   buf_addr_i[11:3];
            if (buf_we_i) begin
                case (buf_data_sz)
                    2'd0:   begin
                        bram_wea[buf_addr_i[2:0]]                   =   1'h1;
                        bram_din[{buf_addr_i[2:0],  3'b0}   +:  8]  =   buf_data_i[7:0];
                    end
                    2'd1:   begin
                        bram_wea[{buf_addr_i[2:1],  1'b0}   +:  2]  =   2'h3;
                        bram_din[{buf_addr_i[2:1],  4'b0}   +:  16] =   buf_data_i[15:0];
                    end
                    2'd2:   begin
                        bram_wea[{buf_addr_i[2],    2'b0}   +:  4]  =   4'hf;
                        bram_din[{buf_addr_i[2],    5'b0}   +:  32] =   buf_data_i[31:0];
                    end
                    2'd3:   begin
                        bram_wea                                    =   8'hff;
                        bram_din                                    =   buf_data_i;
                    end
                endcase
            end
        end
        else if (s_wb_cyc_i && s_wb_stb_i && ~wb_rd_f) begin
            bram_ena    =   1'b1;
            bram_addr   =   s_wb_adr_i[11:3];
            if (s_wb_we_i) begin
                bram_wea[{s_wb_adr_i[2],    2'b0}   +:  4]  =   4'hf;
                bram_din[{s_wb_adr_i[2],    5'b0}   +:  32] =   s_wb_dat_i;
            end
        end
    end

    // ------ Sequential Logic ------ //
    always @(posedge clk or posedge rst) begin
        if (rst)    begin
            buf_rd_f    <=  1'b0;
            wb_rd_f     <=  1'b0;
            wb_wsel_f   <=  1'b0;
        end
        else begin
            if (buf_ce_i)   begin
                buf_rd_f    <=  1'b1;
                wb_rd_f     <=  1'b0;
            end
            else if (s_wb_cyc_i && s_wb_stb_i && ~wb_rd_f) begin
                buf_rd_f    <=  1'b0;
                wb_rd_f     <=  1'b1;
                wb_wsel_f   <=  s_wb_adr_i[2];
            end
            else begin
                buf_rd_f    <=  1'b0;
                wb_rd_f     <=  1'b0;
            end
        end
    end

endmodule

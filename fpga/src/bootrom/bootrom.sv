/* Copyright 2018 ETH Zurich and University of Bologna.
 * Copyright and related rights are licensed under the Solderpad Hardware
 * License, Version 0.51 (the "License"); you may not use this file except in
 * compliance with the License.  You may obtain a copy of the License at
 * http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
 * or agreed to in writing, software, hardware and materials distributed under
 * this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
 * CONDITIONS OF ANY KIND, either express or implied. See the License for the
 * specific language governing permissions and limitations under the License.
 *
 * File: $filename.v
 *
 * Description: Auto-generated bootrom
 */

// Auto-generated code
module bootrom (
   input  logic         clk_i,
   input  logic         req_i,
   input  logic [63:0]  addr_i,
   output logic [63:0]  rdata_o
);
    localparam int RomSize = 130;

    const logic [RomSize-1:0][63:0] mem = {
        64'h46454443_42413938,
        64'h37363534_33323130,
        64'h00000000_00000000,
        64'h00000000_00000000,
        64'h00000000_00000000,
        64'h00000000_00000000,
        64'h00000000_00000000,
        64'h00000000_00000000,
        64'h00000000_00000000,
        64'h00000000_00000000,
        64'h00000000_00000000,
        64'h00000000_00000000,
        64'h00000000_00000000,
        64'h00000000_00000000,
        64'h00000000_00000000,
        64'h00000000_00000000,
        64'h00000000_00000000,
        64'h00000000_00000000,
        64'h00000000_00000000,
        64'h00000000_00000000,
        64'h00000000_00000000,
        64'h00000000_00000000,
        64'h00000000_a001fbdf,
        64'hf0effe94_17e3dcdf,
        64'hf0ef0ff5_7513ff25,
        64'h0de3842a_f15ff0ef,
        64'h44b5597d_f35ff0ef,
        64'hdfbff0ef_e822e04a,
        64'he426ec06_08050513,
        64'h20058593_110102fa,
        64'hf53765f1_80820207,
        64'h80231000_07b78082,
        64'h0ff57513_0007c503,
        64'h00c78023_00b78023,
        64'h00a78023_01078023,
        64'h00e78023_01178023,
        64'h00d78023_00678023,
        64'h01c78023_00d78023,
        64'h00e78023_00e78023,
        64'h01d78023_01e78023,
        64'h00c78223_462900b7,
        64'h822345b5_00a78223,
        64'h02100513_01078223,
        64'h06400813_00e78223,
        64'h01178223_07200893,
        64'h00d78223_00678223,
        64'h05700313_01c78223,
        64'h02000e13_00d78223,
        64'h06f00693_00e78223,
        64'h00e78223_06c00713,
        64'h01d78223_06500e93,
        64'h01e78223_04800f13,
        64'h100007b7_80820ff5,
        64'h75130007_4503c789,
        64'h8b85557d_01474783,
        64'h10000737_80826105,
        64'h60e2ed1f_f0ef0091,
        64'h4503ed9f_f0ef0081,
        64'h4503f55f_f0efec06,
        64'h002c1101_80826145,
        64'h694264e2_740270a2,
        64'hff2410e3_efbff0ef,
        64'h00914503_f03ff0ef,
        64'h34610081_4503f81f,
        64'hf0ef0ff5_7513002c,
        64'h0084d533_59610380,
        64'h041384aa_f406e84a,
        64'hec26f022_71798082,
        64'h61456942_64e27402,
        64'h70a2ff24_10e3f3df,
        64'hf0ef0091_4503f45f,
        64'hf0ef3461_00814503,
        64'hfc3ff0ef_0ff57513,
        64'h002c0084_d53b5961,
        64'h446184aa_f406e84a,
        64'hec26f022_71798082,
        64'h00f58023_0007c783,
        64'h00e580a3_97aa8111,
        64'h00074703_973e00f5,
        64'h77132727_87930000,
        64'h0797b7f5_0405f95f,
        64'hf0ef8082_01416402,
        64'h60a2e509_00044503,
        64'h842ae406_e0221141,
        64'h808200e7_88230200,
        64'h071300e7_8423571d,
        64'h00e78623_470d00a7,
        64'h82230ff5_751300e7,
        64'h80230085_551b0ff5,
        64'h771300e7_8623f800,
        64'h07130007_82231000,
        64'h07b702b5_553b0045,
        64'h959b8082_00a70023,
        64'hdfe50207_f7930147,
        64'h47831000_07378082,
        64'h02057513_0147c503,
        64'h100007b7_80820ff5,
        64'h75130005_45038082,
        64'h00000000_00000000,
        64'h00000000_00000000,
        64'h00000000_00000000,
        64'h00000000_00000000,
        64'h00000000_00000000,
        64'h00000000_00000000,
        64'h00000000_00000000,
        64'h00000000_00000000,
        64'h00000000_00000000,
        64'hffdff06f_10500073,
        64'h34102373_342022f3,
        64'h278000ef_30579073,
        64'h01078793_00000797,
        64'hfec6c6e3_02068693,
        64'h0006bc23_0006b823,
        64'h0006b423_0006b023,
        64'h000580b3_01f59593,
        64'h0010059b_000600e7,
        64'h40e60633_f9c70713,
        64'h00000717_00e60633,
        64'h01c70713_00000717,
        64'h01f61613_0010061b,
        64'hfcc5cce3_02068693,
        64'h02058593_00e6bc23,
        64'h0185b703_00e6b823,
        64'h0105b703_00e6b423,
        64'h0085b703_00e6b023,
        64'h0005b703_01f69693,
        64'h0010069b_00c58633,
        64'h00008637_ff458593,
        64'h00000597_ff810113,
        64'h01b11113_0110011b
    };

    logic [$clog2(RomSize)-1:0] addr_q;

    always_ff @(posedge clk_i) begin
        if (req_i) begin
            addr_q <= addr_i[$clog2(RomSize)-1+3:3];
        end
    end

    // this prevents spurious Xes from propagating into
    // the speculative fetch stage of the core
    assign rdata_o = (addr_q < RomSize) ? mem[addr_q] : '0;
endmodule

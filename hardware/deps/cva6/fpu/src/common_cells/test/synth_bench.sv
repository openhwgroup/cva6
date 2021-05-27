// Copyright 2019 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

module synth_bench (
    input  logic        clk_i,
    input  logic        rst_ni,

    input  logic        src_rst_ni,
    input  logic        src_clk_i,
    input  logic [31:0] src_data_i,
    input  logic        src_valid_i,
    output logic        src_ready_o,

    input  logic        dst_rst_ni,
    input  logic        dst_clk_i,
    output logic [31:0] dst_data_o,
    output logic        dst_valid_o,
    input  logic        dst_ready_i
);

    cdc_2phase_synth i_cdc_2phase (
        .src_rst_ni     (src_rst_ni),
        .src_clk_i      (src_clk_i),
        .src_data_i     (src_data_i),
        .src_valid_i    (src_valid_i),
        .src_ready_o    (src_ready_o),

        .dst_rst_ni     (dst_rst_ni),
        .dst_clk_i      (dst_clk_i),
        .dst_data_o     (dst_data_o),
        .dst_valid_o    (dst_valid_o),
        .dst_ready_i    (dst_ready_i)
    );

    id_queue_synth i_id_queue (
        .clk_i  (clk_i),
        .rst_ni (rst_ni)
    );

    stream_arbiter_synth i_stream_arbiter (
        .clk_i,
        .rst_ni
    );

endmodule

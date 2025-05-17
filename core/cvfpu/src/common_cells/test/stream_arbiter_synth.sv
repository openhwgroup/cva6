// Copyright 2019 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

module stream_arbiter_synth (
    input  logic    clk_i,
    input  logic    rst_ni
);

    typedef logic data_t;
    for (genvar n = 2; n < 32; n += 3) begin : gen_n_inp
        data_t [n-1:0]  inp;
        logic  [n-1:0]  inp_valid, inp_rr_ready, inp_prio_ready;
        data_t          oup;
        logic           oup_rr_valid, oup_prio_valid, oup_ready;

        stream_arbiter #(
            .DATA_T     (data_t),
            .N_INP      (n),
            .ARBITER    ("rr")
        ) i_rr_arb (
            .clk_i,
            .rst_ni,
            .inp_data_i     (inp),
            .inp_valid_i    (inp_valid),
            .inp_ready_o    (inp_rr_ready),
            .oup_data_o     (oup),
            .oup_valid_o    (oup_rr_valid),
            .oup_ready_i    (oup_ready)
        );

        stream_arbiter #(
            .DATA_T     (data_t),
            .N_INP      (n),
            .ARBITER    ("prio")
        ) i_prio_arb (
            .clk_i,
            .rst_ni,
            .inp_data_i     (inp),
            .inp_valid_i    (inp_valid),
            .inp_ready_o    (inp_prio_ready),
            .oup_data_o     (oup),
            .oup_valid_o    (oup_prio_valid),
            .oup_ready_i    (oup_ready)
        );
    end

endmodule

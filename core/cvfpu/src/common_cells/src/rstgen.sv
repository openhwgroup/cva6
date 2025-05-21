// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Davide Rossi <davide.rossi@unibo.it>

module rstgen (
    input  logic clk_i,
    input  logic rst_ni,
    input  logic test_mode_i,
    output logic rst_no,
    output logic init_no
);

    rstgen_bypass i_rstgen_bypass (
        .clk_i            ( clk_i       ),
        .rst_ni           ( rst_ni      ),
        .rst_test_mode_ni ( rst_ni      ),
        .test_mode_i      ( test_mode_i ),
        .rst_no           ( rst_no      ),
        .init_no          ( init_no     )
    );

endmodule

// Copyright 2021 Thales DIS Design Services SAS
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     https://solderpad.org/licenses/
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0

module uvmt_cva6_dut_wrap # ( parameter int unsigned AXI_USER_WIDTH    = 1,
  parameter int unsigned AXI_ADDRESS_WIDTH = 64,
  parameter int unsigned AXI_DATA_WIDTH    = 64,
  parameter int unsigned NUM_WORDS         = 2**25
)

                           (
                            uvma_clknrst_if                     clknrst_if,
                            output wire                         tb_exit_o,
                            output ariane_rvfi_pkg::rvfi_port_t rvfi_o
                           );

    cva6_tb_wrapper #(     .AXI_USER_WIDTH    (1),
     .AXI_ADDRESS_WIDTH (64),
     .AXI_DATA_WIDTH    (64),
     .NUM_WORDS         (2**25)
)
    cva6_tb_wrapper_i        (
         .clk_i                  ( clknrst_if.clk                 ),
         .rst_ni                 ( clknrst_if.reset_n             ),
         .tb_exit_o              ( tb_exit_o),
         .rvfi_o                 ( rvfi_o)
         );

endmodule

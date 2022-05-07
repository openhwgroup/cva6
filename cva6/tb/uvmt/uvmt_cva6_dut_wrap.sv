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
  parameter int unsigned AXI_USER_EN       = 0,
  parameter int unsigned AXI_ADDRESS_WIDTH = 64,
  parameter int unsigned AXI_DATA_WIDTH    = 64,
  parameter int unsigned NUM_WORDS         = 2**25
)

                           (
                            uvma_clknrst_if                     clknrst_if,
                            uvma_cvxif_intf                     cvxif_if,
                            output wire                         tb_exit_o,
                            output ariane_rvfi_pkg::rvfi_port_t rvfi_o
                           );

    cva6_tb_wrapper #(
     .AXI_USER_WIDTH    (AXI_USER_WIDTH),
     .AXI_USER_EN       (AXI_USER_EN),
     .AXI_ADDRESS_WIDTH (AXI_ADDRESS_WIDTH),
     .AXI_DATA_WIDTH    (AXI_DATA_WIDTH),
     .NUM_WORDS         (NUM_WORDS)
)
    cva6_tb_wrapper_i        (
         .clk_i                  ( clknrst_if.clk                 ),
         .rst_ni                 ( clknrst_if.reset_n             ),
         .cvxif_resp             ( cvxif_if.cvxif_resp_o          ),
         .cvxif_req              ( cvxif_if.cvxif_req_i           ),
         .tb_exit_o              ( tb_exit_o                      ),
         .rvfi_o                 ( rvfi_o                         )
);

  assign cvxif_if.cvxif_resp_o.x_compressed_ready = 0;
  assign cvxif_if.cvxif_resp_o.x_compressed_resp  = 0;
  assign cvxif_if.cvxif_resp_o.x_issue_ready      = 1;
  assign cvxif_if.cvxif_resp_o.x_issue_resp       = 0;
  assign cvxif_if.cvxif_resp_o.x_result_valid     = 0;
  assign cvxif_if.cvxif_resp_o.x_result.id        = 0;
  assign cvxif_if.cvxif_resp_o.x_result.data      = 0;
  assign cvxif_if.cvxif_resp_o.x_result.rd        = 0;
  assign cvxif_if.cvxif_resp_o.x_result.we        = 0;
  assign cvxif_if.cvxif_resp_o.x_result.exc       = 0;
  assign cvxif_if.cvxif_resp_o.x_result.exccode   = 0;

endmodule

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

module uvmt_cva6_dut_wrap # (
  parameter config_pkg::cva6_cfg_t CVA6Cfg = config_pkg::cva6_cfg_empty,
  parameter type rvfi_instr_t = logic,
  parameter type rvfi_csr_elmt_t = logic,
  parameter type rvfi_csr_t = logic,
  parameter type rvfi_probes_instr_t = logic,
  parameter type rvfi_probes_csr_t = logic,
  parameter type rvfi_probes_t = logic,
  //
  parameter int unsigned AXI_USER_EN       = 0,
  parameter int unsigned NUM_WORDS         = 2**25
)

                           (
                            uvma_clknrst_if                     clknrst_if,
                            uvma_cvxif_intf                     cvxif_if,
                            uvma_axi_intf                       axi_if,
                            uvmt_axi_switch_intf                axi_switch_vif,
                            uvmt_default_inputs_intf            default_inputs_vif,
                            uvme_cva6_core_cntrl_if             core_cntrl_if,
                            output logic[31:0]                  tb_exit_o,
                            output rvfi_instr_t [CVA6Cfg.NrCommitPorts-1:0] rvfi_o,
                            output rvfi_csr_t                   rvfi_csr_o
                           );

    bit [CVA6Cfg.VLEN-1:0] boot_addr;

    assign boot_addr[31:0] = core_cntrl_if.boot_addr;
    cva6_tb_wrapper #(
     .CVA6Cfg ( CVA6Cfg ),
     .rvfi_instr_t      ( rvfi_instr_t      ),
     .rvfi_csr_elmt_t   ( rvfi_csr_elmt_t   ),
     .rvfi_csr_t        ( rvfi_csr_t        ),
     .rvfi_probes_instr_t(rvfi_probes_instr_t),
     .rvfi_probes_csr_t ( rvfi_probes_csr_t ),
     .rvfi_probes_t     ( rvfi_probes_t     ),
     //
     .AXI_USER_EN       (AXI_USER_EN),
     .NUM_WORDS         (NUM_WORDS)
)
    cva6_tb_wrapper_i        (
         .clk_i                  ( clknrst_if.clk                 ),
         .rst_ni                 ( clknrst_if.reset_n             ),
         .boot_addr_i            ( boot_addr                      ),
         .cvxif_resp             ( cvxif_if.cvxif_resp_o          ),
         .cvxif_req              ( cvxif_if.cvxif_req_i           ),
         .axi_slave              ( axi_if                         ),
         .axi_switch_vif         ( axi_switch_vif                 ),
         .default_inputs_vif     ( default_inputs_vif             ),
         .tb_exit_o              ( tb_exit_o                      ),
         .rvfi_csr_o             ( rvfi_csr_o                     ),
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

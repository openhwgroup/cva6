// Copyright 2020 OpenHW Group
// Copyright 2020 Datum Technologies
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

`ifndef __UVMT_CVA6_MACROS_SV__
`define __UVMT_CVA6_MACROS_SV__

// Assign for RVFI CSR interface
`define RVFI_CSR_ASSIGN(csr_name) \
      uvma_rvfi_csr_if#(uvme_cva6_pkg::XLEN)  rvfi_csr_``csr_name``_if [RVFI_NRET-1:0](); \
   for (genvar i = 0; i < RVFI_NRET; i++) begin \
      assign  rvfi_csr_``csr_name``_if[i].clk              = clknrst_if.clk; \
      assign  rvfi_csr_``csr_name``_if[i].reset_n          = clknrst_if.reset_n; \
      assign  rvfi_csr_``csr_name``_if[i].rvfi_csr_rmask   = rvfi_if.rvfi_csr_o.``csr_name``.rmask; \
      assign  rvfi_csr_``csr_name``_if[i].rvfi_csr_wmask   = rvfi_if.rvfi_csr_o.``csr_name``.wmask; \
      assign  rvfi_csr_``csr_name``_if[i].rvfi_csr_rdata   = rvfi_if.rvfi_csr_o.``csr_name``.rdata; \
      assign  rvfi_csr_``csr_name``_if[i].rvfi_csr_wdata   = rvfi_if.rvfi_csr_o.``csr_name``.wdata; \
   end \

`define RVFI_CSR_SUFFIX_ASSIGN(csr_name, idx) \
      uvma_rvfi_csr_if#(uvme_cva6_pkg::XLEN)  rvfi_csr_``csr_name````idx``_if [RVFI_NRET-1:0](); \
   for (genvar i = 0; i < RVFI_NRET; i++) begin \
      assign  rvfi_csr_``csr_name````idx``_if[i].clk              = clknrst_if.clk; \
      assign  rvfi_csr_``csr_name````idx``_if[i].reset_n          = clknrst_if.reset_n; \
      assign  rvfi_csr_``csr_name````idx``_if[i].rvfi_csr_rmask   = rvfi_if.rvfi_csr_o.``csr_name``[``idx``].rmask; \
      assign  rvfi_csr_``csr_name````idx``_if[i].rvfi_csr_wmask   = rvfi_if.rvfi_csr_o.``csr_name``[``idx``].wmask; \
      assign  rvfi_csr_``csr_name````idx``_if[i].rvfi_csr_rdata   = rvfi_if.rvfi_csr_o.``csr_name``[``idx``].rdata; \
      assign  rvfi_csr_``csr_name````idx``_if[i].rvfi_csr_wdata   = rvfi_if.rvfi_csr_o.``csr_name``[``idx``].wdata; \
   end \

// Create uvm_config_db::set call for a CSR interface
`define RVFI_CSR_UVM_CONFIG_DB_SET(csr_name, idx) \
  uvm_config_db#(virtual uvma_rvfi_csr_if)::set(.cntxt(null), \
                                                .inst_name("*"), \
                                                .field_name({"csr_", `"csr_name`", "_vif", $sformatf("%0d", ``idx``)}), \
                                                .value(rvfi_csr_``csr_name``_if[``idx``])); \

`endif // __UVMT_CVA6_MACROS_SV__

//
// Copyright 2020 OpenHW Group
// Copyright 2020 Datum Technology Corporation
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


`ifndef __UVMT_CV32E40S_MACROS_SV__
`define __UVMT_CV32E40S_MACROS_SV__


// Create bind for RVFI CSR interface
`define RVFI_CSR_BIND(csr_name) \
  bind cv32e40s_wrapper \
    uvma_rvfi_csr_if#(uvme_cv32e40s_pkg::XLEN) rvfi_csr_``csr_name``_if_0_i(.clk(clk_i), \
                                                                            .reset_n(rst_ni), \
                                                                            .rvfi_csr_rmask(rvfi_i.rvfi_csr_``csr_name``_rmask), \
                                                                            .rvfi_csr_wmask(rvfi_i.rvfi_csr_``csr_name``_wmask), \
                                                                            .rvfi_csr_rdata(rvfi_i.rvfi_csr_``csr_name``_rdata), \
                                                                            .rvfi_csr_wdata(rvfi_i.rvfi_csr_``csr_name``_wdata) \
    );

`define RVFI_CSR_IDX_BIND(csr_name,csr_suffix,idx) \
  bind cv32e40s_wrapper \
    uvma_rvfi_csr_if#(uvme_cv32e40s_pkg::XLEN) rvfi_csr_``csr_name````idx````csr_suffix``_if_0_i( \
                                                                           .clk(clk_i), \
                                                                           .reset_n(rst_ni), \
                                                                           .rvfi_csr_rmask(rvfi_i.rvfi_csr_``csr_name````csr_suffix``_rmask[``idx``]), \
                                                                           .rvfi_csr_wmask(rvfi_i.rvfi_csr_``csr_name````csr_suffix``_wmask[``idx``]), \
                                                                           .rvfi_csr_rdata(rvfi_i.rvfi_csr_``csr_name````csr_suffix``_rdata[``idx``]), \
                                                                           .rvfi_csr_wdata(rvfi_i.rvfi_csr_``csr_name````csr_suffix``_wdata[``idx``]) \
    );

// Create uvm_config_db::set call for a CSR interface
`define RVFI_CSR_UVM_CONFIG_DB_SET(csr_name) \
  uvm_config_db#(virtual uvma_rvfi_csr_if)::set(.cntxt(null), \
                                                .inst_name("*.env.rvfi_agent"), \
                                                .field_name({"csr_", `"csr_name`", "_vif0"}), \
                                                .value(dut_wrap.cv32e40s_wrapper_i.rvfi_csr_``csr_name``_if_0_i));

`endif // __UVMT_CV32E40S_MACROS_SV__

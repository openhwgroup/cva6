// Copyright 2020 OpenHW Group
// Copyright 2020 Datum Technology Corporation
// Copyright 2020 Silicon Labs, Inc.
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


`ifndef __UVMA_RVFI_CSR_IF_SV__
`define __UVMA_RVFI_CSR_IF_SV__

/**
 * Encapsulates all signals and clocking of RVFI csruction interface. Used by
 * monitor,
 */
interface uvma_rvfi_csr_if
  import uvma_rvfi_pkg::*;
  #(int XLEN=DEFAULT_XLEN)  
  (
    input                      clk,
    input                      reset_n,

    input [XLEN-1:0]           rvfi_csr_rmask,
    input [XLEN-1:0]           rvfi_csr_wmask,
    input [XLEN-1:0]           rvfi_csr_rdata,
    input [XLEN-1:0]           rvfi_csr_wdata
  );

  // -------------------------------------------------------------------
  // Local variables
  // -------------------------------------------------------------------

  // -------------------------------------------------------------------
  // Begin module code
  // -------------------------------------------------------------------
  
  /**
      * Used by target DUT.
  */
  clocking dut_cb @(posedge clk or reset_n);
  endclocking : dut_cb
  
  /**
      * Used by uvma_rvfi_csr_mon_c.
  */
  clocking mon_cb @(posedge clk or reset_n);
      input #1step  
        rvfi_csr_rmask,
        rvfi_csr_wmask,
        rvfi_csr_rdata,
        rvfi_csr_wdata;
  endclocking : mon_cb

  modport passive_mp    (clocking mon_cb);

endinterface : uvma_rvfi_csr_if


`endif // __UVMA_RVFI_CSR_IF_SV__

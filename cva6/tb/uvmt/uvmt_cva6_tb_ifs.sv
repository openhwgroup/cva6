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


// This file specifies all interfaces used by the CVA6 test bench (uvmt_cva6_tb).

`ifndef __UVMT_CVA6_TB_IFS_SV__
`define __UVMT_CVA6_TB_IFS_SV__


interface uvmt_rvfi_if (
                    output ariane_rvfi_pkg::rvfi_port_t  rvfi_o
                                 );

  import uvm_pkg::*;

  // TODO: X/Z checks
  initial begin
  end

endinterface : uvmt_rvfi_if


`endif // __UVMT_CVA6_TB_IFS_SV__

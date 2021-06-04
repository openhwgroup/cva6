// Copyright 2021 OpenHW Group
// Copyright 2021 Silicon Labs, Inc.
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


class uvma_isacov_mon_trn_logger_c extends uvml_logs_mon_trn_logger_c#(
    .T_TRN  (uvma_isacov_mon_trn_c),
    .T_CFG  (uvma_isacov_cfg_c),
    .T_CNTXT(uvma_isacov_cntxt_c)
);

  `uvm_component_utils(uvma_isacov_mon_trn_logger_c)

  extern function new(string name = "uvma_isacov_mon_trn_logger", uvm_component parent = null);
  extern virtual function void print_header();
  extern virtual function void write(uvma_isacov_mon_trn_c t);

endclass : uvma_isacov_mon_trn_logger_c


function uvma_isacov_mon_trn_logger_c::new(string name = "uvma_isacov_mon_trn_logger",
                                        uvm_component parent = null);

  super.new(name, parent);

endfunction : new


function void uvma_isacov_mon_trn_logger_c::print_header();

  fwrite("time\tinstr");

endfunction : print_header


function void uvma_isacov_mon_trn_logger_c::write(uvma_isacov_mon_trn_c t);

  fwrite($sformatf("%t\t%s", $time, t.convert2string()));

endfunction : write

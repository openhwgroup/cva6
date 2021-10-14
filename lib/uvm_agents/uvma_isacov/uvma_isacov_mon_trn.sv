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


class uvma_isacov_mon_trn_c#(int ILEN=DEFAULT_ILEN,
                             int XLEN=DEFAULT_XLEN) extends uvml_trn_mon_trn_c;

  `uvm_object_param_utils(uvma_isacov_mon_trn_c)

  uvma_isacov_instr_c#(ILEN, XLEN) instr;

  extern function new(string name = "uvma_isacov_mon_trn");

  extern function string convert2string();

endclass : uvma_isacov_mon_trn_c

function uvma_isacov_mon_trn_c::new(string name = "uvma_isacov_mon_trn");

  super.new(name);

endfunction : new

function string uvma_isacov_mon_trn_c::convert2string();

  return instr.convert2string();

endfunction : convert2string

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


class uvma_isacov_cntxt_c extends uvm_object;

  `uvm_object_utils(uvma_isacov_cntxt_c)

  extern function new(string name = "uvma_isacov_cntxt");

endclass : uvma_isacov_cntxt_c


function uvma_isacov_cntxt_c::new(string name = "uvma_isacov_cntxt");

  super.new(name);

endfunction : new

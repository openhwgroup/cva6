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


`ifndef __UVME_CV32E40X_BUSERR_SB_SV__
`define __UVME_CV32E40X_BUSERR_SB_SV__


class uvme_cv32e40x_buserr_sb_c extends uvm_scoreboard;

  `uvm_component_utils(uvme_cv32e40x_buserr_sb_c)

  extern function new(string name="uvme_cv32e40x_buserr_sb", uvm_component parent=null);

endclass : uvme_cv32e40x_buserr_sb_c


function uvme_cv32e40x_buserr_sb_c::new(string name="uvme_cv32e40x_buserr_sb", uvm_component parent=null);

  super.new(name, parent);

  $display("TODO hello buserr sb");

endfunction : new


`endif  // __UVME_CV32E40X_BUSERR_SB_SV__

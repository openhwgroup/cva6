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


module uvmt_cv32e40x_fencei_assert
  import uvm_pkg::*;
(
  input clk_i,
  input rst_ni,

  input fencei_flush_req_o,
  input fencei_flush_ack_i
);

  string info_tag = "CV32E40X_FENCEI_ASSERT";

  default clocking cb @(posedge clk_i); endclocking

  a_req_stay_high: assert property(
    fencei_flush_req_o && !fencei_flush_ack_i
    |=>
    fencei_flush_req_o
  ) else `uvm_error(info_tag, "req must not drop before ack");

endmodule : uvmt_cv32e40x_fencei_assert

// Copyright 2021 OpenHW Group
// Copyright 2021 Silicon Labs
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
//
// Licensed under the Solderpad Hardware License v 2.1 (the "License"); you may
// not use this file except in compliance with the License, or, at your option,
// the Apache License version 2.0. You may obtain a copy of the License at
//
//     https://solderpad.org/licenses/SHL-2.1/
//
// Unless required by applicable law or agreed to in writing, any work
// distributed under the License is distributed on an "AS IS" BASIS, WITHOUT
// WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the
// License for the specific language governing permissions and limitations
// under the License.


`ifndef __UVME_CV32E40X_VP_FENCEI_TAMPER_SEQ_SV__
`define __UVME_CV32E40X_VP_FENCEI_TAMPER_SEQ_SV__


class uvme_cv32e40x_vp_fencei_tamper_seq_c extends uvma_obi_memory_vp_base_seq_c;

  uvme_cv32e40x_cntxt_c cv32e40x_cntxt;

  `uvm_object_utils(uvme_cv32e40x_vp_fencei_tamper_seq_c)

  extern function new(string name="uvme_cv32e40x_vp_fencei_tamper_seq_c");
  extern virtual task vp_body(uvma_obi_memory_mon_trn_c mon_trn);
  extern virtual function int unsigned get_num_words();

endclass : uvme_cv32e40x_vp_fencei_tamper_seq_c


function uvme_cv32e40x_vp_fencei_tamper_seq_c::new(string name="uvme_cv32e40x_vp_fencei_tamper_seq_c");

  super.new(name);
$display("TODO hello fencei tamper");

endfunction : new


task uvme_cv32e40x_vp_fencei_tamper_seq_c::vp_body(uvma_obi_memory_mon_trn_c mon_trn);

endtask : vp_body


function int unsigned uvme_cv32e40x_vp_fencei_tamper_seq_c::get_num_words();

   return 2;

endfunction : get_num_words


`endif // __UVME_OBI_MEMORY_VP_FENCEI_TAMPER_SEQ_SV__

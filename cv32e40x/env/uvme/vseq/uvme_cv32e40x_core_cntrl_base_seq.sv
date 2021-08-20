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


`ifndef __UVME_CV32E40X_CORE_CNTRL_BASE_SEQ_C__
`define __UVME_CV32E40X_CORE_CNTRL_BASE_SEQ_C__

/**
 * Virtual sequence responsible for controlling fetch_en during tests
 */
class uvme_cv32e40x_core_cntrl_base_seq_c extends uvma_core_cntrl_base_seq_c;

   // Environment handles
   uvme_cv32e40x_cfg_c               cfg;
   uvma_cv32e40x_core_cntrl_cntxt_c  cntxt;

  `uvm_object_utils(uvme_cv32e40x_core_cntrl_base_seq_c)
  `uvm_declare_p_sequencer(uvma_core_cntrl_sqr_c)

  extern function new(string name = "");

  extern virtual task pre_start();

endclass : uvme_cv32e40x_core_cntrl_base_seq_c

function uvme_cv32e40x_core_cntrl_base_seq_c::new(string name = "");

  super.new(name);

endfunction : new

task uvme_cv32e40x_core_cntrl_base_seq_c::pre_start();

  if (!$cast(cfg, p_sequencer.cfg)) begin
    `uvm_fatal("E40XCORECNTRLSEQ", $sformatf("Could not cast p_sequencer.cfg to uvme_cv32e40x_cfg"))
  end

  if (!$cast(cntxt, p_sequencer.cntxt)) begin
    `uvm_fatal("E40XCORECNTRLSEQ", $sformatf("Could not cast p_sequencer.cntxt' to uvme_cv32e40x_cntxt'"))
  end

endtask : pre_start

`endif // __UVME_CV32E40X_CORE_CNTRL_BASE_SEQ_C__

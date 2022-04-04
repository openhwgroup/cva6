//
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
//

`ifndef __UVME_CV32E40S_VP_INTERRUPT_TIMER_SEQ_SV__
`define __UVME_CV32E40S_VP_INTERRUPT_TIMER_SEQ_SV__

/**
 * Sequence implementing the virtual status flags decoding
 */
class uvme_cv32e40s_vp_interrupt_timer_seq_c extends uvma_obi_memory_vp_interrupt_timer_seq_c;

   uvme_cv32e40s_cntxt_c cv32e40s_cntxt;

   `uvm_object_utils_begin(uvme_cv32e40s_vp_interrupt_timer_seq_c)
   `uvm_object_utils_end

   /**
    * Default constructor.
    */
   extern function new(string name="uvme_cv32e40s_vp_interrupt_timer_seq_c");

   /**
    * Asserts the actual interrupt wires
    */
   extern virtual task set_interrupt();

endclass : uvme_cv32e40s_vp_interrupt_timer_seq_c

function uvme_cv32e40s_vp_interrupt_timer_seq_c::new(string name="uvme_cv32e40s_vp_interrupt_timer_seq_c");

   super.new(name);

endfunction : new

task uvme_cv32e40s_vp_interrupt_timer_seq_c::set_interrupt();

   cv32e40s_cntxt.interrupt_cntxt.vif.drv_cb.irq_drv <= interrupt_value;

endtask : set_interrupt

`endif // __UVME_CV32E40S_VP_INTERRUPT_TIMER_SEQ_SV__

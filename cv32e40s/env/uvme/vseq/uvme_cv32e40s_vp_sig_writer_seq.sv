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

`ifndef __UVME_CV32E40S_VP_SIG_WRITE_SEQ_SV__
`define __UVME_CV32E40S_VP_SIG_WRITE_SEQ_SV__


/**
 * Sequence implementing the virtual status flags decoding
 */
class uvme_cv32e40s_vp_sig_writer_seq_c extends uvma_obi_memory_vp_sig_writer_seq_c;

   uvme_cv32e40s_cntxt_c cv32e40s_cntxt;

   `uvm_object_utils_begin(uvme_cv32e40s_vp_sig_writer_seq_c)
   `uvm_object_utils_end

   /**
    * Default constructor.
    */
   extern function new(string name="uvme_cv32e40s_vp_sig_writer_seq_c");

   /**
    * Implement a body to pre-validate some configuration before allowing parent class body to run
    */
   extern virtual task body();

   /**
    * Set virtual exit in core
    */
   extern virtual task set_exit_valid();

endclass : uvme_cv32e40s_vp_sig_writer_seq_c

function uvme_cv32e40s_vp_sig_writer_seq_c::new(string name="uvme_cv32e40s_vp_sig_writer_seq_c");

   super.new(name);

endfunction : new

task uvme_cv32e40s_vp_sig_writer_seq_c::body();

   if (cv32e40s_cntxt == null) begin
      `uvm_fatal("E40SVPSTATUS", "Must initialize cv32e40s_cntxt in virtual peripheral")
   end

   super.body();

endtask : body

task uvme_cv32e40s_vp_sig_writer_seq_c::set_exit_valid();

   cv32e40s_cntxt.vp_status_vif.exit_valid   = 1;
   cv32e40s_cntxt.vp_status_vif.exit_value   = 0;

endtask : set_exit_valid

`endif // __UVME_CV32E40S_VP_SIG_WRITER_SEQ_SV__

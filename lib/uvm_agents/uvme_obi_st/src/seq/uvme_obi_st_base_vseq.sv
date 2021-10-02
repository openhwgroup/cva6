// 
// Copyright 2021 OpenHW Group
// Copyright 2021 Datum Technology Corporation
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


`ifndef __UVME_OBI_ST_BASE_VSEQ_SV__
`define __UVME_OBI_ST_BASE_VSEQ_SV__


/**
 * Abstract object from which all other Open Bus Interface virtual sequences extend.
 * Does not generate any sequence items of its own. Subclasses must be run on
 * Open Bus Interface Virtual Sequencer (uvme_obi_st_vsqr_c) instance.
 */
class uvme_obi_st_base_vseq_c extends uvm_sequence#(
   .REQ(uvm_sequence_item),
   .RSP(uvm_sequence_item)
);
   
   // Environment handles
   uvme_obi_st_cfg_c    cfg;
   uvme_obi_st_cntxt_c  cntxt;
   
   
   `uvm_object_utils(uvme_obi_st_base_vseq_c)
   `uvm_declare_p_sequencer(uvme_obi_st_vsqr_c)
   
   
   /**
    * Default constructor.
    */
   extern function new(string name="uvme_obi_st_base_vseq");
   
   /**
    * Retrieve cfg and cntxt handles from p_sequencer.
    */
   extern virtual task pre_start();
   
endclass : uvme_obi_st_base_vseq_c


function uvme_obi_st_base_vseq_c::new(string name="uvme_obi_st_base_vseq");
   
   super.new(name);
   
endfunction : new


task uvme_obi_st_base_vseq_c::pre_start();
   
   cfg   = p_sequencer.cfg;
   cntxt = p_sequencer.cntxt;
   
endtask : pre_start


`endif // __UVME_OBI_ST_BASE_VSEQ_SV__

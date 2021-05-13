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


`ifndef __UVMT_OBI_ST_WRITES_TEST_SV__
`define __UVMT_OBI_ST_WRITES_TEST_SV__


/**
 * TODO Describe uvmt_obi_st_writes_test_c
 */
class uvmt_obi_st_writes_test_c extends uvmt_obi_st_base_test_c;
   
   rand uvme_obi_st_writes_vseq_c  writes_vseq;
   
   
   `uvm_component_utils(uvmt_obi_st_writes_test_c)
   
   /**
    * Creates writes_vseq.
    */
   extern function new(string name="uvmt_obi_st_writes_test", uvm_component parent=null);
   
   /**
    * Runs writes_vseq on vsequencer.
    */
   extern virtual task main_phase(uvm_phase phase);
   
   /**
    * TODO Describe uvmt_obi_st_writes_test_c::check_phase()
    */
   extern virtual function void check_phase(uvm_phase phase);
   
endclass : uvmt_obi_st_writes_test_c


function uvmt_obi_st_writes_test_c::new(string name="uvmt_obi_st_writes_test", uvm_component parent=null);
   
   super.new(name, parent);
   
   writes_vseq = uvme_obi_st_writes_vseq_c::type_id::create("writes_vseq");
   
endfunction : new


task uvmt_obi_st_writes_test_c::main_phase(uvm_phase phase);
   
   super.main_phase(phase);
   
   phase.raise_objection(this);
   `uvm_info("TEST", $sformatf("Starting writes virtual sequence:\n%s", writes_vseq.sprint()), UVM_NONE)
   writes_vseq.start(vsequencer);
   `uvm_info("TEST", $sformatf("Finished writes virtual sequence:\n%s", writes_vseq.sprint()), UVM_NONE)
   phase.drop_objection(this);
   
endtask : main_phase


function void uvmt_obi_st_writes_test_c::check_phase(uvm_phase phase);
   
   super.check_phase(phase);
   
   if (env_cntxt.sb_cntxt.match_count != writes_vseq.num_writes) begin
      `uvm_error("TEST", $sformatf("Number of scoreboard matches (%0d) does not equal number of writes (%0d)", env_cntxt.sb_cntxt.match_count, writes_vseq.num_writes))
   end
   
endfunction : check_phase


`endif // __UVMT_OBI_ST_WRITES_TEST_SV__

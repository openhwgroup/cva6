//
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
// 


`ifndef __UVMT_CV32_${name_uppercase}_TEST_SV__
`define __UVMT_CV32_${name_uppercase}_TEST_SV__


/**
 * TODO Describe uvmt_cv32_${name}_test_c
 */
class uvmt_cv32_${name}_test_c extends uvmt_cv32_base_test_c;
   
   // TODO Add virtual sequence(s) to uvmt_cv32_${name}_test_c
   // Ex: rand uvme_cv32_my_vseq_c  my_vseq;
   
   
   `uvm_component_utils(uvmt_cv32_${name}_test_c)
   
   
   constraint ${name}_cons {
      // TODO Add constraints to uvmt_cv32_${name}_test_c
      // Ex: env_cfg.abc == 100;
      //     my_vseq.xyz ==   5;
      //     watchdog_timeout == 200_000_000; // 200 ms
   }
   
   
   /**
    * Contructor function, performs factory overrides and creates all objects.
    * TODO Describe uvmt_cv32_${name}_test_c::new()
    */
   extern function new(string name="uvmt_cv32_${name}_test", uvm_component parent=null);
   
   /**
    * Executes test stimulus.
    * TODO Describe uvmt_cv32_${name}_test_c::main_phase()
    */
   extern virtual task main_phase(uvm_phase phase);
   
   /**
    * Performs test self-check to ensure stimulus, scoreboarding and checking
    * actually took place.
    * TODO Describe uvmt_cv32_${name}_test_c::check_phase()
    */
   extern virtual function void check_phase(uvm_phase phase);
   
endclass : uvmt_cv32_${name}_test_c


function uvmt_cv32_${name}_test_c::new(string name="uvmt_cv32_${name}_test", uvm_component parent=null);
   
   super.new(name, parent);
   
   // TODO Add factory overrides to uvmt_cv32_${name}_test_c
   // Ex: my_override_class_c::type_id:set_type_override(my_overriden_class_c.get_type());
   
   // TODO Create uvmt_cv32_${name}_test_c test objects
   // Ex: my_vseq = uvme_cv32_my_vseq_c::type_id::create("my_vseq");
   
endfunction : new


task uvmt_cv32_${name}_test_c::main_phase(uvm_phase phase);
   
   super.main_phase(phase);
   
   phase.raise_objection(this);
   // TODO Add stimulus to uvmt_cv32_${name}_test_c
   // Ex: `uvm_info("TEST", $sformatf("Starting my_vseq virtual sequence:\n%s", my_vseq.sprint()), UVM_NONE)
   //     my_vseq.start(vsequencer);
   //     `uvm_info("TEST", "Finished my_vseq virtual sequence", UVM_NONE)
   phase.drop_objection(this);
   
endtask : run_phase


function void uvmt_cv32_${name}_test_c::check_phase(uvm_phase phase);
   
   super.check_phase(phase);
   
   // TODO Implement uvmt_cv32_${name}_test_c::check_phase()
   // Ex: if (env_cntxt.abc > some_threshold) begin
   //       `uvm_error("TEST", "Hmmm, didn't expect that...")
   //     end
   
endfunction : check_phase


`endif // __UVMT_CV32_${name_uppercase}_SV__

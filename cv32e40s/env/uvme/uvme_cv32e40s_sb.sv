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


`ifndef __UVME_CV32E40S_SB_SV__
`define __UVME_CV32E40S_SB_SV__


/**
 * Component encapsulating scoreboards which compare CV32E40S
 * DUT's expected (from predictor) vs. actual (monitored) transactions.
 */
class uvme_cv32e40s_sb_c extends uvm_scoreboard;

   // Objects
   uvme_cv32e40s_cfg_c    cfg;
   uvme_cv32e40s_cntxt_c  cntxt;

   // Components
   // TODO Add sub-scoreboards
   //      Ex: uvme_cv32e40s_sb_simplex_c  egress_sb;
   //          uvme_cv32e40s_sb_simplex_c  ingress_sb;


   `uvm_component_utils_begin(uvme_cv32e40s_sb_c)
      `uvm_field_object(cfg  , UVM_DEFAULT)
      `uvm_field_object(cntxt, UVM_DEFAULT)

      // TODO Add sub-scoreboards field macros
      //      Ex: `uvm_field_object(egress_sb , UVM_DEFAULT)
      //          `uvm_field_object(ingress_sb, UVM_DEFAULT)
   `uvm_component_utils_end


   /**
    * Default constructor.
    */
   extern function new(string name="uvme_cv32e40s_sb", uvm_component parent=null);

   /**
    * Create and configures sub-scoreboards via:
    * 1. assign_cfg()
    * 2. assign_cntxt()
    * 3. create_sbs()
    */
   extern virtual function void build_phase(uvm_phase phase);

   /**
    * Assigns configuration handles.
    */
   extern virtual function void assign_cfg();

   /**
    * Assigns context handles.
    */
   extern virtual function void assign_cntxt();

   /**
    * Creates sub-scoreboard components.
    */
   extern virtual function void create_sbs();

endclass : uvme_cv32e40s_sb_c


function uvme_cv32e40s_sb_c::new(string name="uvme_cv32e40s_sb", uvm_component parent=null);

   super.new(name, parent);

endfunction : new


function void uvme_cv32e40s_sb_c::build_phase(uvm_phase phase);

   super.build_phase(phase);

   void'(uvm_config_db#(uvme_cv32e40s_cfg_c)::get(this, "", "cfg", cfg));
   if (!cfg) begin
      `uvm_fatal("CFG", "Configuration handle is null")
   end

   void'(uvm_config_db#(uvme_cv32e40s_cntxt_c)::get(this, "", "cntxt", cntxt));
   if (!cntxt) begin
      `uvm_fatal("CNTXT", "Context handle is null")
   end

   assign_cfg  ();
   assign_cntxt();
   create_sbs  ();

endfunction : build_phase


function void uvme_cv32e40s_sb_c::assign_cfg();

   // TODO Implement uvme_cv32e40s_sb_c::assign_cfg()
   //      Ex: uvm_config_db#(uvm_sb_cfg_c)::set(this, "egress_sb" , "cfg", cfg.sb_egress_cfg );
   //          uvm_config_db#(uvm_sb_cfg_c)::set(this, "ingress_sb", "cfg", cfg.sb_ingress_cfg);

endfunction : assign_cfg


function void uvme_cv32e40s_sb_c::assign_cntxt();

   // TODO Implement uvme_cv32e40s_sb_c::assign_cntxt()
   //      Ex: uvm_config_db#(uvme_cv32e40s_sb_cntxt_c)::set(this, "egress_sb" , "cntxt", cntxt.sb_egress_cntxt );
   //          uvm_config_db#(uvme_cv32e40s_sb_cntxt_c)::set(this, "ingress_sb", "cntxt", cntxt.sb_ingress_cntxt);

endfunction : assign_cntxt


function void uvme_cv32e40s_sb_c::create_sbs();

   // TODO Implement uvme_cv32e40s_sb_c::create_sbs()
   //      Ex: egress_sb  = uvme_cv32e40s_sb_simplex_c::type_id::create("egress_sb" , this);
   //          ingress_sb = uvme_cv32e40s_sb_simplex_c::type_id::create("ingress_sb", this);

endfunction : create_sbs


`endif // __UVME_CV32E40S_SB_SV__

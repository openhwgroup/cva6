// 
// Copyright 2020 OpenHW Group
// Copyright 2020 Datum Technology Corporation
// Copyright 2020 Silicon Labs, Inc.
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


`ifndef __UVMA_RVFI_AGENT_SV__
`define __UVMA_RVFI_AGENT_SV__

/**
 * Top-level component that encapsulates, builds and connects all others.
 * Capable of driving/monitoring Clock & Reset interface.
 */
class uvma_rvfi_agent_c#(int ILEN=DEFAULT_ILEN,
                         int XLEN=DEFAULT_XLEN) extends uvm_agent;
   
   // Objects
   uvma_rvfi_cfg_c#(ILEN,XLEN)    cfg;
   uvma_rvfi_cntxt_c#(ILEN,XLEN)  cntxt;
   
   // Components   
   uvma_rvfi_instr_mon_c#(ILEN,XLEN)               instr_monitor[];
   uvma_rvfi_mon_trn_logger_c#(ILEN,XLEN)          mon_trn_logger;
   
   // TLM   
   uvm_analysis_port#(uvma_rvfi_instr_seq_item_c#(ILEN,XLEN)) instr_mon_ap[];   
   
   `uvm_component_param_utils_begin(uvma_rvfi_agent_c)
      `uvm_field_object(cfg  , UVM_DEFAULT)
      `uvm_field_object(cntxt, UVM_DEFAULT)
   `uvm_component_utils_end
   
   /**
    * Default constructor.
    */
   extern function new(string name="uvma_rvfi_agent", uvm_component parent=null);
   
   /**
    * 1. Ensures cfg & cntxt handles are not null
    * 2. Builds all components
    */
   extern virtual function void build_phase(uvm_phase phase);
   
   /**
    * 1. Links agent's analysis ports to sub-components'
    * 2. Connects coverage models and loggers
    */
   extern virtual function void connect_phase(uvm_phase phase);
   
   /**
    * Uses uvm_config_db to retrieve cfg and hand out to sub-components.
    */
   extern function void get_and_set_cfg();
   
   /**
    * Uses uvm_config_db to retrieve cntxt and hand out to sub-components.
    */
   extern function void get_and_set_cntxt();
   
   /**
    * Uses uvm_config_db to retrieve the Virtual Interface (vif) associated with this
    * agent.
    */
   extern function void retrieve_vif();
   
   /**
    * Creates sub-components.
    */
   extern function void create_components();
   
   /**
    * Connects sequencer and driver's TLM port(s).
    */
   extern function void connect_sequencer_and_driver();
   
   /**
    * Connects agent's TLM ports to driver's and monitor's.
    */
   extern function void connect_analysis_ports();
   
   /**
    * Connects coverage model to monitor and driver's analysis ports.
    */
   extern function void connect_cov_model();
   
   /**
    * Connects transaction loggers to monitor and driver's analysis ports.
    */
   extern function void connect_trn_loggers();
   
endclass : uvma_rvfi_agent_c


function uvma_rvfi_agent_c::new(string name="uvma_rvfi_agent", uvm_component parent=null);
   
   super.new(name, parent);
   
endfunction : new


function void uvma_rvfi_agent_c::build_phase(uvm_phase phase);
   
   super.build_phase(phase);
   
   get_and_set_cfg  ();
   get_and_set_cntxt();
   retrieve_vif     ();
   create_components();
   
endfunction : build_phase


function void uvma_rvfi_agent_c::connect_phase(uvm_phase phase);
   
   super.connect_phase(phase);
   
   connect_sequencer_and_driver();
   connect_analysis_ports();
   
   if (cfg.cov_model_enabled) begin
      connect_cov_model();
   end
   if (cfg.trn_log_enabled) begin
      connect_trn_loggers();
   end
   
endfunction: connect_phase


function void uvma_rvfi_agent_c::get_and_set_cfg();
   
   void'(uvm_config_db#(uvma_rvfi_cfg_c#(ILEN,XLEN))::get(this, "", "cfg", cfg));
   if (!cfg) begin
      `uvm_fatal("CFG", "Configuration handle is null")
   end
   else begin
      `uvm_info("CFG", $sformatf("Found configuration handle:\n%s", cfg.sprint()), UVM_DEBUG)
      uvm_config_db#(uvma_rvfi_cfg_c#(ILEN,XLEN))::set(this, "*", "cfg", cfg);
   end
   
   instr_mon_ap = new[cfg.nret];   
endfunction : get_and_set_cfg


function void uvma_rvfi_agent_c::get_and_set_cntxt();
   
   void'(uvm_config_db#(uvma_rvfi_cntxt_c#(ILEN,XLEN))::get(this, "", "cntxt", cntxt));
   if (!cntxt) begin
      `uvm_info("CNTXT", "Context handle is null; creating.", UVM_DEBUG)
      cntxt = uvma_rvfi_cntxt_c#(ILEN,XLEN)::type_id::create("cntxt");
   end
   uvm_config_db#(uvma_rvfi_cntxt_c#(ILEN,XLEN))::set(this, "*", "cntxt", cntxt);
   
endfunction : get_and_set_cntxt


function void uvma_rvfi_agent_c::retrieve_vif();
   
   // Retrieve instruction interface
   cntxt.instr_vif = new[cfg.nret];
   for (int i = 0; i < cfg.nret; i++) begin
      if (!uvm_config_db#(virtual uvma_rvfi_instr_if#(ILEN,XLEN))::get(this, "", $sformatf("instr_vif%0d", i), cntxt.instr_vif[i])) begin
         `uvm_fatal("VIF", $sformatf("Could not find vif handle of type %s in uvm_config_db", 
                                     $typename(cntxt.instr_vif[i])))
      end
      else begin
         `uvm_info("VIF", $sformatf("Found vif handle of type %s in uvm_config_db", 
                                    $typename(cntxt.instr_vif[i])), UVM_DEBUG)
      end
   end

   // Create virtual interface and fetch virtual interface for each supported CSR
   begin
      string csrs[$];

      cfg.core_cfg.get_supported_csrs(csrs);

      foreach (csrs[c]) begin
         string csr = csrs[c].tolower();;
         cntxt.csr_vif[csr] = new[cfg.nret];

         for (int i = 0; i < cfg.nret; i++) begin
            if (!uvm_config_db#(virtual uvma_rvfi_csr_if#(XLEN))::get(this, "", $sformatf("csr_%s_vif%0d", csr, i), cntxt.csr_vif[csr][i])) begin
               `uvm_fatal("VIF", $sformatf("Could not find vif handle of type %s, csr [%s] in uvm_config_db",
                                           $typename(cntxt.csr_vif[csr][i]), csr))
            end else begin
               `uvm_info("VIF", $sformatf("Found vif handle of type %s, csr [%s] in uvm_config_db",
                                          $typename(cntxt.csr_vif[csr][i]), csr), UVM_DEBUG)
            end
         end
      end
   end

endfunction : retrieve_vif


function void uvma_rvfi_agent_c::create_components();

   instr_monitor = new[cfg.nret];
   for (int i = 0; i < cfg.nret; i++) begin
      instr_monitor[i] = uvma_rvfi_instr_mon_c#(ILEN,XLEN)::type_id::create($sformatf("instr_monitor%0d", i), this);
      instr_monitor[i].nret_id = i;
   end   
   mon_trn_logger         = uvma_rvfi_mon_trn_logger_c#(ILEN,XLEN)::type_id::create("mon_trn_logger" , this);   
   
endfunction : create_components


function void uvma_rvfi_agent_c::connect_sequencer_and_driver();
      
endfunction : connect_sequencer_and_driver


function void uvma_rvfi_agent_c::connect_analysis_ports();
      
   for (int i = 0; i < cfg.nret; i++) begin
      instr_mon_ap[i] = instr_monitor[i].ap;
   end

endfunction : connect_analysis_ports


function void uvma_rvfi_agent_c::connect_cov_model();
   
   //mon_ap.connect(cov_model.mon_trn_fifo.analysis_export);   
   
endfunction : connect_cov_model


function void uvma_rvfi_agent_c::connect_trn_loggers();
   
   for (int i = 0; i < cfg.nret; i++) begin
      instr_mon_ap[i].connect(mon_trn_logger.instr_export);
   end

endfunction : connect_trn_loggers


`endif // __UVMA_RVFI_AGENT_SV__

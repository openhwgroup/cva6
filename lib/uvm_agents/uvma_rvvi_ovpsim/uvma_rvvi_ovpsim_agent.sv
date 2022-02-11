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


`ifndef __UVMA_RVVI_OVPSIM_AGENT_SV__
`define __UVMA_RVVI_OVPSIM_AGENT_SV__

/**
 * Top-level component that encapsulates, builds and connects all others.
 * Capable of driving/monitoring Clock & Reset interface.
 */
class uvma_rvvi_ovpsim_agent_c#(int ILEN=uvma_rvvi_pkg::DEFAULT_ILEN,
                                int XLEN=uvma_rvvi_pkg::DEFAULT_XLEN) extends uvma_rvvi_agent_c#(ILEN,XLEN);

   `uvm_component_param_utils_begin(uvma_rvvi_ovpsim_agent_c#(ILEN,XLEN))
   `uvm_component_utils_end

   /**
    * Default constructor.
    */
   extern function new(string name="uvma_rvvi_ovpsim_agent", uvm_component parent=null);

   /**
    * End of elaboration phase
    * 1. Emit ovpsim.ic control file
    */
   extern function void end_of_elaboration_phase(uvm_phase phase);

   /**
    * Emit ovpsim.ic control file based on core configuration
    */
   extern virtual function void configure_iss();


   /**
    * Uses uvm_config_db to retrieve the Virtual Interface (vif) associated with this
    * agent.
    */
   extern virtual function void retrieve_vif();

   /**
    * Creates sub-components.
    */
   extern virtual function void create_components();

   /**
    * Uses uvm_config_db to retrieve cntxt and hand out to sub-components.
    */
   extern virtual function void get_and_set_cntxt();

   /**
    * Provide sequencer for RVVI OVPSIM driver to manage clocks for step and compare
    */
   extern function void set_clknrst_sequencer(uvma_clknrst_sqr_c clknrst_sequencer);

   /**
    *  run_phase will kick off the control sequence that runs the duration
    *  of the simulation (if this agent is active)
    */
   extern virtual task run_phase(uvm_phase phase);

endclass : uvma_rvvi_ovpsim_agent_c


function uvma_rvvi_ovpsim_agent_c::new(string name="uvma_rvvi_ovpsim_agent", uvm_component parent=null);

   super.new(name, parent);

   log_tag = "RVVIOVPAGT";

endfunction : new

function void uvma_rvvi_ovpsim_agent_c::end_of_elaboration_phase(uvm_phase phase);

   super.end_of_elaboration_phase(phase);

   if (cfg.is_active == UVM_ACTIVE)
      configure_iss();

endfunction : end_of_elaboration_phase


function void uvma_rvvi_ovpsim_agent_c::configure_iss();

   // Append options from the core configuration into the ovpsim.ic file to ensure the Imperas ISS
   // is configured as the core this RVVI is attached to
   // File is opened in append mode because the Makefile creates an ovpsim.ic file before test execution
   // and populates any configuration YAML defined options
   // Note that such use shoulbe be for testing only and nearly all ovpsim.ic switches should be integrated to this method

   int fh;

   fh = $fopen(cfg.core_cfg.iss_control_file, "a");

   // -------------------------------------------------------------------------------------
   // ISA Extension support
   // -------------------------------------------------------------------------------------
   $fwrite(fh, $sformatf("--override root/cpu/misa_Extensions=0x%06x\n", cfg.core_cfg.get_misa()));
  // TODO: cv32e40x: Remove when correct setting is applied to ovpsim
  if (cfg.core_cfg.core_name == "CV32E40X") begin
      $fwrite(fh, $sformatf("--override root/cpu/tcontrol_undefined=0\n"));
  end

   if (cfg.core_cfg.is_ext_b_supported()) begin
      // Bitmanip version
      case (cfg.core_cfg.bitmanip_version)
         BITMANIP_VERSION_0P90:       $fwrite(fh, $sformatf("--override root/cpu/bitmanip_version=0.90\n"));
         BITMANIP_VERSION_0P91:       $fwrite(fh, $sformatf("--override root/cpu/bitmanip_version=0.91\n"));
         BITMANIP_VERSION_0P92:       $fwrite(fh, $sformatf("--override root/cpu/bitmanip_version=0.92\n"));
         BITMANIP_VERSION_0P93:       $fwrite(fh, $sformatf("--override root/cpu/bitmanip_version=0.93\n"));
         BITMANIP_VERSION_0P93_DRAFT: $fwrite(fh, $sformatf("--override root/cpu/bitmanip_version=0.93-draft\n"));
         BITMANIP_VERSION_0P94:       $fwrite(fh, $sformatf("--override root/cpu/bitmanip_version=0.94\n"));
         BITMANIP_VERSION_1P00:       $fwrite(fh, $sformatf("--override root/cpu/bitmanip_version=1.0.0\n"));
      endcase

      // Bitmanip extensions
      $fwrite(fh, $sformatf("--override root/cpu/Zba=%0d\n", cfg.core_cfg.ext_zba_supported));
      $fwrite(fh, $sformatf("--override root/cpu/Zbb=%0d\n", cfg.core_cfg.ext_zbb_supported));
      $fwrite(fh, $sformatf("--override root/cpu/Zbc=%0d\n", cfg.core_cfg.ext_zbc_supported));
      $fwrite(fh, $sformatf("--override root/cpu/Zbe=%0d\n", cfg.core_cfg.ext_zbe_supported));
      $fwrite(fh, $sformatf("--override root/cpu/Zbf=%0d\n", cfg.core_cfg.ext_zbf_supported));
      $fwrite(fh, $sformatf("--override root/cpu/Zbm=%0d\n", cfg.core_cfg.ext_zbm_supported));
      $fwrite(fh, $sformatf("--override root/cpu/Zbp=%0d\n", cfg.core_cfg.ext_zbp_supported));
      $fwrite(fh, $sformatf("--override root/cpu/Zbr=%0d\n", cfg.core_cfg.ext_zbr_supported));
      $fwrite(fh, $sformatf("--override root/cpu/Zbs=%0d\n", cfg.core_cfg.ext_zbs_supported));
      $fwrite(fh, $sformatf("--override root/cpu/Zbt=%0d\n", cfg.core_cfg.ext_zbt_supported));
   end

   case(cfg.core_cfg.priv_spec_version)
     PRIV_VERSION_MASTER:   $fwrite(fh, $sformatf("--override root/cpu/priv_version=master\n"));
     PRIV_VERSION_1_10:     $fwrite(fh, $sformatf("--override root/cpu/priv_version=1.10\n"));
     PRIV_VERSION_1_11:     $fwrite(fh, $sformatf("--override root/cpu/priv_version=1.11\n"));
     PRIV_VERSION_20190405: $fwrite(fh, $sformatf("--override root/cpu/priv_version=20190405\n"));
   endcase

   if (cfg.core_cfg.priv_spec_version == PRIV_VERSION_MASTER) begin
     case(cfg.core_cfg.endianness)
       ENDIAN_LITTLE, ENDIAN_BIG: $fwrite(fh, $sformatf("--override root/cpu/endianFixed=1\n"));
       ENDIAN_MIXED:              $fwrite(fh, $sformatf("--override root/cpu/endianFixed=0\n"));
     endcase
   end


   // -------------------------------------------------------------------------------------
   // Boot strap pins
   // -------------------------------------------------------------------------------------
   $fwrite(fh, $sformatf("--override root/cpu/mhartid=%0d\n", cfg.core_cfg.mhartid));
   $fwrite(fh, $sformatf("--override root/cpu/mimpid=%0d\n", cfg.core_cfg.mimpid));
   $fwrite(fh, $sformatf("--override root/cpu/startaddress=0x%08x\n", cfg.core_cfg.boot_addr));
   // Specification forces mtvec[0] high at reset regardless of bootstrap pin state of mtvec_addr_i]0]
   $fwrite(fh, $sformatf("--override root/cpu/mtvec=0x%08x\n", cfg.core_cfg.mtvec_addr| 32'h1));
   $fwrite(fh, $sformatf("--override root/cpu/nmi_address=0x%08x\n", cfg.core_cfg.nmi_addr));
   $fwrite(fh, $sformatf("--override root/cpu/debug_address=0x%08x\n", cfg.core_cfg.dm_halt_addr));
   $fwrite(fh, $sformatf("--override root/cpu/dexc_address=0x%08x\n", cfg.core_cfg.dm_exception_addr));

   // -------------------------------------------------------------------------------------
   // Parameters
   // -------------------------------------------------------------------------------------

   // NUM_MHPMCOUNTERS - Set zero in the noinhibit_mask to enable a counter, starting from index 3
   $fwrite(fh, $sformatf("--override root/cpu/noinhibit_mask=0x%08x\n", cfg.core_cfg.get_noinhibit_mask()));

   // PMA Regions
   $fwrite(fh, $sformatf("--override root/cpu/extension/PMA_NUM_REGIONS=%0d\n", cfg.core_cfg.pma_regions.size()));
   foreach (cfg.core_cfg.pma_regions[i]) begin
      $fwrite(fh, $sformatf("--override root/cpu/extension/word_addr_low%0d=0x%08x\n", i, cfg.core_cfg.pma_regions[i].word_addr_low));
      $fwrite(fh, $sformatf("--override root/cpu/extension/word_addr_high%0d=0x%08x\n", i, cfg.core_cfg.pma_regions[i].word_addr_high));
      $fwrite(fh, $sformatf("--override root/cpu/extension/main%0d=%0d\n", i, cfg.core_cfg.pma_regions[i].main));
      $fwrite(fh, $sformatf("--override root/cpu/extension/bufferable%0d=%0d\n", i, cfg.core_cfg.pma_regions[i].bufferable));
      $fwrite(fh, $sformatf("--override root/cpu/extension/cacheable%0d=%0d\n", i, cfg.core_cfg.pma_regions[i].cacheable));
      $fwrite(fh, $sformatf("--override root/cpu/extension/atomic%0d=%0d\n", i, cfg.core_cfg.pma_regions[i].atomic));
   end

   $fclose(fh);

endfunction : configure_iss

function void uvma_rvvi_ovpsim_agent_c::get_and_set_cntxt();

   super.get_and_set_cntxt();

endfunction : get_and_set_cntxt

function void uvma_rvvi_ovpsim_agent_c::set_clknrst_sequencer(uvma_clknrst_sqr_c clknrst_sequencer);

   uvma_rvvi_ovpsim_drv_c#(ILEN,XLEN) rvvi_ovpsim_driver;

   // Cast into the OVPSIM context to get access to the BUS interface
   if (!$cast(rvvi_ovpsim_driver, driver)) begin
      `uvm_fatal(log_tag, "Failed to cast RVVI driver to RVVI ovpsim_driver");
   end
   rvvi_ovpsim_driver.clknrst_sequencer = clknrst_sequencer;

endfunction : set_clknrst_sequencer

function void uvma_rvvi_ovpsim_agent_c::retrieve_vif();

   uvma_rvvi_ovpsim_cntxt_c#(ILEN,XLEN) rvvi_ovpsim_cntxt;

   // Cast into the OVPSIM context to get access to the BUS interface
   if (!$cast(rvvi_ovpsim_cntxt, cntxt)) begin
      `uvm_fatal(log_tag, "Failed to cast RVVI cntxt to RVVI ovpsim_cntxt");
   end

   super.retrieve_vif();

   // OVPSIM BUS VIF : FIXME:strichmo:would be ideal to incorporate into common rvvi
   if (!uvm_config_db#(virtual RVVI_bus)::get(this, "", $sformatf("ovpsim_bus_vif"), rvvi_ovpsim_cntxt.ovpsim_bus_vif)) begin
      `uvm_fatal("VIF", $sformatf("Could not find vif handle of type %s in uvm_config_db",
                                    $typename(rvvi_ovpsim_cntxt.ovpsim_bus_vif)))
   end
   else begin
      `uvm_info("VIF", $sformatf("Found vif handle of type %s in uvm_config_db",
                                 $typename(rvvi_ovpsim_cntxt.ovpsim_bus_vif)), UVM_DEBUG)
   end

   if (!uvm_config_db#(virtual RVVI_io)::get(this, "", $sformatf("ovpsim_io_vif"), rvvi_ovpsim_cntxt.ovpsim_io_vif)) begin
      `uvm_fatal("VIF", $sformatf("Could not find vif handle of type %s in uvm_config_db",
                                    $typename(rvvi_ovpsim_cntxt.ovpsim_io_vif)))
   end
   else begin
      `uvm_info("VIF", $sformatf("Found vif handle of type %s in uvm_config_db",
                                 $typename(rvvi_ovpsim_cntxt.ovpsim_io_vif)), UVM_DEBUG)
   end

   if (!uvm_config_db#(virtual RVVI_memory)::get(this, "", $sformatf("ovpsim_mem_vif"), rvvi_ovpsim_cntxt.ovpsim_mem_vif)) begin
      `uvm_fatal("VIF", $sformatf("Could not find vif handle of type %s in uvm_config_db",
                                    $typename(rvvi_ovpsim_cntxt.ovpsim_mem_vif)))
   end
   else begin
      `uvm_info("VIF", $sformatf("Found vif handle of type %s in uvm_config_db",
                                 $typename(rvvi_ovpsim_cntxt.ovpsim_mem_vif)), UVM_DEBUG)
   end

endfunction : retrieve_vif


function void uvma_rvvi_ovpsim_agent_c::create_components();

   state_monitor   = uvma_rvvi_ovpsim_state_mon_c#(ILEN,XLEN)::type_id::create("state_monitor"  , this);
   mon_trn_logger  = uvma_rvvi_mon_trn_logger_c#(ILEN,XLEN)::type_id::create("mon_trn_logger" , this);

   if (cfg.is_active == UVM_ACTIVE) begin
      sequencer = uvma_rvvi_sqr_c#(ILEN,XLEN)::type_id::create("sequencer", this);
      driver = uvma_rvvi_ovpsim_drv_c#(ILEN,XLEN)::type_id::create("driver", this);
   end

endfunction : create_components

task uvma_rvvi_ovpsim_agent_c::run_phase(uvm_phase phase);

   super.run_phase(phase);

   if (cfg.is_active == UVM_ACTIVE) begin
      uvma_rvvi_ovpsim_control_seq_c#(ILEN,XLEN) control_seq = uvma_rvvi_ovpsim_control_seq_c#(ILEN, XLEN)::type_id::create("control_seq");

      `uvm_info("RVVIOVPAGT", "Starting the RVVI sequences...", UVM_LOW);
      fork
         control_seq.start(sequencer);
      join_none
   end

endtask : run_phase



`endif // __UVMA_RVVI_OVPSIM_AGENT_SV__

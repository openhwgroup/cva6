//
// Copyright 2020 OpenHW Group
// Copyright 2020 Datum Technologies
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



`ifndef __UVMT_CV32_BASE_TEST_SV__
`define __UVMT_CV32_BASE_TEST_SV__


/**
 * Abstract component from which all other CV32 test cases must
 * ultimately extend.
 * Subclasses must provide stimulus via the virtual sequencer by implementing
 * UVM runtime phases.
 */
class uvmt_cv32_base_test_c extends uvm_test;
   
   // Objects
   rand uvmt_cv32_test_cfg_c  test_cfg ;
   rand uvme_cv32_cfg_c       env_cfg  ;
   uvme_cv32_cntxt_c          env_cntxt;
   //uvml_logs_rs_text_c        rs       ;
   //uvme_cv32_ral_c            ral      ;
   //uvml_logs_reg_logger_cbs_c reg_cbs  ;
   
   // Components
   uvme_cv32_env_c   env       ;
   //uvme_cv32_vsqr_c  vsequencer;
   
   // Handle to clock generation interface
   virtual uvmt_cv32_clk_gen_if  clk_gen_vif;
   
   // Knobs
   rand int unsigned  heartbeat_period; // Specified in nanoseconds (ns)
   rand int unsigned  watchdog_timeout; // Specified in nanoseconds (ns)
   
   // Default sequences
   //rand uvme_cv32_reset_vseq_c  reset_vseq;
   
   
   `uvm_component_utils_begin(uvmt_cv32_base_test_c)
      `uvm_field_object(test_cfg , UVM_DEFAULT)
      `uvm_field_object(env_cfg  , UVM_DEFAULT)
      `uvm_field_object(env_cntxt, UVM_DEFAULT)
      
      `uvm_field_int(heartbeat_period, UVM_DEFAULT)
      `uvm_field_int(watchdog_timeout, UVM_DEFAULT)
   `uvm_component_utils_end
   
   
   constraint timeouts_default_cons {
      soft heartbeat_period ==    200_000; //  2 us // TODO Set default Heartbeat Monitor period for uvmt_cv32_base_test_c
      soft watchdog_timeout == 10_000_000; // 10 ms // TODO Set default Watchdog timeout period for uvmt_cv32_base_test_c
   }
   
   //constraint env_cfg_cons {
   //   env_cfg.enabled         == 1;
   //   env_cfg.is_active       == UVM_ACTIVE;
   //   env_cfg.trn_log_enabled == 1;
   //}
   
   
   // Additional, temporary constraints to get around known design bugs/constraints
   `include "uvmt_cv32_base_test_workarounds.sv"
   
   
   /**
    * 1. Replaces default report server with rs.
    * 2. Creates reset_vseq.
    */
   extern function new(string name="uvmt_cv32_base_test", uvm_component parent=null);
   
   /**
    * 1. Builds test_cfg & env_cfg via create_cfg()
    * 2. Randomizes entire test class via randomize_test()
    * 3. Passes env_cfg to env via uvm_config_db via assign_cfg()
    * 4. Builds env_cntxt via create_cntxt()
    * 5. Passes env_cntxt to env using UVM Configuration Database via assign_cntxt()
    * 6. Builds env via create_env()
    * 7. Builds the rest of the components/objects via create_components()
    */
   extern virtual function void build_phase(uvm_phase phase);
   
   /**
    * 1. Assigns environment's virtual sequencer handle to vsequencer.
    * 2. Add register callback (reg_cbs) to all registers & fields.
    */
   extern virtual function void connect_phase(uvm_phase phase);
   
   /**
    * 1. Triggers the start of clock generation via start_clk()
    * 2. Starts the watchdog timeout via watchdog_timeout()
    */
   extern virtual task run_phase(uvm_phase phase);
   
   /**
    * Runs reset_vseq.
    */
   extern virtual task reset_phase(uvm_phase phase);
   
   /**
    * Writes contents of RAL to the DUT.
    */
   extern virtual task configure_phase(uvm_phase phase);
   
   /**
    * Prints out start of phase banners.
    */
   extern virtual function void phase_started(uvm_phase phase);
   
   /**
    * Indicates to the test bench (uvmt_cv32_tb) that the test has completed.
    * This is done by checking the properties of the phase argument.
    */
   extern virtual function void phase_ended(uvm_phase phase);
   
   /**
    * Retrieves clk_gen_vif from UVM configuration database.
    */
   extern function void retrieve_clk_gen_vif();
   
   /**
    * Creates test_cfg and env_cfg. Assigns ral handle to env_cfg's.
    */
   extern virtual function void create_cfg();
   
   /**
    * 1. Calls test_cfg's process_cli_args()
    * 2. Calls randomize on 'this' and fatals out if it fails.
    */
   extern virtual function void randomize_test();
   
   /**
    * Configures uvml_default_hrtbt_monitor.
    */
   extern function void cfg_hrtbt_monitor();
   
   /**
    * Assigns environment configuration (env_cfg) handle to environment (env)
    * using UVM Configuration Database.
    */
   extern virtual function void assign_cfg();
   
   /**
    * Creates env_cntxt.
    */
   extern virtual function void create_cntxt();
   
   /**
    * Assigns environment context (env_cntxt) handle to environment (env) using
    * UVM Configuration Database.
    */
   extern virtual function void assign_cntxt();
   
   /**
    * Creates env.
    */
   extern virtual function void create_env();
   
   /**
    * Creates additional (non-environment) components (and objects).
    */
   extern virtual function void create_components();
   
   /**
    * Prints overlined and underlined text in uppercase.
    */
   extern function void print_banner(string text);
   
   /**
    * Starts clock generation via clk_gen_vif functions.
    */
   extern virtual task start_clk();
   
   /**
    * Fatals out after watchdog_timeout has elapsed.
    */
   extern virtual task watchdog_timer();
   
endclass : uvmt_cv32_base_test_c


function uvmt_cv32_base_test_c::new(string name="uvmt_cv32_base_test", uvm_component parent=null);
   
   super.new(name, parent);
   
   //rs = new("rs");
   //uvm_report_server::set_server(rs);
   //reset_vseq = uvme_cv32_reset_vseq_c::type_id::create("reset_vseq");
   
endfunction : new


function void uvmt_cv32_base_test_c::build_phase(uvm_phase phase);
   
   super.build_phase(phase);
   
   retrieve_clk_gen_vif();
   create_cfg          ();
   randomize_test      ();
   //cfg_hrtbt_monitor   ();
   assign_cfg          ();
   create_cntxt        ();
   assign_cntxt        ();
   create_env          ();
   create_components   ();
   
endfunction : build_phase


function void uvmt_cv32_base_test_c::connect_phase(uvm_phase phase);
   
   super.connect_phase(phase);
   
   //vsequencer = env.vsequencer;
   //uvm_reg_cb::add(null, reg_cbs);
   
endfunction : connect_phase


task uvmt_cv32_base_test_c::run_phase(uvm_phase phase);
   
   super.run_phase(phase);
   
   start_clk();
   watchdog_timer();
   
endtask : run_phase


task uvmt_cv32_base_test_c::reset_phase(uvm_phase phase);
   
   super.reset_phase(phase);
   
   //`uvm_info("TEST", $sformatf("Starting reset virtual sequence:\n%s", reset_vseq.sprint()), UVM_NONE)
   //reset_vseq.start(vsequencer);
   
   phase.raise_objection(this);
   @(posedge clk_gen_vif.core_clock);
   @(posedge clk_gen_vif.core_reset_n);
   repeat (2) @(posedge clk_gen_vif.core_clock);
   phase.drop_objection(this);

   `uvm_info("TEST", "Finished reset virtual sequence", UVM_NONE)
   
endtask : reset_phase


task uvmt_cv32_base_test_c::configure_phase(uvm_phase phase);
   
   uvm_status_e status;
   
   super.configure_phase(phase);
   
   //`uvm_info("TEST", $sformatf("Starting to update DUT with RAL contents:\n%s", ral.sprint()), UVM_NONE)
   //ral.update(status);
   `uvm_info("TEST", "Finished updating DUT with RAL contents", UVM_NONE)
   
endtask : configure_phase


function void uvmt_cv32_base_test_c::phase_started(uvm_phase phase);
   
   string  phase_name = phase.get_name();
   
   super.phase_started(phase);
   
   print_banner($sformatf("start of %s phase", phase_name));
   
endfunction : phase_started


function void uvmt_cv32_base_test_c::phase_ended(uvm_phase phase);
   
   super.phase_ended(phase);
   
   if (phase.is(uvm_final_phase::get())) begin
     uvm_config_db#(bit)::set(null, "", "sim_finished", 1);
     print_banner("test finished");
   end
   
endfunction : phase_ended


function void uvmt_cv32_base_test_c::retrieve_clk_gen_vif();
   
   if (!uvm_config_db#(virtual uvmt_cv32_clk_gen_if)::get(this, "", "clk_gen_vif", clk_gen_vif)) begin
      `uvm_fatal("VIF", $sformatf("Could not find clk_gen_vif handle of type %s in uvm_config_db", $typename(clk_gen_vif)))
   end
   else begin
      `uvm_info("VIF", $sformatf("Found clk_gen_vif handle of type %s in uvm_config_db", $typename(clk_gen_vif)), UVM_DEBUG)
   end
   
endfunction : retrieve_clk_gen_vif


function void uvmt_cv32_base_test_c::create_cfg();
   
   test_cfg = uvmt_cv32_test_cfg_c::type_id::create("test_cfg");
   //test_cfg = new("test_cfg"); // Datum TODO: why doesn't type_id::create() work?
   env_cfg  = uvme_cv32_cfg_c     ::type_id::create("env_cfg" );
   //ral      = env_cfg.ral;
   
endfunction : create_cfg


function void uvmt_cv32_base_test_c::randomize_test();
   
   test_cfg.process_cli_args();
   if (!this.randomize()) begin
      `uvm_fatal("TEST", "Failed to randomize test");
   end
   `uvm_info("TEST", $sformatf("Top-level environment configuration:\n%s", env_cfg.sprint()), UVM_NONE)
   
endfunction : randomize_test


function void uvmt_cv32_base_test_c::cfg_hrtbt_monitor();
   
   //`uvml_hrtbt_set_cfg(startup_timeout , 10_000)
   //`uvml_hrtbt_set_cfg(heartbeat_period, heartbeat_period)
   
endfunction : cfg_hrtbt_monitor


function void uvmt_cv32_base_test_c::assign_cfg();
   
   uvm_config_db#(uvme_cv32_cfg_c)::set(this, "env", "cfg", env_cfg);
   
endfunction : assign_cfg


function void uvmt_cv32_base_test_c::create_cntxt();
   
   env_cntxt = uvme_cv32_cntxt_c::type_id::create("env_cntxt");
   
endfunction : create_cntxt


function void uvmt_cv32_base_test_c::assign_cntxt();
   
   uvm_config_db#(uvme_cv32_cntxt_c)::set(this, "env", "cntxt", env_cntxt);
   
endfunction : assign_cntxt


function void uvmt_cv32_base_test_c::create_env();
   
   env = uvme_cv32_env_c::type_id::create("env", this);
   
endfunction : create_env


function void uvmt_cv32_base_test_c::create_components();
   
   //reg_cbs = uvml_logs_reg_logger_cbs_c::type_id::create("reg_cbs");
   
endfunction : create_components


function void uvmt_cv32_base_test_c::print_banner(string text);
   
   $display("");
   $display("*******************************************************************************");
   $display(text.toupper());
   $display("*******************************************************************************");
   
endfunction : print_banner


task uvmt_cv32_base_test_c::start_clk();
   
   //clk_gen_vif.set_clk_period(
   //   env_cfg.reset_clk_period,
   //   env_cfg.debug_clk_period
   //);
   
   clk_gen_vif.start();
   
endtask : start_clk


task uvmt_cv32_base_test_c::watchdog_timer();
   
   fork
      begin
         #(watchdog_timeout * 1ns);
         //`uvm_fatal("TIMEOUT", $sformatf("Global timeout after %0dns. Heartbeat list:\n%s", watchdog_timeout, uvml_default_hrtbt.print_comp_names()))
         `uvm_fatal("TIMEOUT", $sformatf("Global timeout after %0dns.\n", watchdog_timeout))
      end
   join_none
   
endtask : watchdog_timer


`endif // __UVMT_CV32_BASE_TEST_SV__

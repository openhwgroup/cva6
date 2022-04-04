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



`ifndef __UVMT_CV32E40X_BASE_TEST_SV__
`define __UVMT_CV32E40X_BASE_TEST_SV__


/**
 * Abstract component from which all other CV32E40X test cases must
 * ultimately extend.
 * Subclasses must provide stimulus via the virtual sequencer by implementing
 * UVM runtime phases.
 */
class uvmt_cv32e40x_base_test_c extends uvm_test;

   // Objects
   rand uvmt_cv32e40x_test_cfg_c   test_cfg ;
   rand uvme_cv32e40x_cfg_c        env_cfg  ;
   rand uvme_cv32e40x_cntxt_c      env_cntxt;
   uvml_logs_rs_text_c             rs       ;
   uvml_logs_reg_logger_cbs_c      reg_cbs  ;

   // Components
   uvme_cv32e40x_env_c   env       ;
   uvme_cv32e40x_vsqr_c  vsequencer;

   // Handles testbench interfaces
   virtual uvmt_cv32e40x_vp_status_if    vp_status_vif;  // virtual peripheral status

   // Default sequences
   rand uvme_cv32e40x_reset_vseq_c  reset_vseq;


   `uvm_component_utils_begin(uvmt_cv32e40x_base_test_c)
      `uvm_field_object(test_cfg , UVM_DEFAULT)
      `uvm_field_object(env_cfg  , UVM_DEFAULT)
      `uvm_field_object(env_cntxt, UVM_DEFAULT)
   `uvm_component_utils_end


   constraint env_cfg_cons {
      env_cfg.enabled               == 1;
      env_cfg.is_active             == UVM_ACTIVE;
      env_cfg.trn_log_enabled       == 1;
   }

   constraint heartbreat_mon_default_cons {
      soft test_cfg.heartbeat_mon_enabled == 1;
   }

   constraint test_type_default_cons {
      soft test_cfg.tpt == NO_TEST_PROGRAM;
   }

   // Additional, temporary constraints to get around known design bugs/constraints
   `include "uvmt_cv32e40x_base_test_workarounds.sv"


   /**
    * 1. Replaces default report server with rs.
    * 2. Creates reset_vseq.
    */
   extern function new(string name="uvmt_cv32e40x_base_test", uvm_component parent=null);

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
    * Print final test configuration
    */
   extern virtual function void end_of_elaboration_phase(uvm_phase phase);

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
    * In a typical UVM env, this task writes contents of RAL to the DUT.
    * Here, test_cfg is used to determine if the test program is loaded into
    * the TB's instruction memory.
    */
   extern virtual task configure_phase(uvm_phase phase);

   /**
    * Prints out start of phase banners.
    */
   extern virtual function void phase_started(uvm_phase phase);

   /**
    * Indicates to the test bench (uvmt_cv32e40x_tb) that the test has completed.
    * This is done by checking the properties of the phase argument.
    */
   extern virtual function void phase_ended(uvm_phase phase);

   /**
    * post_randomize hook to complete configuration of test/environment config object
    */
   extern function void post_randomize();

   /**
    * Retrieves virtual interfaces from UVM configuration database.
    */
   extern function void retrieve_vifs();

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
    * Sample the core (DUT) parameters
    */
   extern virtual function void sample_core_parameters();

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
    * Fatals out after watchdog_timeout has elapsed.
    */
   extern virtual task watchdog_timer();

endclass : uvmt_cv32e40x_base_test_c


function uvmt_cv32e40x_base_test_c::new(string name="uvmt_cv32e40x_base_test", uvm_component parent=null);

   super.new(name, parent);

   // Replaces default report server
   // Gives you short-and-sweet looger messages like this:
   //        UVM_INFO @ 9.750 ns : uvmt_cv32e40x_dut_wrap.sv(79) reporter [DUT_WRAP] load_instr_mem asserted!
   rs = new("rs");


   // Terminate simulation after a "reasonable" number of errors
   uvm_report_server::set_server(rs);
   reset_vseq = uvme_cv32e40x_reset_vseq_c::type_id::create("reset_vseq");
endfunction : new


function void uvmt_cv32e40x_base_test_c::build_phase(uvm_phase phase);

   super.build_phase(phase);

   rs.set_max_quit_count(.count(5), .overridable(1));

   create_cfg       ();
   cfg_hrtbt_monitor();
   assign_cfg       ();
   create_cntxt     ();
   assign_cntxt     ();
   retrieve_vifs    ();
   sample_core_parameters();
   randomize_test   ();
   create_env       ();
   create_components();

endfunction : build_phase


function void uvmt_cv32e40x_base_test_c::connect_phase(uvm_phase phase);

   super.connect_phase(phase);

   vsequencer = env.vsequencer;
   uvm_reg_cb::add(null, reg_cbs);

endfunction : connect_phase

function void uvmt_cv32e40x_base_test_c::end_of_elaboration_phase(uvm_phase phase);

   super.end_of_elaboration_phase(phase);

   `uvm_info("BASE TEST", $sformatf("Top-level environment configuration:\n%s", env_cfg.sprint()), UVM_NONE)
   `uvm_info("BASE TEST", $sformatf("Testcase configuration:\n%s", test_cfg.sprint()), UVM_NONE)

endfunction : end_of_elaboration_phase


task uvmt_cv32e40x_base_test_c::run_phase(uvm_phase phase);

   super.run_phase(phase);

   watchdog_timer();

endtask : run_phase


task uvmt_cv32e40x_base_test_c::reset_phase(uvm_phase phase);

   super.reset_phase(phase);

   phase.raise_objection(this);

   env_cntxt.core_cntrl_cntxt.core_cntrl_vif.load_instr_mem = 1'bX; // Using 'X to signal uvmt_cv32e40x_dut_wrap.sv to wait...

   `uvm_info("BASE TEST", $sformatf("Starting reset virtual sequence:\n%s", reset_vseq.sprint()), UVM_NONE)
   reset_vseq.start(vsequencer);
   `uvm_info("BASE TEST", $sformatf("Finished reset virtual sequence:\n%s", reset_vseq.sprint()), UVM_NONE)

   phase.drop_objection(this);

endtask : reset_phase


task uvmt_cv32e40x_base_test_c::configure_phase(uvm_phase phase);

   // Control the loading of the pre-compiled firmware
   // Actual loading done in uvmt_cv32e40x_dut_wrap.sv to avoid XMRs across packages.
   if (test_cfg.tpt == NO_TEST_PROGRAM) begin
     env_cntxt.core_cntrl_cntxt.core_cntrl_vif.load_instr_mem = 1'b0;
     `uvm_info("BASE TEST", "clear load_instr_mem", UVM_NONE)
   end
   else begin
     env_cntxt.core_cntrl_cntxt.core_cntrl_vif.load_instr_mem = 1'b1;
     `uvm_info("BASE TEST", "set load_instr_mem", UVM_NONE)
   end

   //TODO: is this OK?!?
   super.configure_phase(phase);
   `uvm_info("BASE TEST", "configure_phase() complete", UVM_HIGH)

endtask : configure_phase


function void uvmt_cv32e40x_base_test_c::phase_started(uvm_phase phase);

   string  phase_name = phase.get_name();

   super.phase_started(phase);

   print_banner($sformatf("start of %s phase", phase_name));

endfunction : phase_started


function void uvmt_cv32e40x_base_test_c::phase_ended(uvm_phase phase);

   // Local vars for test status outputs from Virtual Peripheral in uvmt_cv32e40x_tb.dut_wrap.mem_i
   bit        tp;
   bit        tf;
   bit        evalid;
   bit [31:0] evalue;

   super.phase_ended(phase);

   if (phase.is(uvm_final_phase::get())) begin
     // Set sim_finished (otherwise tb will flag that sim was aborted)
     uvm_config_db#(bit)::set(null, "", "sim_finished", 1);

     //
     // Get test status outputs
     if(!(uvm_config_db#(bit      )::get(null, "*", "tp",     tp    ))) `uvm_error("END_OF_TEST", "Cannot get tp from config_db.")
     if(!(uvm_config_db#(bit      )::get(null, "*", "tf",     tf    ))) `uvm_error("END_OF_TEST", "Cannot get tf from config_db.")
     if(!(uvm_config_db#(bit      )::get(null, "*", "evalid", evalid))) `uvm_error("END_OF_TEST", "Cannot get valid from config_db.")
     if(!(uvm_config_db#(bit[31:0])::get(null, "*", "evalue", evalue))) `uvm_error("END_OF_TEST", "Cannot get evalue from config_db.")

     // Use the DUT Wrapper Virtual Peripheral's status outputs to update report server status.
     if (tf)  `uvm_error  ("END_OF_TEST", "DUT WRAPPER virtual peripheral flagged test failure.")

     // Check exit code if a valid exit code was written to Virtual Peripheral
     if (evalid) begin
       if (evalue != 0) begin
          `uvm_error("END_OF_TEST", $sformatf("DUT WRAPPER virtual peripheral signaled exit_value=%0h.", evalue))
       end
       else begin
         `uvm_info("END_OF_TEST", $sformatf("DUT WRAPPER virtual peripheral signaled exit_value=%0h.", evalue), UVM_NONE)
       end
     end

     // Catch hanging tests.  If no exit code nor test pass/test fail status was ever written to Virtual Peripheral
     // then mark test as failed
     if (!tp && !evalid && !tf) `uvm_error("END_OF_TEST", "DUT WRAPPER virtual peripheral failed to flag test passed and failed to signal exit value.")

     print_banner("test finished");
   end

endfunction : phase_ended

function void uvmt_cv32e40x_base_test_c::post_randomize();


endfunction : post_randomize


function void uvmt_cv32e40x_base_test_c::retrieve_vifs();

   if (!uvm_config_db#(virtual uvmt_cv32e40x_vp_status_if)::get(this, "", "vp_status_vif", vp_status_vif)) begin
      `uvm_fatal("VIF", $sformatf("Could not find vp_status_vif handle of type %s in uvm_config_db", $typename(vp_status_vif)))
   end
   else begin
      `uvm_info("VIF", $sformatf("Found vp_status_vif handle of type %s in uvm_config_db", $typename(vp_status_vif)), UVM_DEBUG)
   end

   if (!uvm_config_db#(virtual uvme_cv32e40x_core_cntrl_if)::get(this, "", "core_cntrl_vif", env_cntxt.core_cntrl_cntxt.core_cntrl_vif)) begin
      `uvm_fatal("VIF", $sformatf("Could not find core_cntrl_vif handle of type %s in uvm_config_db", $typename(env_cntxt.core_cntrl_cntxt.core_cntrl_vif)))
   end
   else begin
      `uvm_info("VIF", $sformatf("Found core_cntrl_vif handle of type %s in uvm_config_db", $typename(env_cntxt.core_cntrl_cntxt.core_cntrl_vif)), UVM_DEBUG)
   end

endfunction : retrieve_vifs


function void uvmt_cv32e40x_base_test_c::create_cfg();

   test_cfg = uvmt_cv32e40x_test_cfg_c::type_id::create("test_cfg");
   env_cfg  = uvme_cv32e40x_cfg_c     ::type_id::create("env_cfg" );

endfunction : create_cfg


function void uvmt_cv32e40x_base_test_c::randomize_test();

   test_cfg.process_cli_args();
   `uvm_info("TEST", "randomize test", UVM_LOW);
   if (!this.randomize()) begin
      `uvm_fatal("BASE TEST", "Failed to randomize test");
   end

endfunction : randomize_test


function void uvmt_cv32e40x_base_test_c::cfg_hrtbt_monitor();

   uvml_default_hrtbt.enabled = test_cfg.heartbeat_mon_enabled;
   //`uvml_hrtbt_set_cfg(startup_timeout , test_cfg.startup_timeout)
   uvml_default_hrtbt.startup_timeout = test_cfg.startup_timeout; // TODO DOP: Fix heartbeat macros
   //`uvml_hrtbt_set_cfg(heartbeat_period, test_cfg.heartbeat_period)
   uvml_default_hrtbt.startup_timeout = test_cfg.heartbeat_period; // TODO DOP: Fix heartbeat macros

endfunction : cfg_hrtbt_monitor


function void uvmt_cv32e40x_base_test_c::assign_cfg();

   uvm_config_db#(uvme_cv32e40x_cfg_c)::set(this, "env", "cfg", env_cfg);

endfunction : assign_cfg


function void uvmt_cv32e40x_base_test_c::create_cntxt();

   env_cntxt = uvme_cv32e40x_cntxt_c::type_id::create("env_cntxt");

endfunction : create_cntxt


function void uvmt_cv32e40x_base_test_c::assign_cntxt();

   uvm_config_db#(uvme_cv32e40x_cntxt_c)::set(this, "env", "cntxt", env_cntxt);

endfunction : assign_cntxt


function void uvmt_cv32e40x_base_test_c::sample_core_parameters();

   env_cfg.sample_parameters(env_cntxt.core_cntrl_cntxt);

endfunction : sample_core_parameters


function void uvmt_cv32e40x_base_test_c::create_env();

   env = uvme_cv32e40x_env_c::type_id::create("env", this);

endfunction : create_env


function void uvmt_cv32e40x_base_test_c::create_components();

   reg_cbs = uvml_logs_reg_logger_cbs_c::type_id::create("reg_cbs");

endfunction : create_components


function void uvmt_cv32e40x_base_test_c::print_banner(string text);

  if (test_cfg != null) begin
    if (test_cfg.print_uvm_runflow_banner) begin
      $display("");
      $display("*******************************************************************************");
      $display(text.toupper());
      $display("*******************************************************************************");
    end
    else begin
      `uvm_info("BASE_TEST", "Printing of UVM run-flow banner disabled", UVM_HIGH)
    end
  end

endfunction : print_banner


task uvmt_cv32e40x_base_test_c::watchdog_timer();

   fork
      begin
         #(test_cfg.watchdog_timeout * 1ns);
         `uvm_fatal("TIMEOUT", $sformatf("Global timeout after %0dns. Heartbeat list:\n%s", test_cfg.watchdog_timeout, uvml_default_hrtbt.print_comp_names()))
      end
   join_none

endtask : watchdog_timer


`endif // __UVMT_CV32E40X_BASE_TEST_SV__

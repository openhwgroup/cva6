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

// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1


`ifndef __UVMT_CV32E40P_BASE_TEST_SV__
`define __UVMT_CV32E40P_BASE_TEST_SV__


/**
 * Abstract component from which all other CV32E40P test cases must
 * ultimately extend.
 * Subclasses must provide stimulus via the virtual sequencer by implementing
 * UVM runtime phases.
 */
class uvmt_cv32e40p_base_test_c extends uvm_test;

   // Objects
   rand uvmt_cv32e40p_test_cfg_c      test_cfg      ;
   rand uvmt_cv32e40p_test_randvars_c test_randvars ;
   rand uvme_cv32e40p_cfg_c           env_cfg       ;
   rand uvme_cv32e40p_cntxt_c         env_cntxt     ;
   uvml_logs_rs_text_c                rs            ;
   uvml_logs_reg_logger_cbs_c         reg_cbs       ;

   // Components
   uvme_cv32e40p_env_c   env       ;
   uvme_cv32e40p_vsqr_c  vsequencer;

   // Handles testbench interfaces
   virtual uvmt_cv32e40p_vp_status_if    vp_status_vif;  // virtual peripheral status
   virtual uvmt_cv32e40p_core_cntrl_if   core_cntrl_vif; // control inputs to the core
   virtual uvmt_cv32e40p_step_compare_if step_compare_vif;

   // Default sequences
   rand uvme_cv32e40p_reset_vseq_c  reset_vseq;


   `uvm_component_utils_begin(uvmt_cv32e40p_base_test_c)
      `uvm_field_object(test_cfg      , UVM_DEFAULT)
      `uvm_field_object(test_randvars , UVM_DEFAULT)
      `uvm_field_object(env_cfg       , UVM_DEFAULT)
      `uvm_field_object(env_cntxt     , UVM_DEFAULT)
   `uvm_component_utils_end


   constraint env_cfg_cons {
      env_cfg.enabled         == 1;
      env_cfg.is_active       == UVM_ACTIVE;
      env_cfg.trn_log_enabled == 1;
   }

   constraint test_type_default_cons {
     soft test_cfg.tpt == NO_TEST_PROGRAM;
   }


   // Additional, temporary constraints to get around known design bugs/constraints
   `include "uvmt_cv32e40p_base_test_workarounds.sv"


   /**
    * 1. Replaces default report server with rs.
    * 2. Creates reset_vseq.
    */
   extern function new(string name="uvmt_cv32e40p_base_test", uvm_component parent=null);

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
    * Indicates to the test bench (uvmt_cv32e40p_tb) that the test has completed.
    * This is done by checking the properties of the phase argument.
    */
   extern virtual function void phase_ended(uvm_phase phase);

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
    * Creates env.
    */
   extern virtual function void create_env();

   /**
    * Creates additional (non-environment) components (and objects).
    */
   extern virtual function void create_components();

   /**
    * Prints overlined and underlined text in uppercase.
    * Waiving Verissimo SVTB.32.2.0: Pass strings by reference unless otherwise needed
    */
   extern function void print_banner(string text); //@DVT_LINTER_WAIVER "MT20211228_3" disable SVTB.32.2.0

   /**
    * Fatals out after watchdog_timeout has elapsed.
    */
   extern virtual task watchdog_timer();

endclass : uvmt_cv32e40p_base_test_c


function uvmt_cv32e40p_base_test_c::new(string name="uvmt_cv32e40p_base_test", uvm_component parent=null);

   super.new(name, parent);

   // Replaces default report server
   // Gives you short-and-sweet looger messages like this:
   //        UVM_INFO @ 9.750 ns : uvmt_cv32e40p_dut_wrap.sv(79) reporter [DUT_WRAP] load_instr_mem asserted!
   rs = new("rs");


   // Terminate simulation after a "reasonable" number of errors
   uvm_report_server::set_server(rs);
   reset_vseq = uvme_cv32e40p_reset_vseq_c::type_id::create("reset_vseq", vsequencer);
endfunction : new


function void uvmt_cv32e40p_base_test_c::build_phase(uvm_phase phase);

   super.build_phase(phase);

   rs.set_max_quit_count(.count(5), .overridable(1));

   retrieve_vifs    ();
   create_cfg       ();
   randomize_test   ();
   cfg_hrtbt_monitor();
   assign_cfg       ();
   create_cntxt     ();
   assign_cntxt     ();
   create_env       ();
   create_components();

endfunction : build_phase


function void uvmt_cv32e40p_base_test_c::connect_phase(uvm_phase phase);

   super.connect_phase(phase);

   vsequencer = env.vsequencer;
   uvm_reg_cb::add(null, reg_cbs);

endfunction : connect_phase


task uvmt_cv32e40p_base_test_c::run_phase(uvm_phase phase);


   super.run_phase(phase);

   watchdog_timer();

endtask : run_phase


task uvmt_cv32e40p_base_test_c::reset_phase(uvm_phase phase);

   super.reset_phase(phase);

   phase.raise_objection(this);

   core_cntrl_vif.load_instr_mem = 1'bX; // Using 'X to signal uvmt_cv32e40p_dut_wrap.sv to wait...

   `uvm_info("BASE TEST", $sformatf("Starting reset virtual sequence:\n%s", reset_vseq.sprint()), UVM_NONE)
   reset_vseq.start(vsequencer);
   `uvm_info("BASE TEST", $sformatf("Finished reset virtual sequence:\n%s", reset_vseq.sprint()), UVM_NONE)

   phase.drop_objection(this);

endtask : reset_phase


task uvmt_cv32e40p_base_test_c::configure_phase(uvm_phase phase);

   uvm_status_e status;

   //super.configure_phase(phase);

   //`uvm_info("BASE TEST", $sformatf("Starting to update DUT with RAL contents:\n%s", ral.sprint()), UVM_NONE)
   //ral.update(status);
   //`uvm_info("BASE TEST", "Finished updating DUT with RAL contents", UVM_NONE)

   // Control the loading of the pre-compiled firmware
   // Actual loading done in uvmt_cv32e40p_dut_wrap.sv to avoid XMRs across packages.
   if (test_cfg.tpt == NO_TEST_PROGRAM) begin
     core_cntrl_vif.load_instr_mem = 1'b0;
     `uvm_info("BASE TEST", "clear load_instr_mem", UVM_NONE)
   end
   else begin
     core_cntrl_vif.load_instr_mem = 1'b1;
     `uvm_info("BASE TEST", "set load_instr_mem", UVM_NONE)
   end

   //TODO: is this OK?!?
   super.configure_phase(phase);
   `uvm_info("BASE TEST", "configure_phase() complete", UVM_HIGH)

endtask : configure_phase


function void uvmt_cv32e40p_base_test_c::phase_started(uvm_phase phase);

   string  phase_name = phase.get_name();

   super.phase_started(phase);

   print_banner($sformatf("start of %s phase", phase_name));

endfunction : phase_started


function void uvmt_cv32e40p_base_test_c::phase_ended(uvm_phase phase);

   // Local vars for test status outputs from Virtual Peripheral in uvmt_cv32e40p_tb.dut_wrap.mem_i
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

     // Report on number of ISS step and compare checks if the ISS is used
     if ($test$plusargs("USE_ISS")) begin
       step_compare_vif.report_step_compare();
     end

     print_banner("test finished");
   end

endfunction : phase_ended


function void uvmt_cv32e40p_base_test_c::retrieve_vifs();

   if (!uvm_config_db#(virtual uvmt_cv32e40p_vp_status_if)::get(this, "", "vp_status_vif", vp_status_vif)) begin
      `uvm_fatal("VIF", $sformatf("Could not find vp_status_vif handle of type %s in uvm_config_db", $typename(vp_status_vif)))
   end
   else begin
      `uvm_info("VIF", $sformatf("Found vp_status_vif handle of type %s in uvm_config_db", $typename(vp_status_vif)), UVM_DEBUG)
   end

   if (!uvm_config_db#(virtual uvmt_cv32e40p_core_cntrl_if)::get(this, "", "core_cntrl_vif", core_cntrl_vif)) begin
      `uvm_fatal("VIF", $sformatf("Could not find core_cntrl_vif handle of type %s in uvm_config_db", $typename(core_cntrl_vif)))
   end
   else begin
      `uvm_info("VIF", $sformatf("Found core_cntrl_vif handle of type %s in uvm_config_db", $typename(core_cntrl_vif)), UVM_DEBUG)
   end

   if (!uvm_config_db#(virtual uvmt_cv32e40p_step_compare_if)::get(this, "", "step_compare_vif", step_compare_vif)) begin
      `uvm_fatal("VIF", $sformatf("Could not find step_compare_vif handle of type %s in uvm_config_db", $typename(step_compare_vif)))
   end
   else begin
      `uvm_info("VIF", $sformatf("Found step_compare_vif handle of type %s in uvm_config_db", $typename(step_compare_vif)), UVM_DEBUG)
   end

endfunction : retrieve_vifs


function void uvmt_cv32e40p_base_test_c::create_cfg();

   test_cfg = uvmt_cv32e40p_test_cfg_c::type_id::create("test_cfg");
   env_cfg  = uvme_cv32e40p_cfg_c     ::type_id::create("env_cfg" );
   //ral      = env_cfg.ral;

endfunction : create_cfg


function void uvmt_cv32e40p_base_test_c::randomize_test();

   test_cfg.process_cli_args();
   if (!this.randomize()) begin
      `uvm_fatal("BASE TEST", "Failed to randomize test");
   end
   `uvm_info("BASE TEST", $sformatf("Testcase configuration:\n%s", test_cfg.sprint()), UVM_NONE)

endfunction : randomize_test


function void uvmt_cv32e40p_base_test_c::cfg_hrtbt_monitor();

   uvml_default_hrtbt.enabled = 0;
   //`uvml_hrtbt_set_cfg(startup_timeout , test_cfg.startup_timeout)
   uvml_default_hrtbt.startup_timeout = test_cfg.startup_timeout; // TODO DOP: Fix heartbeat macros
   //`uvml_hrtbt_set_cfg(heartbeat_period, test_cfg.heartbeat_period)
   uvml_default_hrtbt.startup_timeout = test_cfg.heartbeat_period; // TODO DOP: Fix heartbeat macros

endfunction : cfg_hrtbt_monitor


function void uvmt_cv32e40p_base_test_c::assign_cfg();

   uvm_config_db#(uvme_cv32e40p_cfg_c)::set(this, "env", "cfg", env_cfg);

endfunction : assign_cfg


function void uvmt_cv32e40p_base_test_c::create_cntxt();

   env_cntxt = uvme_cv32e40p_cntxt_c::type_id::create("env_cntxt");

endfunction : create_cntxt


function void uvmt_cv32e40p_base_test_c::assign_cntxt();

   uvm_config_db#(uvme_cv32e40p_cntxt_c)::set(this, "env", "cntxt", env_cntxt);
   env_cntxt.vp_status_vif = this.vp_status_vif;

endfunction : assign_cntxt


function void uvmt_cv32e40p_base_test_c::create_env();

   env = uvme_cv32e40p_env_c::type_id::create("env", this);

endfunction : create_env


function void uvmt_cv32e40p_base_test_c::create_components();

   reg_cbs = uvml_logs_reg_logger_cbs_c::type_id::create("reg_cbs");

endfunction : create_components


function void uvmt_cv32e40p_base_test_c::print_banner(string text);

  if (test_cfg != null) begin
    if (test_cfg.print_uvm_runflow_banner) begin
      // In most other contexts, calls to $display() in a UVM environment are
      // illegal. Here they are OK because the following is a banner header
      // with no fatal/error/warning or uvm_info implications.
      //@DVT_LINTER_WAIVER_START "MT20210909_1" disable SVTB.29.1.7
      $display("");
      $display("*******************************************************************************");
      $display(text.toupper());
      $display("*******************************************************************************");
      //@DVT_LINTER_WAIVER_END "MT20210909_1"
    end
    else begin
      `uvm_info("BASE_TEST", "Printing of UVM run-flow banner disabled", UVM_HIGH)
    end
  end

endfunction : print_banner


task uvmt_cv32e40p_base_test_c::watchdog_timer();

   fork
      begin
         #(test_cfg.watchdog_timeout * 1ns);
         `uvm_fatal("TIMEOUT", $sformatf("Global timeout after %0dns. Heartbeat list:\n%s", test_cfg.watchdog_timeout, uvml_default_hrtbt.print_comp_names()))
      end
   join_none

endtask : watchdog_timer


`endif // __UVMT_CV32E40P_BASE_TEST_SV__

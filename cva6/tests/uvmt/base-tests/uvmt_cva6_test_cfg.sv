// Copyright 2020 OpenHW Group
// Copyright 2020 Datum Technology Corporation
// Copyright 2021 Thales DIS Design Services SAS
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
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0


`ifndef __UVMT_CVA6_TEST_CFG_SV__
`define __UVMT_CVA6_TEST_CFG_SV__


/**
 * Configuration object for testcases
 */
class uvmt_cva6_test_cfg_c extends uvm_object;

   //typedef enum {
   //              PREEXISTING_SELFCHECKING,
   //              PREEXISTING_NOTSELFCHECKING,
   //              GENERATED_SELFCHECKING,
   //              GENERATED_NOTSELFCHECKING,
   //              NONE
   //             } test_program_type;


   // Knobs for environment control
   rand int unsigned  startup_timeout ; // Specified in nanoseconds (ns)
   rand int unsigned  heartbeat_period; // Specified in nanoseconds (ns)
   rand int unsigned  watchdog_timeout; // Specified in nanoseconds (ns)

   // Knobs for test-program control
   rand test_program_type tpt;

   // Command line arguments for controlling RAL
   // (note: its not clear if this ENV will use the RAL)
   string cli_block_name_str      = "BLKNM";
   bit    cli_block_name_override = 0;
   //uvm_reg_block  cli_selected_block;

   // Command line arguments for FIRMWARE (Test Program) selection
   // +firmware=<path_to_hexfile_test_program>
   string cli_firmware_select_str      = "firmware";
   bit    cli_firmware_select_override = 0;
   string cli_firmware_name_str        = "";

   // Command line arguments to control whether the UVM run-flow banner is
   // written to stdout. (A bit overkill for on/off control.)
   // +print_uvm_runflow_banner=1
   string cli_uvm_banner_select_str      = "print_uvm_runflow_banner";
   bit    cli_uvm_banner_select_override = 0;
   string cli_uvm_banner_name_str        = "";

   // Run-time control
   bit    run_riscv_gcc_toolchain  = 0;
   bit    print_uvm_runflow_banner = 0;

   `uvm_object_utils_begin(uvmt_cva6_test_cfg_c)
      `uvm_field_int(heartbeat_period, UVM_DEFAULT)
      `uvm_field_int(watchdog_timeout, UVM_DEFAULT)

      `uvm_field_enum(test_program_type, tpt, UVM_DEFAULT)

      //`uvm_field_object(cli_selected_block, UVM_DEFAULT)
      `uvm_field_int(run_riscv_gcc_toolchain, UVM_DEFAULT)
      `uvm_field_int(print_uvm_runflow_banner, UVM_DEFAULT)
   `uvm_object_utils_end


   constraint timeouts_default_cons {
      soft startup_timeout  == 100_000_000; // Set to be huge for now so that sim can finish
      soft heartbeat_period ==    200_000; //  2 us // TODO Set default Heartbeat Monitor period for uvmt_cva6_base_test_c
      soft watchdog_timeout == 100_000_000; // 10 ms // TODO Set default Watchdog timeout period for uvmt_cva6_base_test_c
   }

   //constraint test_type_default_cons {
   //  soft tpt == NONE;
   //}

   /**
    * Default constructor.
    */
   extern function new(string name="uvmt_cva6_test_cfg");

   /**
    * TODO Describe uvmt_cva6_test_cfg_c::process_cli_args()
    */
   extern function void process_cli_args();

endclass : uvmt_cva6_test_cfg_c


function uvmt_cva6_test_cfg_c::new(string name="uvmt_cva6_test_cfg");

   super.new(name);

endfunction : new


function void uvmt_cva6_test_cfg_c::process_cli_args();

   string  cli_block_name_parsed_str           = "";

   // RAL control
   cli_block_name_override = 0; //default
   if (uvm_cmdline_proc.get_arg_value({"+", cli_block_name_str, "="}, cli_block_name_parsed_str)) begin
      if (cli_block_name_parsed_str != "") begin
         cli_block_name_override = 1;
         //cli_selected_block = ral.get_block_by_name(cli_block_name_parsed_str);
         `uvm_info("TEST_CFG", $sformatf("process_cli_args() RAL block_name=%s", cli_block_name_str), UVM_LOW)
      end
   end

   // Test program (firmware) selection
   cli_firmware_select_override = 0; // default
   if (uvm_cmdline_proc.get_arg_value({"+", cli_firmware_select_str, "="}, cli_firmware_name_str)) begin
      if (cli_firmware_name_str != "") begin
         cli_firmware_select_override = 1;
         run_riscv_gcc_toolchain      = 1;
         `uvm_info("TEST_CFG", $sformatf("process_cli_args() firmware=%s", cli_firmware_name_str), UVM_LOW)
      end
   end

   // Turn on printing of UVM run-flow banner (any arg will work)
   // void'($value$plusargs("print_uvm_runflow_banner=%0d", print_uvm_runflow_banner));
   cli_uvm_banner_select_override = 0; // default
   if (uvm_cmdline_proc.get_arg_value({"+", cli_uvm_banner_select_str, "="}, cli_uvm_banner_name_str)) begin
      if (cli_firmware_name_str != "") begin
         cli_uvm_banner_select_override = 1;
         print_uvm_runflow_banner       = 1;
         `uvm_info("TEST_CFG", $sformatf("process_cli_args() cli_uvm_banner_select_str=%s", cli_uvm_banner_name_str), UVM_LOW)
      end
   end

   `uvm_info("TEST_CFG", "process_cli_args() complete", UVM_HIGH)

endfunction : process_cli_args


`endif // __UVMT_CVA6_TEST_CFG_SV__

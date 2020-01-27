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


`ifndef __UVMT_CV32_TB_SV__
`define __UVMT_CV32_TB_SV__


/**
 * Module encapsulating the CV32 DUT wrapper, agents and clock
 * generating interfaces. The clock and reset interfaces only feed into the
 * CV32 and DEBUG interfaces as their
 * clocks and resets, respectively.
 */
module uvmt_cv32_tb;
   
   import uvm_pkg::*;
   import uvmt_cv32_pkg::*;
   
   // temporary I/Os for the dut_wrap()
   logic        clk;
   logic        rst_n;
   logic        fetch_enable;
   logic        tests_passed;
   logic        tests_failed;
   logic [31:0] exit_value;
   logic        exit_valid;

   // Clocking & Reset
   uvmt_cv32_clk_gen_if  clk_gen_if();
//   uvma_reset_if  reset_if(.clk(clk_gen_if.reset_clk));
   
   // Agent interfaces
//   uvma_debug_if  debug_if(.clk(clk_gen_if.debug_clk), .reset(reset_if.reset));
   
  /**
   * DUT WRAPPER instance:
   * This is the riscv_wrapper.sv from PULP-Platform RI5CY project
   * with a few mods to bring unused ports from the CORE to this level.
   */
   uvmt_cv32_dut_wrap  #(
                         .INSTR_RDATA_WIDTH ( 128),
                         .RAM_ADDR_WIDTH    (  20),
                         .BOOT_ADDR         ('h80),
                         .PULP_SECURE       (   1)
                        )
                        dut_wrap
                        (
                         .clk_i             (clk),
                         .rst_ni            (rst_n),
                         .fetch_enable_i    (fetch_enable),
                         .tests_passed_o    (tests_passed),
                         .tests_failed_o    (tests_failed),
                         .exit_value_o      (exit_value),
                         .exit_valid_o      (exit_valid)
                        );
   
   
   /**
    * Test bench entry point.
    */
   initial begin
      // Specify time format for simulation (units_number, precision_number, suffix_string, minimum_field_width)
      $timeformat(-9, 3, " ns", 8);
      
      // Add interfaces to uvm_config_db
      uvm_config_db#(virtual uvmt_cv32_clk_gen_if)::set(null, "*", "clk_gen_vif", clk_gen_if);
//      uvm_config_db#(virtual uvma_reset_if)::set(null, "*.env.reset_agent", "vif", reset_if);
//      uvm_config_db#(virtual uvma_debug_if)::set(null, "*.env.debug_agent", "vif", debug_if);
      
      // Run test
      uvm_top.enable_print_topology = 1;
      uvm_top.finish_on_completion  = 1;
      uvm_top.run_test();
   end
   
   
   /**
    * End-of-test summary printout.
    */
   final begin
      string             summary_string;
      uvm_report_server  rs;
      int                err_count;
      int                fatal_count;
      static bit         sim_finished = 0;
      
      static string  red   = "\033[31m\033[1m";
      static string  green = "\033[32m\033[1m";
      static string  reset = "\033[0m";
      
      // Use the Virtual Peripheral's status outputs to update report server status.
      if (tests_failed)  `uvm_error("WRAPPER FLAGS", "DUT WRAPPER virtual peripheral flagged test failure.")
      if (!tests_passed) `uvm_error("WRAPPER FLAGS", "DUT WRAPPER virtual peripheral failed to flag test passed.")
      if (!exit_valid) begin
        `uvm_error("WRAPPER FLAGS", "DUT WRAPPER virtual peripheral failed to exit properly.")
      end
      // TODO: handle exit_value properly
      
      rs          = uvm_top.get_report_server();
      err_count   = rs.get_severity_count(UVM_ERROR);
      fatal_count = rs.get_severity_count(UVM_FATAL);
      
      void'(uvm_config_db#(bit)::get(null, "", "sim_finished", sim_finished));

      $display("\n*** Test Summary ***\n");
      
      if (sim_finished && (err_count == 0) && (fatal_count == 0)) begin
         $display("    PPPPPPP    AAAAAA    SSSSSS    SSSSSS   EEEEEEEE  DDDDDDD     ");
         $display("    PP    PP  AA    AA  SS    SS  SS    SS  EE        DD    DD    ");
         $display("    PP    PP  AA    AA  SS        SS        EE        DD    DD    ");
         $display("    PPPPPPP   AAAAAAAA   SSSSSS    SSSSSS   EEEEE     DD    DD    ");
         $display("    PP        AA    AA        SS        SS  EE        DD    DD    ");
         $display("    PP        AA    AA  SS    SS  SS    SS  EE        DD    DD    ");
         $display("    PP        AA    AA   SSSSSS    SSSSSS   EEEEEEEE  DDDDDDD     ");
         $display("    ----------------------------------------------------------");
         $display("                        SIMULATION PASSED                     ");
         $display("    ----------------------------------------------------------");
      end
      else begin
         $display("    FFFFFFFF   AAAAAA   IIIIII  LL        EEEEEEEE  DDDDDDD       ");
         $display("    FF        AA    AA    II    LL        EE        DD    DD      ");
         $display("    FF        AA    AA    II    LL        EE        DD    DD      ");
         $display("    FFFFF     AAAAAAAA    II    LL        EEEEE     DD    DD      ");
         $display("    FF        AA    AA    II    LL        EE        DD    DD      ");
         $display("    FF        AA    AA    II    LL        EE        DD    DD      ");
         $display("    FF        AA    AA  IIIIII  LLLLLLLL  EEEEEEEE  DDDDDDD       ");
         
         if (sim_finished == 0) begin
            $display("    --------------------------------------------------------");
            $display("                   SIMULATION FAILED - ABORTED              ");
            $display("    --------------------------------------------------------");
         end
         else begin
            $display("    --------------------------------------------------------");
            $display("                       SIMULATION FAILED                    ");
            $display("    --------------------------------------------------------");
         end
      end
   end
   
endmodule : uvmt_cv32_tb


`endif // __UVMT_CV32_TB_SV__

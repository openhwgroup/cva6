//
// Copyright 2020 OpenHW Group
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
//


`ifndef __UVMT_CV32_STEP_COMPARE_SV__
`define __UVMT_CV32_STEP_COMPARE_SV__

// Step-and-Compare between the CV32E40P and Imperas OVPsim ISS
// Cloned from the Imperas demo at $(IMPERAS_HOME)/RTL_OVPmodel_step_compare/verilog_testbench/testbench.sv

/*
 * Copyright (c) 2005-2020 Imperas Software Ltd., www.imperas.com
 * Copyright (C) EM Microelectronic US Inc.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *   http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND,
 * either express or implied.
 *
 * See the License for the specific language governing permissions and
 * limitations under the License.
 *
 */

`ifdef COVERAGE
`include "class_coverage.svh" 
`endif

//
// Execute step and compare of dut ISS instance vs riscv RTL instance
//
`ifndef T0_TYPE
  `define T0_TYPE "RV32IMC"
`endif

//import params_pkg::*;
//import compare_pkg::*;
import uvm_pkg::*;      // needed for the UVM messaging service (`uvm_info(), etc.)


//`define RTL
//`define ISS 

module uvmt_cv32_step_compare
  (
   uvma_clknrst_if    clknrst_if,
   uvmt_cv32_step_compare_if step_compare_if
);

   parameter bit                 COMP_CSR=1; // By default compare CSRs
   
   bit  Clk;
   bit  miscompare;

  function void check_32bit(input string compared, input bit [31:0] expected, input logic [31:0] actual);
      static int now = 0;
      if (now != $time) begin
        miscompare = 0;
        now = $time;
      end
      if (expected !== actual) begin
        miscompare = 1;
        `uvm_error("", $sformatf("%s expected=0x%8h and actual=0x%8h PC=0x%8h", compared, expected, actual, step_compare_if.ovp_cpu_PCr));
      end else begin
         `uvm_info("", $sformatf("%s expected=0x%8h==actual", compared, actual), UVM_DEBUG);
      end
   endfunction // check_32bit
   
   
   function automatic void compare();
      int idx;
      logic [31:0][31:0] riscy_GPR; // packed dimensions, register index by data width
      logic [ 5:0] insn_regs_write_addr;
      logic [31:0] insn_regs_write_value;
      int          insn_regs_write_size;
      string       compared_str;

      // Compare PC
      check_32bit(.compared("PC"), .expected(step_compare_if.ovp_cpu_PCr), 
                                   .actual(step_compare_if.insn_pc));

    endfunction // compare

    /*
        The schedule works like this
        1. Run the RTL for 1 instruction retirement
        2. if the RTL.RetiredPC == OVP.NextPC
           then run OVP for 1 instruction retirement
        3. Compare RTL <-> OVP
    */
    bit step_rtl = 0;
    bit step_ovp = 0;
    bit ret_ovp = 0;
    bit ret_rtl = 0;
    event ev_ovp, ev_rtl;
    event ev_compare;

    initial begin
        if (COMP_CSR != 1)
            $display("NOTE! CSRs not compared because COMP_CSR=%0b", COMP_CSR);
      
        step_compare_if.ovp_b1_Step = 0;
        step_compare_if.ovp_b1_Stepping = 1;
        step_ovp = 0;
        step_rtl = 1;
    end
    
    // ovp_core
    always @(step_compare_if.ovp_cpu_retire) begin
        step_ovp = 0;
        ret_ovp  = 1;
        #0 ->ev_ovp;
    end

    // riscv_core
    always @(step_compare_if.riscv_retire) begin
        step_rtl = 0;
        ret_rtl  = 1;
        #0 ->ev_rtl;
    end
    
    always @(posedge ret_rtl) begin
        ret_ovp  = 0;
        step_ovp = 1;
    end

    always @(ev_ovp or ev_rtl) begin
        if (ret_ovp && ret_rtl) begin
            fork
                ->step_compare_if.ovp_cpu_busWait;
                #60ns;
            join_any;
            compare();
            ret_rtl  = 0;
            step_rtl = 1;
            #0 ->ev_compare;
        end
    end

    always @(step_ovp) begin
        step_compare_if.ovp_b1_Step = step_ovp;
    end
    
   // Run riscv_core.Clk if step_rtl=1
   initial begin
      #1; // To get uvmt_cv32_base_test_c::reset_phase to execute
      forever begin
         if (step_rtl) begin
            clknrst_if.start_clk();
            #(clknrst_if.clk_period);
         end
         else begin
            clknrst_if.stop_clk();
            @(ev_compare);
         end
      end
   end
   






`ifdef COVERAGE
   coverage cov1;
   initial begin
       cov1 = new();
   end

    function void split(input string in_s, output string s1, s2);
        automatic int i;
        for (i=0; i<in_s.len(); i++) begin
            if (in_s.getc(i) == ":")
                break;
         end
         if (i==0 ) begin
            `uvm_fatal("STEP COMPARE", $sformatf(": not found in split '%0s'", in_s))
         end
         s1 = in_s.substr(0,i-1);
         s2 = in_s.substr(i+1,in_s.len()-1);
    endfunction


    function automatic void sample();
        string decode = iss_wrap.cpu.Decode;
        string ins_str, op[4], key, val;
        int i;
        ins_t ins;
        int num = $sscanf (decode, "%s %s %s %s %s", ins_str, op[0], op[1], op[2], op[3]);
        ins.ins_str = ins_str;
        for (i=0; i<num-1; i++) begin
            split(op[i], key, val);
            ins.ops[i].key=key;
            ins.ops[i].val=val;
        end
        cov1.sample (ins);
    endfunction
`endif

endmodule: uvmt_cv32_step_compare

`endif //__UVMT_CV32_STEP_COMPARE_SV__

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
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
//


`ifndef __UVMT_CV32E40P_STEP_COMPARE_SV__
`define __UVMT_CV32E40P_STEP_COMPARE_SV__

// Step-and-Compare between the CV32E40PE40P and Imperas OVPsim ISS
// Cloned from the Imperas demo at $(IMPERAS_HOME)/RTL_OVPmodel_step_compare/verilog_testbench/testbench.sv

/*
 * Copyright (c) 2005-2020 Imperas Software Ltd., www.imperas.com
 * Copyright (C) Tumbush Enterprises, LLC
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

//
// Execute step and compare of dut OVP instance vs riscv RTL instance
//
`ifndef T0_TYPE
  `define T0_TYPE "RV32IMC"
`endif

import uvm_pkg::*;      // needed for the UVM messaging service (`uvm_info(), etc.)

`include "uvm_macros.svh"
`define CV32E40P_CORE   $root.uvmt_cv32e40p_tb.dut_wrap.cv32e40p_wrapper_i.core_i
`define CV32E40P_TRACER $root.uvmt_cv32e40p_tb.dut_wrap.cv32e40p_wrapper_i.tracer_i

// TODO change names
`define CV32E40P_RM              $root.uvmt_cv32e40p_tb.iss_wrap.cpu
`define CV32E40P_RM_RVVI_STATE   $root.uvmt_cv32e40p_tb.iss_wrap.cpu.state
`define CV32E40P_RM_RVVI_CONTROL $root.uvmt_cv32e40p_tb.iss_wrap.cpu.control


module uvmt_cv32e40p_step_compare
(
   uvma_clknrst_if                clknrst_if,
   uvmt_cv32e40p_step_compare_if  step_compare_if
);

   bit  Clk;
   bit  miscompare;
   bit  is_stall_sim = 0;
   bit  ignore_dpc_check = 0;
   bit  use_iss = 0;

  // FIXME:strichmo:when running random interrupts and random debug requests it is possible to enter debug mode
  // (while also acking an interrupt) when the debug program counter may or may not yet be pointing to the interrupt
  // vector (mtvec) upon debug entry.  However the PC stream should verify proper operation (the PC will mismatch when
  // the debug ROM eventually executes a dret).  For now we will skip this comparison if the test requests it
  initial begin
    if ($test$plusargs("ignore_dpc_check")) begin
      ignore_dpc_check = 1;
      `uvm_info("Step-and-Compare", $sformatf("Requesting +ignore_dpc_check"), UVM_NONE)
    end
    else begin
      ignore_dpc_check = 0;
    end
  end

  initial begin
    if ($test$plusargs("USE_ISS"))
      use_iss = 1;
  end

  // Set the is_stall_sim flag if random stalls are enabled
  // This will turn off some unpredictable checks:
  // - CSR wire checks
  // - Non-written GPR registers (per instructions)
  // Note that register writebacks to GPRs will still be checked during each instruction retirement even with stalls

  initial begin
    if (!$test$plusargs("rand_stall_obi_disable")) begin
      is_stall_sim = 1;
    end
  end

  always begin
    wait (clknrst_if.reset_n === 1'b0);
    wait (clknrst_if.reset_n === 1'b1);
    if (is_stall_sim) begin
      `uvm_info("Step-andCompare", $sformatf("is_stall_sim set to 1, disabling CSR wire checks and stable GPR register checks"), UVM_NONE)
    end
  end

                                                                                                          // Waiving Verissimo SVTB.32.2.0: Pass strings by reference unless otherwise needed
  function void check_32bit(input string compared, input bit [31:0] expected, input logic [31:0] actual); //@DVT_LINTER_WAIVER "MT20211228_1" disable SVTB.32.2.0
      static int now = 0;
      if (now != $time) begin
        miscompare = 0;
        now = $time;
      end
      if (expected !== actual) begin
        miscompare = 1;
        `uvm_error("Step-and-Compare", $sformatf("%s expected=0x%8h and actual=0x%8h PC=0x%8h", compared, expected, actual, step_compare_if.ovp_cpu_PCr))
      end else begin
        `uvm_info("Step-and-Compare", $sformatf("%s expected=0x%8h==actual", compared, actual), UVM_DEBUG)
      end
   endfunction // check_32bit

   function automatic void compare();
      int idx;
      logic [ 5:0] insn_regs_write_addr;
      logic [31:0] insn_regs_write_value;
      int          insn_regs_write_size;
      string       compared_str;
      bit ignore;

      logic [31:0] csr_val;

      // Compare PC
      //check_32bit(.compared("PC"), .expected(step_compare_if.ovp_cpu_PCr), .actual(step_compare_if.insn_pc));
      check_32bit(.compared("PC"), .expected(`CV32E40P_RM_RVVI_STATE.pc), .actual(step_compare_if.insn_pc));
      step_compare_if.num_pc_checks++;

      // Compare GPR's
      // Assuming that `CV32E40P_TRACER.insn_regs_write size is never > 1.  Check this.
      // Note that dut_wrap is found 1 level up
      insn_regs_write_size = `CV32E40P_TRACER.insn_regs_write.size();
      if (insn_regs_write_size > 1) begin
        `uvm_error("Step-and-Compare",  $sformatf("Assume insn_regs_write size is 0 or 1 but is %0d", insn_regs_write_size))
      end
      else if (insn_regs_write_size == 1) begin // Get `CV32E40P_TRACER.insn_regs_write fields if size is 1
         insn_regs_write_addr  = `CV32E40P_TRACER.insn_regs_write[0].addr;
         insn_regs_write_value = `CV32E40P_TRACER.insn_regs_write[0].value;
         `uvm_info("Step-and-Compare", $sformatf("insn_regs_write queue[0] addr=0x%0x, value=0x%0x", insn_regs_write_addr, insn_regs_write_value), UVM_DEBUG)
      end

      // Ignore insn_regs_write_addr=0 just like in riscv_tracer.sv
      for (idx=0; idx<32; idx++) begin
         compared_str = $sformatf("GPR[%0d]", idx);
         if ((idx == insn_regs_write_addr) && (idx != 0) && (insn_regs_write_size == 1)) // Use register in insn_regs_write queue if it exists
            check_32bit(.compared(compared_str), .expected(step_compare_if.ovp_cpu_GPR[idx][31:0]), .actual(insn_regs_write_value));
         // FIXME:strichmo:I am removing the static (non-written) register checks, as they fail in presence of I and D bus RAM stalls
         // It would be highly desirable to find an alternative for this type of check to ensure unintended writes to do not
         else if (!is_stall_sim && !`CV32E40P_TRACER.insn_wb_bypass) // Use actual value from RTL to compare registers which should have not changed
            check_32bit(.compared(compared_str), .expected(step_compare_if.ovp_cpu_GPR[idx][31:0]), .actual(step_compare_if.riscy_GPR[idx]));
         step_compare_if.num_gpr_checks++;
      end

      // Compare CSR's
      foreach(`CV32E40P_RM_RVVI_STATE.csr[index]) begin
          step_compare_if.num_csr_checks++;
          ignore = 0;
          csr_val = 0;

          // CSR timing at instruction retirement is not completely deterministic in this simple model in presence of OBI stalls
          if (is_stall_sim)
          ignore = 1;
          case (index)

            "marchid"       : csr_val = cv32e40p_pkg::MARCHID; // warning!  defined in cv32e40p_pkg

            "mcountinhibit" : csr_val = `CV32E40P_CORE.cs_registers_i.mcountinhibit_q;

            "mvendorid"     : csr_val = {cv32e40p_pkg::MVENDORID_BANK, cv32e40p_pkg::MVENDORID_OFFSET};
            "mstatus"       : if (step_compare_if.deferint_prime == 0) ignore = 1;
                              else csr_val = {`CV32E40P_CORE.cs_registers_i.mstatus_q.mprv, // Not documented in Rev 4.5 of user_manual.doc but is in the design
                                        4'b0,
                                        `CV32E40P_CORE.cs_registers_i.mstatus_q.mpp,
                                        3'b0,
                                        `CV32E40P_CORE.cs_registers_i.mstatus_q.mpie,
                                        2'b0,
                                        `CV32E40P_CORE.cs_registers_i.mstatus_q.upie,
                                        `CV32E40P_CORE.cs_registers_i.mstatus_q.mie,
                                        2'b0,
                                        `CV32E40P_CORE.cs_registers_i.mstatus_q.uie};
            "misa"          : csr_val = `CV32E40P_CORE.cs_registers_i.MISA_VALUE;
            "mie"           : csr_val = `CV32E40P_CORE.cs_registers_i.mie_q;
            "mtvec"         : csr_val = {`CV32E40P_CORE.cs_registers_i.mtvec_q, 6'h0, `CV32E40P_CORE.cs_registers_i.mtvec_mode_q};
            "mscratch"      : csr_val = `CV32E40P_CORE.cs_registers_i.mscratch_q;
            "mepc"          : if (step_compare_if.deferint_prime == 0) ignore = 1;
                              else csr_val = `CV32E40P_CORE.cs_registers_i.mepc_q;
            "mcause"        : if (step_compare_if.deferint_prime == 0) ignore = 1;
                              else csr_val = {`CV32E40P_CORE.cs_registers_i.mcause_q[5],
                                              26'b0,
                                              `CV32E40P_CORE.cs_registers_i.mcause_q[4:0]};
          //  "mip"           : if (step_compare_if.deferint_prime == 0 || iss_wrap.io.deferint == 0) ignore = 1;
          //                    else csr_val = `CV32E40P_CORE.cs_registers_i.mip;
            "mip"           : ignore = 1;
            "mhartid"       : csr_val = `CV32E40P_CORE.cs_registers_i.hart_id_i;

            // only valid in DEBUG Mode
            "dcsr"          : begin
                              csr_val = `CV32E40P_CORE.cs_registers_i.dcsr_q;
                              if (iss_wrap.io.DM==0) ignore = 1;
            end
            "dpc"           : begin
                              csr_val = `CV32E40P_CORE.cs_registers_i.depc_q;
                              if (iss_wrap.io.DM==0) ignore = 1;
                              if (ignore_dpc_check) ignore = 1;
            end

            "dscratch0"     : csr_val = `CV32E40P_CORE.cs_registers_i.dscratch0_q;
            "dscratch1"     : csr_val = `CV32E40P_CORE.cs_registers_i.dscratch1_q;
            "pmpcfg0"       : csr_val = `CV32E40P_CORE.cs_registers_i.pmp_reg_q.pmpcfg_packed[0];
            "pmpcfg1"       : csr_val = `CV32E40P_CORE.cs_registers_i.pmp_reg_q.pmpcfg_packed[1];
            "pmpcfg2"       : csr_val = `CV32E40P_CORE.cs_registers_i.pmp_reg_q.pmpcfg_packed[2];
            "pmpcfg3"       : csr_val = `CV32E40P_CORE.cs_registers_i.pmp_reg_q.pmpcfg_packed[3];
            "tselect"       : csr_val = 32'h0000_0000;
            "tdata1"        : csr_val = `CV32E40P_CORE.cs_registers_i.tmatch_control_rdata;
            "tdata2"        : csr_val = `CV32E40P_CORE.cs_registers_i.tmatch_value_rdata;
            "tdata3"        : csr_val = 32'h0000_0000;
            "tinfo"         : csr_val = `CV32E40P_CORE.cs_registers_i.tinfo_types;

            "time"          : ignore  = 1;

            "mcontext"      : ignore  = 1;
            "scontext"      : ignore  = 1;

            "cycle"         : ignore  = 1;
            "cycleh"        : ignore  = 1;
            "instret"       : ignore  = 1;
            "instreth"      : ignore  = 1;
            "minstret"      : ignore  = 1;
            "minstreth"     : ignore  = 1;

            "mimpid"        : ignore  = 1;

            "hpmcounter3"   : ignore  = 1;
            "hpmcounter4"   : ignore  = 1;
            "hpmcounter5"   : ignore  = 1;
            "hpmcounter6"   : ignore  = 1;
            "hpmcounter7"   : ignore  = 1;
            "hpmcounter8"   : ignore  = 1;
            "hpmcounter9"   : ignore  = 1;
            "hpmcounter10"  : ignore  = 1;
            "hpmcounter11"  : ignore  = 1;
            "hpmcounter12"  : ignore  = 1;
            "hpmcounter13"  : ignore  = 1;
            "hpmcounter14"  : ignore  = 1;
            "hpmcounter15"  : ignore  = 1;
            "hpmcounter16"  : ignore  = 1;
            "hpmcounter17"  : ignore  = 1;
            "hpmcounter18"  : ignore  = 1;
            "hpmcounter19"  : ignore  = 1;
            "hpmcounter20"  : ignore  = 1;
            "hpmcounter21"  : ignore  = 1;
            "hpmcounter22"  : ignore  = 1;
            "hpmcounter23"  : ignore  = 1;
            "hpmcounter24"  : ignore  = 1;
            "hpmcounter25"  : ignore  = 1;
            "hpmcounter26"  : ignore  = 1;
            "hpmcounter27"  : ignore  = 1;
            "hpmcounter28"  : ignore  = 1;
            "hpmcounter29"  : ignore  = 1;
            "hpmcounter30"  : ignore  = 1;
            "hpmcounter31"  : ignore  = 1;

            "hpmcounterh3"  : ignore  = 1;
            "hpmcounterh4"  : ignore  = 1;
            "hpmcounterh5"  : ignore  = 1;
            "hpmcounterh6"  : ignore  = 1;
            "hpmcounterh7"  : ignore  = 1;
            "hpmcounterh8"  : ignore  = 1;
            "hpmcounterh9"  : ignore  = 1;
            "hpmcounterh10" : ignore  = 1;
            "hpmcounterh11" : ignore  = 1;
            "hpmcounterh12" : ignore  = 1;
            "hpmcounterh13" : ignore  = 1;
            "hpmcounterh14" : ignore  = 1;
            "hpmcounterh15" : ignore  = 1;
            "hpmcounterh16" : ignore  = 1;
            "hpmcounterh17" : ignore  = 1;
            "hpmcounterh18" : ignore  = 1;
            "hpmcounterh19" : ignore  = 1;
            "hpmcounterh20" : ignore  = 1;
            "hpmcounterh21" : ignore  = 1;
            "hpmcounterh22" : ignore  = 1;
            "hpmcounterh23" : ignore  = 1;
            "hpmcounterh24" : ignore  = 1;
            "hpmcounterh25" : ignore  = 1;
            "hpmcounterh26" : ignore  = 1;
            "hpmcounterh27" : ignore  = 1;
            "hpmcounterh28" : ignore  = 1;
            "hpmcounterh29" : ignore  = 1;
            "hpmcounterh30" : ignore  = 1;
            "hpmcounterh31" : ignore  = 1;

            "mhpmcounter3"  : ignore  = 1;
            "mhpmcounter4"  : ignore  = 1;
            "mhpmcounter5"  : ignore  = 1;
            "mhpmcounter6"  : ignore  = 1;
            "mhpmcounter7"  : ignore  = 1;
            "mhpmcounter8"  : ignore  = 1;
            "mhpmcounter9"  : ignore  = 1;
            "mhpmcounter10" : ignore  = 1;
            "mhpmcounter11" : ignore  = 1;
            "mhpmcounter12" : ignore  = 1;
            "mhpmcounter13" : ignore  = 1;
            "mhpmcounter14" : ignore  = 1;
            "mhpmcounter15" : ignore  = 1;
            "mhpmcounter16" : ignore  = 1;
            "mhpmcounter17" : ignore  = 1;
            "mhpmcounter18" : ignore  = 1;
            "mhpmcounter19" : ignore  = 1;
            "mhpmcounter20" : ignore  = 1;
            "mhpmcounter21" : ignore  = 1;
            "mhpmcounter22" : ignore  = 1;
            "mhpmcounter23" : ignore  = 1;
            "mhpmcounter24" : ignore  = 1;
            "mhpmcounter25" : ignore  = 1;
            "mhpmcounter26" : ignore  = 1;
            "mhpmcounter27" : ignore  = 1;
            "mhpmcounter28" : ignore  = 1;
            "mhpmcounter29" : ignore  = 1;
            "mhpmcounter30" : ignore  = 1;
            "mhpmcounter31" : ignore  = 1;

            "mhpmcounterh3" : ignore  = 1;
            "mhpmcounterh4" : ignore  = 1;
            "mhpmcounterh5" : ignore  = 1;
            "mhpmcounterh6" : ignore  = 1;
            "mhpmcounterh7" : ignore  = 1;
            "mhpmcounterh8" : ignore  = 1;
            "mhpmcounterh9" : ignore  = 1;
            "mhpmcounterh10": ignore  = 1;
            "mhpmcounterh11": ignore  = 1;
            "mhpmcounterh12": ignore  = 1;
            "mhpmcounterh13": ignore  = 1;
            "mhpmcounterh14": ignore  = 1;
            "mhpmcounterh15": ignore  = 1;
            "mhpmcounterh16": ignore  = 1;
            "mhpmcounterh17": ignore  = 1;
            "mhpmcounterh18": ignore  = 1;
            "mhpmcounterh19": ignore  = 1;
            "mhpmcounterh20": ignore  = 1;
            "mhpmcounterh21": ignore  = 1;
            "mhpmcounterh22": ignore  = 1;
            "mhpmcounterh23": ignore  = 1;
            "mhpmcounterh24": ignore  = 1;
            "mhpmcounterh25": ignore  = 1;
            "mhpmcounterh26": ignore  = 1;
            "mhpmcounterh27": ignore  = 1;
            "mhpmcounterh28": ignore  = 1;
            "mhpmcounterh29": ignore  = 1;
            "mhpmcounterh30": ignore  = 1;
            "mhpmcounterh31": ignore  = 1;

            default: begin
              `uvm_error("STEP_COMPARE", $sformatf("index=%s does not match a CSR name", index))
              ignore = 1;
            end
          endcase // case (index)

          if (!ignore)
            check_32bit(.compared(index), .expected(`CV32E40P_RM_RVVI_STATE.csr[index]), .actual(csr_val));

      end // foreach (ovp.cpu.csr[index])
    endfunction // compare

    int cycles = 0;
    always @(posedge `CV32E40P_CORE.clk) begin
        cycles++;
    end

    // RTL->RM CSR : mcycle, minstret, mcycleh, minstreth
                                                         // Waiving Verissimo SVTB.32.2.0: Pass strings by reference unless otherwise needed
    function automatic void pushRTL2RM(string message);  //@DVT_LINTER_WAIVER "MT20211228_2" disable SVTB.32.2.0
        logic [ 5:0] gpr_addr;
        logic [31:0] gpr_value;

        if (`CV32E40P_TRACER.insn_regs_write.size()) begin
          gpr_addr  = `CV32E40P_TRACER.insn_regs_write[0].addr;
          gpr_value = `CV32E40P_TRACER.insn_regs_write[0].value;
          `CV32E40P_RM.state.GPR_rtl[gpr_addr] = gpr_value;
        end
        // Pass cycles and reset
        `CV32E40P_RM.cycles = cycles;
        cycles = 0;
    endfunction // pushRTL2RM

    /*
        The schedule works like this
        1. Run the RTL for 1 instruction retirement
        2. if the RTL.RetiredPC == OVP.NextPC
           then run OVP for 1 instruction retirement
        3. Compare RTL <-> OVP
    */
    event ev_compare;
    static int instruction_count = 0;

    typedef enum {
        INIT,
        IDLE,  // Needed to get an event on state so always block is initially entered

        RTL_STEP,
        RTL_VALID,
        RTL_TRAP,
        RTL_HALT,

        RM_STEP,
        RM_VALID,
        RM_TRAP,
        RM_HALT,

        CMP
    } state_e;

   state_e state = INIT;
   initial state <= IDLE; // cause an event for always @*

   always @(*) begin
     if (use_iss) begin
        case (state)
          IDLE: begin
              state <= RTL_STEP;
          end

          RTL_STEP: begin
              clknrst_if.start_clk();
              fork
                  begin
                      @step_compare_if.riscv_retire;
                      clknrst_if.stop_clk();
                      state <= RTL_VALID;
                  end
                  begin
                      @step_compare_if.riscv_trap;
                      state <= RTL_TRAP;
                  end
                  begin
                      @step_compare_if.riscv_halt;
                      state <= RTL_HALT;
                  end
              join_any
              disable fork;
          end

          RTL_VALID: begin
              state <= RM_STEP;
          end

          RTL_TRAP: begin
              //state <= RM_STEP; // TODO: RTL/RVVI needs additional work
              state <= RTL_STEP;
          end

          RTL_HALT: begin
              state <= RTL_STEP;
          end

          RM_STEP: begin
              pushRTL2RM("ret_rtl");
              `CV32E40P_RM_RVVI_CONTROL.stepi();
              fork
                  begin
                      @step_compare_if.ovp_cpu_valid;
                      ->`CV32E40P_TRACER.ovp_retire;
                      state <= RM_VALID;
                  end
                  begin
                      @step_compare_if.ovp_cpu_trap;
                      state <= RM_TRAP;
                  end
                  begin
                      @step_compare_if.ovp_cpu_halt;
                      state <= RM_HALT;
                  end
              join_any
              disable fork;
          end

          RM_VALID: begin
              state <= CMP;
          end

          RM_TRAP: begin
              //state <= CMP; // TODO: needs enabling after RTL/RVVI fix
              state <= RM_STEP;
          end

          RM_HALT: begin
              state <= RM_STEP;
          end

          CMP: begin
              compare();
              ->ev_compare;
              instruction_count += 1;
              //state <= RTL_STEP;
              state <= IDLE;
          end
        endcase // case (state)
     end
   end

   always @(instruction_count) begin
      if (!(instruction_count % 10000)) begin
         `uvm_info("Step-and-Compare", $sformatf("Compared %0d instructions", instruction_count), UVM_NONE)
      end
      if (instruction_count >= 10_000_000) begin
         `uvm_fatal("Step-and-Compare", $sformatf("Compared %0d instructions - that's too long!", instruction_count))
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
        string decode = `CV32E40P_RM.Decode;
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

endmodule: uvmt_cv32e40p_step_compare

`endif //__UVMT_CV32E40P_STEP_COMPARE_SV__


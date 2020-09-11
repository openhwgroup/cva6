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

`ifndef __UVMT_CV32_ISS_WRAP_SV__
`define __UVMT_CV32_ISS_WRAP_SV__

/**
 * Module wrapper for Imperas ISS.
 * Instanitates "CPU", the ISS wrapper, and "RAM" a spare memory model.
 */
module uvmt_cv32_iss_wrap
  #(
    //parameter int ROM_START_ADDR = 'h8000,
    //parameter int ROM_BYTE_SIZE  = 'h20000,
    //parameter int RAM_BYTE_SIZE  = 'h20000,
    parameter int ROM_START_ADDR = 'h00000000,
    parameter int ROM_BYTE_SIZE  = 'h0,
    parameter int RAM_BYTE_SIZE  = 'h400000,
    parameter int ID = 0
   )

   (
    input realtime      clk_period,
    uvma_clknrst_if clknrst_if,
    uvmt_cv32_step_compare_if step_compare_if,
    uvmt_cv32_isa_covg_if     isa_covg_if
//    input bit           Step,
//    input bit           Stepping,
//    output logic [31:0] PCr
   );

    BUS         b1();

    MONITOR     mon(b1);
    RAM         #(
                .ROM_START_ADDR(ROM_START_ADDR),
                .ROM_BYTE_SIZE(ROM_BYTE_SIZE),
                .RAM_BYTE_SIZE(RAM_BYTE_SIZE)) ram(b1);

    CPU #(.ID(ID)) cpu(b1);

   assign b1.Clk = clknrst_if.clk;
   assign step_compare_if.ovp_cpu_PCr = cpu.PCr;
`ifndef DSIM
   assign step_compare_if.ovp_cpu_GPR = cpu.GPR;
 `else
   assign step_compare_if.ovp_cpu_GPR[31] = cpu.GPR[31];
   assign step_compare_if.ovp_cpu_GPR[30] = cpu.GPR[30];
   assign step_compare_if.ovp_cpu_GPR[29] = cpu.GPR[29];
   assign step_compare_if.ovp_cpu_GPR[28] = cpu.GPR[28];
   assign step_compare_if.ovp_cpu_GPR[27] = cpu.GPR[27];
   assign step_compare_if.ovp_cpu_GPR[26] = cpu.GPR[26];
   assign step_compare_if.ovp_cpu_GPR[25] = cpu.GPR[25];
   assign step_compare_if.ovp_cpu_GPR[24] = cpu.GPR[24];
   assign step_compare_if.ovp_cpu_GPR[23] = cpu.GPR[23];
   assign step_compare_if.ovp_cpu_GPR[22] = cpu.GPR[22];
   assign step_compare_if.ovp_cpu_GPR[21] = cpu.GPR[21];
   assign step_compare_if.ovp_cpu_GPR[20] = cpu.GPR[20];
   assign step_compare_if.ovp_cpu_GPR[19] = cpu.GPR[19];
   assign step_compare_if.ovp_cpu_GPR[18] = cpu.GPR[18];
   assign step_compare_if.ovp_cpu_GPR[17] = cpu.GPR[17];
   assign step_compare_if.ovp_cpu_GPR[16] = cpu.GPR[16];
   assign step_compare_if.ovp_cpu_GPR[15] = cpu.GPR[15];
   assign step_compare_if.ovp_cpu_GPR[14] = cpu.GPR[14];
   assign step_compare_if.ovp_cpu_GPR[13] = cpu.GPR[13];
   assign step_compare_if.ovp_cpu_GPR[12] = cpu.GPR[12];
   assign step_compare_if.ovp_cpu_GPR[11] = cpu.GPR[11];
   assign step_compare_if.ovp_cpu_GPR[10] = cpu.GPR[10];
   assign step_compare_if.ovp_cpu_GPR[9]  = cpu.GPR[9];
   assign step_compare_if.ovp_cpu_GPR[8]  = cpu.GPR[8];
   assign step_compare_if.ovp_cpu_GPR[7]  = cpu.GPR[7];
   assign step_compare_if.ovp_cpu_GPR[6]  = cpu.GPR[6];
   assign step_compare_if.ovp_cpu_GPR[5]  = cpu.GPR[5];
   assign step_compare_if.ovp_cpu_GPR[4]  = cpu.GPR[4];
   assign step_compare_if.ovp_cpu_GPR[3]  = cpu.GPR[3];
   assign step_compare_if.ovp_cpu_GPR[2]  = cpu.GPR[2];
   assign step_compare_if.ovp_cpu_GPR[1]  = cpu.GPR[1];
   assign step_compare_if.ovp_cpu_GPR[0]  = cpu.GPR[0];
 `endif  // DSIM
   always @(step_compare_if.ovp_b1_Step) b1.Step = step_compare_if.ovp_b1_Step;
   assign b1.Stepping = step_compare_if.ovp_b1_Stepping;

   always @(step_compare_if.ovp_cpu_busWait) cpu.busWait();
   always @(cpu.Retire) -> step_compare_if.ovp_cpu_retire;

    function void split(input string in_s, output string s1, s2);
        automatic int i;
        for (i=0; i<in_s.len(); i++) begin
            if (in_s.getc(i) == ":")
                break;
         end
         if (i==0 ) begin
            $display("ERROR not : found in split '%0s'", in_s);
            $finish(-1);
         end
         s1 = in_s.substr(0,i-1);
         s2 = in_s.substr(i+1,in_s.len()-1);
    endfunction

    function automatic void sample();
        string decode = cpu.Decode;
        string ins_str, op[4], key, val;
        int i;

        int num = $sscanf (decode, "%s %s %s %s %s", ins_str, op[0], op[1], op[2], op[3]);
        isa_covg_if.ins.ins_str = ins_str;
        isa_covg_if.ins.pc = cpu.PCr;
        isa_covg_if.ins.compressed = dut_wrap.cv32e40p_wrapper_i.tracer_i.insn_compressed;        
        for (i=0; i<num-1; i++) begin
            split(op[i], key, val);
            isa_covg_if.ins.ops[i].key=key;
            isa_covg_if.ins.ops[i].val=val;
        end
        `uvm_info("OVPSIM", $sformatf("Decoded instr: %s%s pc: 0x%08x", isa_covg_if.ins.compressed ? "c." : "",
                                                                    decode,
                                                                    isa_covg_if.ins.pc), 
                            UVM_DEBUG)
        ->isa_covg_if.ins_valid;
    endfunction

   always @(cpu.Retire) begin
       sample();
   end

   initial begin
     clknrst_if.clk = 1'b0;
      #1;  // time for clknrst_if_dut to set the clk_period
      wait (clk_period != 0.0);
      `uvm_info("ISSWRAP", "Starting ISS clock", UVM_LOW)
      clknrst_if.set_period(clk_period);
      clknrst_if.start_clk();
   end

endmodule : uvmt_cv32_iss_wrap

`endif // __UVMT_CV32_ISS_WRAP_SV__


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

`default_nettype none

`ifdef TB_CORE
  `define TB tb_top
  `define P2C tb_top.riscv_wrapper_i
`else
  // Module name of top level testbench
  `define TB uvmt_cv32_tb
  // Hierachical path to the core (riscv_core_i)
  `define P2C uvmt_cv32_tb.dut_wrap
`endif

module bind_pc(pc_if pc_if_i);

   assign pc_if_i.insn_pc = `P2C.riscv_core_i.riscv_tracer_i.insn_pc;
   assign pc_if_i.iss_pc  = `TB.iss_wrap.cpu.PCr;
                             
endmodule // bind_pc
`default_nettype wire

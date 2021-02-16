/*
 * Copyright 2020 OpenHW Group
 * Copyright 2020 Silicon Labs, Inc.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */


/*
 * corev_nop_instr
 *
 * Generates a compressed or non-compressed NOP (pseduo-op)
 */
 
class corev_nop_instr extends riscv_directed_instr_stream;

  `uvm_object_utils(corev_nop_instr)

  function new(string name = "");
    super.new(name);
  endfunction : new

  function void post_randomize();
    riscv_instr_name_t allowed_nop[$];
    riscv_instr        nop;

    allowed_nop.push_back(NOP);
    if (!cfg.disable_compressed_instr)
      allowed_nop.push_back(C_NOP);

    nop = riscv_instr::get_rand_instr(.include_instr(allowed_nop));
    nop.m_cfg = cfg;
    randomize_gpr(nop);
    insert_instr(nop);
  endfunction : post_randomize

endclass : corev_nop_instr

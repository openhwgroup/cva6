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
 * corev_xori_not_instr
 *
 * Generates a XORI with a -1 immediate value to tesdt logical not pseudo-op
 */
 
class corev_xori_not_instr extends riscv_directed_instr_stream;

  `uvm_object_utils(corev_xori_not_instr)

  function new(string name = "");
    super.new(name);
  endfunction : new

  function void post_randomize();
    riscv_instr_name_t allowed_xori[$];
    riscv_instr        xori;

    allowed_xori.push_back(XORI);

    xori = riscv_instr::get_rand_instr(.include_instr(allowed_xori));
    xori.m_cfg = cfg;
    randomize_gpr(xori);
    xori.imm = -1;
    xori.extend_imm();
    xori.update_imm_str();
    xori.comment = "corev_xori_not_instr";
    insert_instr(xori, 0);
  endfunction : post_randomize

endclass : corev_xori_not_instr


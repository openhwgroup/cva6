// Copyright 2021 OpenHW Group
// Copyright 2021 Silicon Labs, Inc.
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

#include "svdpi.h"
#include "string.h"
#include "disasm.h"
#include "extension.h"

using namespace std;

// Global class pointers
function <extension_t*()> gcp_extension;

// Global strings
string          gs_ext_str;
string          gs_ret_str;

// Global pointers
disassembler_t* gp_disassembler;
insn_t*         gp_insn;

// Global variables
uint8_t         gv_xlen;
uint8_t         gv_is_big_endian;

// Error messages
const           string errmsg[2] = { /* 0 */ "DPI_ERROR: Invalid arguments in disassembler configuration\n",
                                     /* 1 */ "DPI_ERROR: Disassembler config not set\n" };

// Constants
const int       instr_len    = 32;

// Headers
uint64_t               endian_swap(uint64_t bits, uint8_t swap_ena);
extern "C" void        set_config(uint32_t bsize, char* isa, uint8_t is_big_endian);
extern "C" void        initialize_disassembler();
extern "C" const char* disassemble_insn_str(uint64_t insn);
extern "C" const char* get_insn_name(uint64_t insn);

//--------------------------------------------------------------------------------

extern "C" void set_config(uint32_t bsize, char* isa, uint8_t is_big_endian) {

  gs_ext_str       = string(isa);
  gv_is_big_endian = is_big_endian;

  [&](const char* gs_ext_str){gcp_extension = find_extension(gs_ext_str);};

  if (bsize != 32 && bsize != 64) {
    cout << errmsg[0];
    return;
  }

  gv_xlen = bsize;

  if (gp_disassembler) {
    delete gp_disassembler;
    initialize_disassembler();
  }
}

//--------------------------------------------------------------------------------

extern "C" void initialize_disassembler() {
  if (!gv_xlen) {
    cout << errmsg[1];
    return;
  }

  gp_disassembler = new disassembler_t(gv_xlen);

  if (gcp_extension) {
    for (auto disasm_insn : gcp_extension()->get_disasms()){
      gp_disassembler->add_insn(disasm_insn);
    }
  }
}

//--------------------------------------------------------------------------------

extern "C" const char* disassemble_insn_str(uint64_t insn) {
  if (!gp_disassembler) {
    initialize_disassembler();
  }

  insn        = endian_swap(insn, gv_is_big_endian);
  gs_ret_str  = gp_disassembler->disassemble(insn & 0xFFFFFFFF);

  return gs_ret_str.data();
}

//--------------------------------------------------------------------------------

extern "C" const char* get_insn_name(uint64_t insn) {
  const disasm_insn_t* the_insn;

  if (!gp_disassembler) {
    initialize_disassembler();
  }

  insn       = endian_swap(insn, gv_is_big_endian);
  the_insn = gp_disassembler->lookup(insn & 0xFFFFFFFF);

  // If the opcode is not valid, then return illegal
  if (the_insn == NULL) {
    return "unknown";
  }

  gs_ret_str = the_insn->get_name();

  return gs_ret_str.data();
}

//--------------------------------------------------------------------------------

uint64_t endian_swap(uint64_t bits, uint8_t swap_ena) {
  uint64_t temp = bits;
  if (swap_ena) {
      if (__GNUC__) {
        temp = __builtin_bswap64(bits);
      } else {
        temp = ( ((bits >> 56) & 0x00000000000000FF) |
                 ((bits << 56) & 0xFF00000000000000) |
                 ((bits >> 40) & 0x000000000000FF00) |
                 ((bits << 40) & 0x00FF000000000000) |
                 ((bits >> 24) & 0x0000000000FF0000) |
                 ((bits << 24) & 0x0000FF0000000000) |
                 ((bits >>  8) & 0x00000000FF000000) |
                 ((bits <<  8) & 0x000000FF00000000) );
      }
    temp >>= (64 - instr_len);
  }
  return temp;
}

//--------------------------------------------------------------------------------
// C-wrappers for insn_t methods
//--------------------------------------------------------------------------------

extern "C" int length(uint64_t insn) {
  gp_insn      = new insn_t(insn);
  uint32_t tmp = gp_insn->length();

  delete gp_insn;
  return tmp;
}

//--------------------------------------------------------------------------------

extern "C" int64_t i_imm(uint64_t insn) {
  gp_insn      = new insn_t(insn);
  uint64_t tmp = gp_insn->i_imm();

  delete gp_insn;
  return tmp;
}

//--------------------------------------------------------------------------------

extern "C" int64_t s_imm(uint64_t insn) {
  gp_insn      = new insn_t(insn);
  uint64_t tmp = gp_insn->s_imm();

  delete gp_insn;
  return tmp;
}

//--------------------------------------------------------------------------------

extern "C" int64_t sb_imm(uint64_t insn) {
  gp_insn      = new insn_t(insn);
  uint64_t tmp = gp_insn->sb_imm();

  delete gp_insn;
  return tmp;
}

//--------------------------------------------------------------------------------

extern "C" int64_t u_imm(uint64_t insn) {
  gp_insn      = new insn_t(insn);
  uint64_t tmp = gp_insn->u_imm();

  delete gp_insn;
  return tmp;
}

//--------------------------------------------------------------------------------

extern "C" int64_t uj_imm(uint64_t insn) {
  gp_insn      = new insn_t(insn);
  uint64_t tmp = gp_insn->uj_imm();

  delete gp_insn;
  return tmp;
}

//--------------------------------------------------------------------------------

extern "C" int64_t shamt(uint64_t insn) {
  gp_insn      = new insn_t(insn);
  uint64_t tmp = gp_insn->shamt();

  delete gp_insn;
  return tmp;
}

//--------------------------------------------------------------------------------

extern "C" uint64_t rd(uint64_t insn) {
  gp_insn      = new insn_t(insn);
  uint64_t tmp = gp_insn->rd();

  delete gp_insn;
  return tmp;
}

//--------------------------------------------------------------------------------

extern "C" uint64_t rs1(uint64_t insn) {
  gp_insn      = new insn_t(insn);
  uint64_t tmp = gp_insn->rs1();

  delete gp_insn;
  return tmp;
}

//--------------------------------------------------------------------------------

extern "C" uint64_t rs2(uint64_t insn) {
  gp_insn      = new insn_t(insn);
  uint64_t tmp = gp_insn->rs2();

  delete gp_insn;
  return tmp;
}

//--------------------------------------------------------------------------------

extern "C" uint64_t rs3(uint64_t insn) {
  gp_insn      = new insn_t(insn);
  uint64_t tmp = gp_insn->rs3();

  delete gp_insn;
  return tmp;
}

//--------------------------------------------------------------------------------

extern "C" uint64_t rm(uint64_t insn) {
  gp_insn      = new insn_t(insn);
  uint64_t tmp = gp_insn->rm();

  delete gp_insn;
  return tmp;
}

//--------------------------------------------------------------------------------

extern "C" uint64_t csr(uint64_t insn) {
  gp_insn      = new insn_t(insn);
  uint64_t tmp = gp_insn->csr();

  delete gp_insn;
  return tmp;
}

//--------------------------------------------------------------------------------

extern "C" uint64_t iorw(uint64_t insn) {
  gp_insn      = new insn_t(insn);
  uint64_t tmp = gp_insn->iorw();

  delete gp_insn;
  return tmp;
}

//--------------------------------------------------------------------------------

extern "C" uint64_t bs(uint64_t insn) {
  gp_insn      = new insn_t(insn);
  uint64_t tmp = gp_insn->bs();

  delete gp_insn;
  return tmp;
}

//--------------------------------------------------------------------------------

extern "C" uint64_t rcon(uint64_t insn) {
  gp_insn      = new insn_t(insn);
  uint64_t tmp = gp_insn->rcon();

  delete gp_insn;
  return tmp;
}

//--------------------------------------------------------------------------------

extern "C" int64_t rvc_imm(uint64_t insn) {
  gp_insn     = new insn_t(insn);
  int64_t tmp = gp_insn->rvc_imm();

  delete gp_insn;
  return tmp;
}

//--------------------------------------------------------------------------------

extern "C" int64_t rvc_zimm(uint64_t insn) {
  gp_insn     = new insn_t(insn);
  int64_t tmp = gp_insn->rvc_zimm();

  delete gp_insn;
  return tmp;
}

//--------------------------------------------------------------------------------

extern "C" int64_t rvc_addi4spn_imm(uint64_t insn) {
  gp_insn     = new insn_t(insn);
  int64_t tmp = gp_insn->rvc_addi4spn_imm();

  delete gp_insn;
  return tmp;
}

//--------------------------------------------------------------------------------

extern "C" int64_t rvc_addi16sp_imm(uint64_t insn) {
  gp_insn     = new insn_t(insn);
  int64_t tmp = gp_insn->rvc_addi16sp_imm();

  delete gp_insn;
  return tmp;
}

//--------------------------------------------------------------------------------

extern "C" int64_t rvc_lwsp_imm(uint64_t insn) {
  gp_insn     = new insn_t(insn);
  int64_t tmp = gp_insn->rvc_lwsp_imm();

  delete gp_insn;
  return tmp;
}

//--------------------------------------------------------------------------------

extern "C" int64_t rvc_ldsp_imm(uint64_t insn) {
  gp_insn     = new insn_t(insn);
  int64_t tmp = gp_insn->rvc_ldsp_imm();

  delete gp_insn;
  return tmp;
}

//--------------------------------------------------------------------------------

extern "C" int64_t rvc_swsp_imm(uint64_t insn) {
  gp_insn     = new insn_t(insn);
  int64_t tmp = gp_insn->rvc_swsp_imm();

  delete gp_insn;
  return tmp;
}

//--------------------------------------------------------------------------------

extern "C" int64_t rvc_sdsp_imm(uint64_t insn) {
  gp_insn     = new insn_t(insn);
  int64_t tmp = gp_insn->rvc_sdsp_imm();

  delete gp_insn;
  return tmp;
}

//--------------------------------------------------------------------------------

extern "C" int64_t rvc_lw_imm(uint64_t insn) {
  gp_insn     = new insn_t(insn);
  int64_t tmp = gp_insn->rvc_lw_imm();

  delete gp_insn;
  return tmp;
}

//--------------------------------------------------------------------------------

extern "C" int64_t rvc_ld_imm(uint64_t insn) {
  gp_insn     = new insn_t(insn);
  int64_t tmp = gp_insn->rvc_ld_imm();

  delete gp_insn;
  return tmp;
}

//--------------------------------------------------------------------------------

extern "C" int64_t rvc_j_imm(uint64_t insn) {
  gp_insn     = new insn_t(insn);
  int64_t tmp = gp_insn->rvc_j_imm();

  delete gp_insn;
  return tmp;
}

//--------------------------------------------------------------------------------

extern "C" int64_t rvc_b_imm(uint64_t insn) {
  gp_insn     = new insn_t(insn);
  int64_t tmp = gp_insn->rvc_b_imm();

  delete gp_insn;
  return tmp;
}

//--------------------------------------------------------------------------------

extern "C" int64_t rvc_simm3(uint64_t insn) {
  gp_insn     = new insn_t(insn);
  int64_t tmp = gp_insn->rvc_simm3();

  delete gp_insn;
  return tmp;
}

//--------------------------------------------------------------------------------

extern "C" uint64_t rvc_rd(uint64_t insn) {
  gp_insn      = new insn_t(insn);
  uint64_t tmp = gp_insn->rvc_rd();

  delete gp_insn;
  return tmp;
}

//--------------------------------------------------------------------------------

extern "C" uint64_t rvc_rs1(uint64_t insn) {
  gp_insn      = new insn_t(insn);
  uint64_t tmp = gp_insn->rvc_rs1();

  delete gp_insn;
  return tmp;
}

//--------------------------------------------------------------------------------

extern "C" uint64_t rvc_rs2(uint64_t insn) {
  gp_insn      = new insn_t(insn);
  uint64_t tmp = gp_insn->rvc_rs2();

  delete gp_insn;
  return tmp;
}

//--------------------------------------------------------------------------------

extern "C" uint64_t rvc_rs1s(uint64_t insn) {
  gp_insn      = new insn_t(insn);
  uint64_t tmp = gp_insn->rvc_rs1s();

  delete gp_insn;
  return tmp;
}

//--------------------------------------------------------------------------------

extern "C" uint64_t rvc_rs2s(uint64_t insn) {
  gp_insn      = new insn_t(insn);
  uint64_t tmp = gp_insn->rvc_rs2s();

  delete gp_insn;
  return tmp;
}

//--------------------------------------------------------------------------------

extern "C" uint64_t v_vm(uint64_t insn) {
  gp_insn      = new insn_t(insn);
  uint64_t tmp = gp_insn->v_vm();

  delete gp_insn;
  return tmp;
}

//--------------------------------------------------------------------------------

extern "C" uint64_t v_wd(uint64_t insn) {
  gp_insn      = new insn_t(insn);
  uint64_t tmp = gp_insn->v_wd();

  delete gp_insn;
  return tmp;
}

//--------------------------------------------------------------------------------

extern "C" uint64_t v_nf(uint64_t insn) {
  gp_insn      = new insn_t(insn);
  uint64_t tmp = gp_insn->v_nf();

  delete gp_insn;
  return tmp;
}

//--------------------------------------------------------------------------------

extern "C" uint64_t v_simm5(uint64_t insn) {
  gp_insn      = new insn_t(insn);
  uint64_t tmp = gp_insn->v_simm5();

  delete gp_insn;
  return tmp;
}

//--------------------------------------------------------------------------------

extern "C" uint64_t v_zimm5(uint64_t insn) {
  gp_insn      = new insn_t(insn);
  uint64_t tmp = gp_insn->v_zimm5();

  delete gp_insn;
  return tmp;
}

//--------------------------------------------------------------------------------

extern "C" uint64_t v_zimm11(uint64_t insn) {
  gp_insn      = new insn_t(insn);
  uint64_t tmp = gp_insn->v_zimm11();

  delete gp_insn;
  return tmp;
}

//--------------------------------------------------------------------------------

extern "C" uint64_t v_lmul(uint64_t insn) {
  gp_insn      = new insn_t(insn);
  uint64_t tmp = gp_insn->v_lmul();

  delete gp_insn;
  return tmp;
}

//--------------------------------------------------------------------------------

extern "C" uint64_t v_frac_lmul(uint64_t insn) {
  gp_insn      = new insn_t(insn);
  uint64_t tmp = gp_insn->v_frac_lmul();

  delete gp_insn;
  return tmp;
}

//--------------------------------------------------------------------------------

extern "C" uint64_t v_sew(uint64_t insn) {
  gp_insn      = new insn_t(insn);
  uint64_t tmp = gp_insn->v_sew();

  delete gp_insn;
  return tmp;
}

//--------------------------------------------------------------------------------

extern "C" uint64_t v_width(uint64_t insn) {
  gp_insn      = new insn_t(insn);
  uint64_t tmp = gp_insn->v_width();

  delete gp_insn;
  return tmp;
}

//--------------------------------------------------------------------------------

extern "C" uint64_t v_mop(uint64_t insn) {
  gp_insn      = new insn_t(insn);
  uint64_t tmp = gp_insn->v_mop();

  delete gp_insn;
  return tmp;
}

//--------------------------------------------------------------------------------

extern "C" uint64_t v_lumop(uint64_t insn) {
  gp_insn      = new insn_t(insn);
  uint64_t tmp = gp_insn->v_lumop();

  delete gp_insn;
  return tmp;
}

//--------------------------------------------------------------------------------

extern "C" uint64_t v_sumop(uint64_t insn) {
  gp_insn      = new insn_t(insn);
  uint64_t tmp = gp_insn->v_sumop();

  delete gp_insn;
  return tmp;
}

//--------------------------------------------------------------------------------

extern "C" uint64_t v_vta(uint64_t insn) {
  gp_insn      = new insn_t(insn);
  uint64_t tmp = gp_insn->v_vta();

  delete gp_insn;
  return tmp;
}

//--------------------------------------------------------------------------------

extern "C" uint64_t v_vma(uint64_t insn) {
  gp_insn      = new insn_t(insn);
  uint64_t tmp = gp_insn->v_vma();

  delete gp_insn;
  return tmp;
}

//--------------------------------------------------------------------------------

extern "C" uint64_t v_mew(uint64_t insn) {
  gp_insn      = new insn_t(insn);
  uint64_t tmp = gp_insn->v_mew();

  delete gp_insn;
  return tmp;
}

//--------------------------------------------------------------------------------


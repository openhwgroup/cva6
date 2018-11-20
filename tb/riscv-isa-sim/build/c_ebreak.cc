// See LICENSE for license details.

#include "insn_template.h"

reg_t rv32_c_ebreak(processor_t* p, insn_t insn, reg_t pc)
{
  int xlen = 32;
  reg_t npc = sext_xlen(pc + insn_length( MATCH_C_EBREAK));
  #include "insns/c_ebreak.h"
  trace_opcode(p,  MATCH_C_EBREAK, insn);
  return npc;
}

reg_t rv64_c_ebreak(processor_t* p, insn_t insn, reg_t pc)
{
  int xlen = 64;
  reg_t npc = sext_xlen(pc + insn_length( MATCH_C_EBREAK));
  #include "insns/c_ebreak.h"
  trace_opcode(p,  MATCH_C_EBREAK, insn);
  return npc;
}

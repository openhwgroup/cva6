// See LICENSE for license details.

#include "insn_template.h"

reg_t rv32_slli(processor_t* p, insn_t insn, reg_t pc)
{
  int xlen = 32;
  reg_t npc = sext_xlen(pc + insn_length( MATCH_SLLI));
  #include "insns/slli.h"
  trace_opcode(p,  MATCH_SLLI, insn);
  return npc;
}

reg_t rv64_slli(processor_t* p, insn_t insn, reg_t pc)
{
  int xlen = 64;
  reg_t npc = sext_xlen(pc + insn_length( MATCH_SLLI));
  #include "insns/slli.h"
  trace_opcode(p,  MATCH_SLLI, insn);
  return npc;
}

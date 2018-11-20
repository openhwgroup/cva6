// See LICENSE for license details.

#include "insn_template.h"

reg_t rv32_slliw(processor_t* p, insn_t insn, reg_t pc)
{
  int xlen = 32;
  reg_t npc = sext_xlen(pc + insn_length( MATCH_SLLIW));
  #include "insns/slliw.h"
  trace_opcode(p,  MATCH_SLLIW, insn);
  return npc;
}

reg_t rv64_slliw(processor_t* p, insn_t insn, reg_t pc)
{
  int xlen = 64;
  reg_t npc = sext_xlen(pc + insn_length( MATCH_SLLIW));
  #include "insns/slliw.h"
  trace_opcode(p,  MATCH_SLLIW, insn);
  return npc;
}

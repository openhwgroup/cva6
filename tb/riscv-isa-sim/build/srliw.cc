// See LICENSE for license details.

#include "insn_template.h"

reg_t rv32_srliw(processor_t* p, insn_t insn, reg_t pc)
{
  int xlen = 32;
  reg_t npc = sext_xlen(pc + insn_length( MATCH_SRLIW));
  #include "insns/srliw.h"
  trace_opcode(p,  MATCH_SRLIW, insn);
  return npc;
}

reg_t rv64_srliw(processor_t* p, insn_t insn, reg_t pc)
{
  int xlen = 64;
  reg_t npc = sext_xlen(pc + insn_length( MATCH_SRLIW));
  #include "insns/srliw.h"
  trace_opcode(p,  MATCH_SRLIW, insn);
  return npc;
}

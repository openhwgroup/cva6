// See LICENSE for license details.

#include "insn_template.h"

reg_t rv32_amoor_w(processor_t* p, insn_t insn, reg_t pc)
{
  int xlen = 32;
  reg_t npc = sext_xlen(pc + insn_length( MATCH_AMOOR_W));
  #include "insns/amoor_w.h"
  trace_opcode(p,  MATCH_AMOOR_W, insn);
  return npc;
}

reg_t rv64_amoor_w(processor_t* p, insn_t insn, reg_t pc)
{
  int xlen = 64;
  reg_t npc = sext_xlen(pc + insn_length( MATCH_AMOOR_W));
  #include "insns/amoor_w.h"
  trace_opcode(p,  MATCH_AMOOR_W, insn);
  return npc;
}

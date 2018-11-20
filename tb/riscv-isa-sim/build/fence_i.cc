// See LICENSE for license details.

#include "insn_template.h"

reg_t rv32_fence_i(processor_t* p, insn_t insn, reg_t pc)
{
  int xlen = 32;
  reg_t npc = sext_xlen(pc + insn_length( MATCH_FENCE_I));
  #include "insns/fence_i.h"
  trace_opcode(p,  MATCH_FENCE_I, insn);
  return npc;
}

reg_t rv64_fence_i(processor_t* p, insn_t insn, reg_t pc)
{
  int xlen = 64;
  reg_t npc = sext_xlen(pc + insn_length( MATCH_FENCE_I));
  #include "insns/fence_i.h"
  trace_opcode(p,  MATCH_FENCE_I, insn);
  return npc;
}

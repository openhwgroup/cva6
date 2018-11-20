// See LICENSE for license details.

#include "insn_template.h"

reg_t rv32_fnmsub_q(processor_t* p, insn_t insn, reg_t pc)
{
  int xlen = 32;
  reg_t npc = sext_xlen(pc + insn_length( MATCH_FNMSUB_Q));
  #include "insns/fnmsub_q.h"
  trace_opcode(p,  MATCH_FNMSUB_Q, insn);
  return npc;
}

reg_t rv64_fnmsub_q(processor_t* p, insn_t insn, reg_t pc)
{
  int xlen = 64;
  reg_t npc = sext_xlen(pc + insn_length( MATCH_FNMSUB_Q));
  #include "insns/fnmsub_q.h"
  trace_opcode(p,  MATCH_FNMSUB_Q, insn);
  return npc;
}

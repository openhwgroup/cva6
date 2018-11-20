// See LICENSE for license details.

#include "insn_template.h"

reg_t rv32_fdiv_q(processor_t* p, insn_t insn, reg_t pc)
{
  int xlen = 32;
  reg_t npc = sext_xlen(pc + insn_length( MATCH_FDIV_Q));
  #include "insns/fdiv_q.h"
  trace_opcode(p,  MATCH_FDIV_Q, insn);
  return npc;
}

reg_t rv64_fdiv_q(processor_t* p, insn_t insn, reg_t pc)
{
  int xlen = 64;
  reg_t npc = sext_xlen(pc + insn_length( MATCH_FDIV_Q));
  #include "insns/fdiv_q.h"
  trace_opcode(p,  MATCH_FDIV_Q, insn);
  return npc;
}

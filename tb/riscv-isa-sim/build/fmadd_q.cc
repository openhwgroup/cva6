// See LICENSE for license details.

#include "insn_template.h"

reg_t rv32_fmadd_q(processor_t* p, insn_t insn, reg_t pc)
{
  int xlen = 32;
  reg_t npc = sext_xlen(pc + insn_length( MATCH_FMADD_Q));
  #include "insns/fmadd_q.h"
  trace_opcode(p,  MATCH_FMADD_Q, insn);
  return npc;
}

reg_t rv64_fmadd_q(processor_t* p, insn_t insn, reg_t pc)
{
  int xlen = 64;
  reg_t npc = sext_xlen(pc + insn_length( MATCH_FMADD_Q));
  #include "insns/fmadd_q.h"
  trace_opcode(p,  MATCH_FMADD_Q, insn);
  return npc;
}

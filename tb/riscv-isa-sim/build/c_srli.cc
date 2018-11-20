// See LICENSE for license details.

#include "insn_template.h"

reg_t rv32_c_srli(processor_t* p, insn_t insn, reg_t pc)
{
  int xlen = 32;
  reg_t npc = sext_xlen(pc + insn_length( MATCH_C_SRLI));
  #include "insns/c_srli.h"
  trace_opcode(p,  MATCH_C_SRLI, insn);
  return npc;
}

reg_t rv64_c_srli(processor_t* p, insn_t insn, reg_t pc)
{
  int xlen = 64;
  reg_t npc = sext_xlen(pc + insn_length( MATCH_C_SRLI));
  #include "insns/c_srli.h"
  trace_opcode(p,  MATCH_C_SRLI, insn);
  return npc;
}

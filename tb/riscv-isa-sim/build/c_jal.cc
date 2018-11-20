// See LICENSE for license details.

#include "insn_template.h"

reg_t rv32_c_jal(processor_t* p, insn_t insn, reg_t pc)
{
  int xlen = 32;
  reg_t npc = sext_xlen(pc + insn_length( MATCH_C_JAL));
  #include "insns/c_jal.h"
  trace_opcode(p,  MATCH_C_JAL, insn);
  return npc;
}

reg_t rv64_c_jal(processor_t* p, insn_t insn, reg_t pc)
{
  int xlen = 64;
  reg_t npc = sext_xlen(pc + insn_length( MATCH_C_JAL));
  #include "insns/c_jal.h"
  trace_opcode(p,  MATCH_C_JAL, insn);
  return npc;
}

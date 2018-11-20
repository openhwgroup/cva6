// See LICENSE for license details.

#include "insn_template.h"

reg_t rv32_fmsub_d(processor_t* p, insn_t insn, reg_t pc)
{
  int xlen = 32;
  reg_t npc = sext_xlen(pc + insn_length( MATCH_FMSUB_D));
  #include "insns/fmsub_d.h"
  trace_opcode(p,  MATCH_FMSUB_D, insn);
  return npc;
}

reg_t rv64_fmsub_d(processor_t* p, insn_t insn, reg_t pc)
{
  int xlen = 64;
  reg_t npc = sext_xlen(pc + insn_length( MATCH_FMSUB_D));
  #include "insns/fmsub_d.h"
  trace_opcode(p,  MATCH_FMSUB_D, insn);
  return npc;
}

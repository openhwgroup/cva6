// See LICENSE for license details.

#include "insn_template.h"

reg_t rv32_fsub_d(processor_t* p, insn_t insn, reg_t pc)
{
  int xlen = 32;
  reg_t npc = sext_xlen(pc + insn_length( MATCH_FSUB_D));
  #include "insns/fsub_d.h"
  trace_opcode(p,  MATCH_FSUB_D, insn);
  return npc;
}

reg_t rv64_fsub_d(processor_t* p, insn_t insn, reg_t pc)
{
  int xlen = 64;
  reg_t npc = sext_xlen(pc + insn_length( MATCH_FSUB_D));
  #include "insns/fsub_d.h"
  trace_opcode(p,  MATCH_FSUB_D, insn);
  return npc;
}

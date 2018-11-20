// See LICENSE for license details.

#include "insn_template.h"

reg_t rv32_c_addi(processor_t* p, insn_t insn, reg_t pc)
{
  int xlen = 32;
  reg_t npc = sext_xlen(pc + insn_length( MATCH_C_ADDI));
  #include "insns/c_addi.h"
  trace_opcode(p,  MATCH_C_ADDI, insn);
  return npc;
}

reg_t rv64_c_addi(processor_t* p, insn_t insn, reg_t pc)
{
  int xlen = 64;
  reg_t npc = sext_xlen(pc + insn_length( MATCH_C_ADDI));
  #include "insns/c_addi.h"
  trace_opcode(p,  MATCH_C_ADDI, insn);
  return npc;
}

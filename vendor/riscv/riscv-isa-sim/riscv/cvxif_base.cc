// Copyright (C) 2022 Thales DIS Design Services SAS
//
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0.
//
// Original Author: Zbigniew CHAMSKI <zbigniew.chamski@thalesgroup.com>

#define DECODE_MACRO_USAGE_LOGGED 1
#include "decode_macros.h"
#include "cvxif.h"
#include "trap.h"
#include <cstdlib>

// Virtual base class of CVXIF.

// Return true if writeback is required.
// Be on the safe side, disable writeback.
bool cvxif_extn_t::do_writeback_p(cvxif_insn_t insn)
{
  return false;
}

// Define custom insns templates.
// The insn-level wrapper is 'c##n' (default implementation,
// writeback disabled), the default implementation
// is 'custom##n': illegal instruction, return 0.
// The writeback controller 'cvxif_extn_t::do_writeback_p'
// is in charge of determining if writeback is required or not.
// Expected instruction encoding is 4 bytes.
#define customX(n) \
static reg_t c##n(processor_t* p, insn_t insn, reg_t pc) \
  { \
    cvxif_extn_t* cvxif = static_cast<cvxif_extn_t*>(p->get_extension()); \
    cvxif_insn_t custom_insn; \
    custom_insn.i = insn; \
    reg_t xd = cvxif->custom##n(custom_insn); \
    if (cvxif->do_writeback_p(custom_insn)) \
      WRITE_RD(xd); \
    return pc+4; \
  } \
  \
  reg_t cvxif_extn_t::custom##n(cvxif_insn_t insn) \
  { \
    illegal_instruction(); \
    return -1; \
  }

customX(0)
customX(1)
customX(2)
customX(3)

std::vector<insn_desc_t> cvxif_extn_t::get_instructions()
{
  std::vector<insn_desc_t> insns;
  insns.push_back((insn_desc_t){0x0b, 0x7f, &::illegal_instruction, c0});
  insns.push_back((insn_desc_t){0x2b, 0x7f, &::illegal_instruction, c1});
  insns.push_back((insn_desc_t){0x5b, 0x7f, &::illegal_instruction, c2});
  insns.push_back((insn_desc_t){0x7b, 0x7f, &::illegal_instruction, c3});
  return insns;
}

std::vector<disasm_insn_t*> cvxif_extn_t::get_disasms()
{
  std::vector<disasm_insn_t*> insns;
  return insns;
}

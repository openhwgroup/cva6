// Copyright 2026 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// Description: Self-contained RV32/RV64 disassembler used by the CVA6
//              instruction tracer. It decodes raw encodings and spells them in
//              one of two styles: the column layout of the legacy instr_tracer,
//              or the mnemonics and operands spike-dasm prints.

#ifndef CVA6TB_TRACER_RV_DISASM_H
#define CVA6TB_TRACER_RV_DISASM_H

#include <cstdint>
#include <string>

namespace cva6tb_tracer {

// Which register file an operand refers to.
enum reg_kind_t : uint8_t { REG_NONE = 0, REG_GPR = 1, REG_FPR = 2 };

struct reg_ref_t {
  reg_kind_t kind;
  uint8_t    idx;
};

// How the text of an instruction is spelled.
enum rv_style_t : uint8_t {
  RV_STYLE_LEGACY = 0,  // the legacy instr_tracer's columns, mnemonics and operand order
  RV_STYLE_SPIKE = 1,   // what spike-dasm prints: its pseudo-instructions, ABI names, pc offsets
};

// Everything the tracer needs to know about one instruction, derived purely
// from its encoding.
struct decoded_t {
  std::string text;      // mnemonic + operands, in the requested style
  // spike style only: `text` split into its two halves, and the branch or jump
  // target, which is always the last operand, so that a format can print it as
  // an absolute address
  std::string mnemonic;
  std::string operands;
  bool        has_target;
  int64_t     target_offset;  // from the pc of the instruction
  size_t      target_pos;     // where the target starts in `operands`
  reg_ref_t   dst;       // destination register (kind == REG_NONE if none)
  reg_ref_t   src[3];    // source registers, in the order the legacy tracer printed them
  unsigned    n_src;
  bool        is_load;
  bool        is_store;
  bool        is_amo;
  bool        is_csr;
  bool        is_branch;  // conditional branch
  bool        is_jump;    // unconditional jump, direct or register
  uint16_t    csr_addr;  // valid if is_csr
  unsigned    mem_bytes; // access width in bytes, valid if is_load/is_store/is_amo
};

// Optional extensions whose encodings collide with something else, so the
// decoder cannot tell them apart on its own.
enum rv_ext_t : unsigned {
  RV_EXT_ZCMT = 1u << 0,  // cm.jt / cm.jalt, which share the c.fsdsp encoding
};

// Decode a single instruction. Compressed instructions are passed in the low
// 16 bits with the upper bits zeroed (as RVFI reports them). `xlen` is 32 or 64
// and only affects encodings that differ between RV32 and RV64 (c.jal/c.addiw,
// c.flw/c.ld, c.fsw/c.sd, c.flwsp/c.ldsp, c.fswsp/c.sdsp). `ext` is a mask of
// rv_ext_t; Zcb needs no flag because it only uses otherwise reserved encodings.
// The register, memory and class fields do not depend on `style`.
decoded_t rv_decode(uint32_t insn, int xlen, unsigned ext = 0,
                    rv_style_t style = RV_STYLE_LEGACY);

// Absolute address of the branch or jump target of `d`, an instruction at `pc`.
uint64_t rv_target_address(const decoded_t &d, uint64_t pc, int xlen);

// ABI register names ("ra", "sp", "a0", "ft0", ...).
const char *rv_gpr_name(unsigned idx);
const char *rv_fpr_name(unsigned idx);

// CSR name, or "0x___" for addresses we do not know.
std::string rv_csr_name(uint16_t addr);

// Sets `name` and returns true for a CSR address we know the name of.
bool rv_csr_lookup(uint16_t addr, std::string *name);

// Architectural trap cause as a string, e.g. "ILLEGAL_INSTR". `cause` is the
// raw mcause/scause value: bit XLEN-1 set marks an interrupt.
std::string rv_cause_name(uint64_t cause, int xlen);

}  // namespace cva6tb_tracer

#endif  // CVA6TB_TRACER_RV_DISASM_H

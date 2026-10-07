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
// Description: RV32/RV64 IMAFDC + Zicsr disassembler for the CVA6 tracer.
//              The operand layout of every mnemonic mirrors the legacy
//              common/local/util/instr_trace_item.svh so that the produced logs
//              line up column for column with the old trace_hart_*.log files.

#include "rv_disasm.h"

#include <cstdarg>
#include <cstdio>

namespace cva6tb_tracer {

// ---------------------------------------------------------------------------
// small helpers
// ---------------------------------------------------------------------------

static std::string fmt(const char *f, ...) {
  char buf[256];
  va_list ap;
  va_start(ap, f);
  int n = vsnprintf(buf, sizeof(buf), f, ap);
  va_end(ap);
  if (n < 0) return std::string();
  if ((size_t)n < sizeof(buf)) return std::string(buf, n);
  std::string big((size_t)n, '\0');
  va_start(ap, f);
  vsnprintf(&big[0], (size_t)n + 1, f, ap);
  va_end(ap);
  return big;
}

static inline uint32_t bits(uint32_t v, int hi, int lo) {
  return (v >> lo) & ((1u << (hi - lo + 1)) - 1);
}

static inline int64_t sext(uint64_t v, unsigned n) {
  const uint64_t m = 1ull << (n - 1);
  return (int64_t)((v ^ m) - m);
}

const char *rv_gpr_name(unsigned idx) {
  static const char *const n[32] = {"x0", "ra", "sp", "gp", "tp",  "t0",  "t1", "t2",
                                    "s0", "s1", "a0", "a1", "a2",  "a3",  "a4", "a5",
                                    "a6", "a7", "s2", "s3", "s4",  "s5",  "s6", "s7",
                                    "s8", "s9", "s10", "s11", "t3", "t4", "t5", "t6"};
  return n[idx & 31];
}

const char *rv_fpr_name(unsigned idx) {
  static const char *const n[32] = {"ft0", "ft1", "ft2",  "ft3",  "ft4", "ft5", "ft6",  "ft7",
                                    "fs0", "fs1", "fa0",  "fa1",  "fa2", "fa3", "fa4",  "fa5",
                                    "fa6", "fa7", "fs2",  "fs3",  "fs4", "fs5", "fs6",  "fs7",
                                    "fs8", "fs9", "fs10", "fs11", "ft8", "ft9", "ft10", "ft11"};
  return n[idx & 31];
}

// Every CSR CVA6 implements, named as spike names them, plus the CLIC and
// cva6 custom registers spike has no name for.
static const char *csr_fixed_name(uint16_t addr) {
  switch (addr) {
    // user floating point, vector and table jump
    case 0x001: return "fflags";
    case 0x002: return "frm";
    case 0x003: return "fcsr";
    case 0x008: return "vstart";
    case 0x009: return "vxsat";
    case 0x00A: return "vxrm";
    case 0x00F: return "vcsr";
    case 0x017: return "jvt";
    case 0xC20: return "vl";
    case 0xC21: return "vtype";
    case 0xC22: return "vlenb";
    // user counters
    case 0xC00: return "cycle";
    case 0xC01: return "time";
    case 0xC02: return "instret";
    case 0xC80: return "cycleh";
    case 0xC81: return "timeh";
    case 0xC82: return "instreth";
    // supervisor
    case 0x100: return "sstatus";
    case 0x104: return "sie";
    case 0x105: return "stvec";
    case 0x106: return "scounteren";
    case 0x10A: return "senvcfg";
    case 0x140: return "sscratch";
    case 0x141: return "sepc";
    case 0x142: return "scause";
    case 0x143: return "stval";
    case 0x144: return "sip";
    case 0x180: return "satp";
    // machine information
    case 0xF11: return "mvendorid";
    case 0xF12: return "marchid";
    case 0xF13: return "mimpid";
    case 0xF14: return "mhartid";
    case 0xF15: return "mconfigptr";
    // machine trap setup
    case 0x300: return "mstatus";
    case 0x301: return "misa";
    case 0x302: return "medeleg";
    case 0x303: return "mideleg";
    case 0x304: return "mie";
    case 0x305: return "mtvec";
    case 0x306: return "mcounteren";
    case 0x30A: return "menvcfg";
    case 0x310: return "mstatush";
    case 0x31A: return "menvcfgh";
    case 0x320: return "mcountinhibit";
    // machine trap handling
    case 0x340: return "mscratch";
    case 0x341: return "mepc";
    case 0x342: return "mcause";
    case 0x343: return "mtval";
    case 0x344: return "mip";
    case 0x34A: return "mtinst";
    case 0x34B: return "mtval2";
    // machine counters
    case 0xB00: return "mcycle";
    case 0xB02: return "minstret";
    case 0xB80: return "mcycleh";
    case 0xB82: return "minstreth";
    // debug / trace
    case 0x7A0: return "tselect";
    case 0x7A1: return "tdata1";
    case 0x7A2: return "tdata2";
    case 0x7A3: return "tdata3";
    case 0x7A4: return "tinfo";
    case 0x7A8: return "mcontext";
    case 0x5A8: return "scontext";
    case 0x6A8: return "hcontext";
    case 0x7B0: return "dcsr";
    case 0x7B1: return "dpc";
    case 0x7B2: return "dscratch0";
    case 0x7B3: return "dscratch1";
    // hypervisor / virtual supervisor
    case 0x200: return "vsstatus";
    case 0x204: return "vsie";
    case 0x205: return "vstvec";
    case 0x240: return "vsscratch";
    case 0x241: return "vsepc";
    case 0x242: return "vscause";
    case 0x243: return "vstval";
    case 0x244: return "vsip";
    case 0x280: return "vsatp";
    case 0x600: return "hstatus";
    case 0x602: return "hedeleg";
    case 0x603: return "hideleg";
    case 0x604: return "hie";
    case 0x605: return "htimedelta";
    case 0x606: return "hcounteren";
    case 0x607: return "hgeie";
    case 0x60A: return "henvcfg";
    case 0x615: return "htimedeltah";
    case 0x61A: return "henvcfgh";
    case 0x643: return "htval";
    case 0x644: return "hip";
    case 0x645: return "hvip";
    case 0x64A: return "htinst";
    case 0x680: return "hgatp";
    case 0xE12: return "hgeip";
    // CLIC
    case 0x307: return "mtvt";
    case 0x345: return "mnxti";
    case 0x347: return "mintthresh";
    case 0x348: return "mscratchcsw";
    case 0x349: return "mscratchcswl";
    case 0x346: return "mintstatus";
    case 0x107: return "stvt";
    case 0x145: return "snxti";
    case 0x147: return "sintthresh";
    case 0x148: return "sscratchcsw";
    case 0x149: return "sscratchcswl";
    case 0x207: return "vstvt";
    case 0x247: return "vsintthresh";
    case 0xDB1: return "sintstatus";
    // cva6 custom
    case 0x7C0: return "icache";
    case 0x7C1: return "dcache";
    case 0x7C2: return "acc_cons";
    default: return nullptr;
  }
}

bool rv_csr_lookup(uint16_t addr, std::string *name) {
  if (const char *n = csr_fixed_name(addr)) *name = n;
  else if (addr >= 0x3A0 && addr <= 0x3AF) *name = fmt("pmpcfg%d", addr - 0x3A0);
  else if (addr >= 0x3B0 && addr <= 0x3EF) *name = fmt("pmpaddr%d", addr - 0x3B0);
  else if (addr >= 0xB03 && addr <= 0xB1F) *name = fmt("mhpmcounter%d", addr - 0xB00);
  else if (addr >= 0xB83 && addr <= 0xB9F) *name = fmt("mhpmcounter%dh", addr - 0xB80);
  else if (addr >= 0x323 && addr <= 0x33F) *name = fmt("mhpmevent%d", addr - 0x320);
  else if (addr >= 0xC03 && addr <= 0xC1F) *name = fmt("hpmcounter%d", addr - 0xC00);
  else if (addr >= 0xC83 && addr <= 0xC9F) *name = fmt("hpmcounter%dh", addr - 0xC80);
  else return false;
  return true;
}

std::string rv_csr_name(uint16_t addr) {
  std::string name;
  return rv_csr_lookup(addr, &name) ? name : fmt("0x%03x", addr);
}

uint64_t rv_target_address(const decoded_t &d, uint64_t pc, int xlen) {
  const uint64_t t = pc + (uint64_t)d.target_offset;
  return xlen == 32 ? (t & 0xFFFFFFFFull) : t;
}

std::string rv_cause_name(uint64_t cause, int xlen) {
  const uint64_t irq_bit = 1ull << ((xlen == 32 ? 32 : 64) - 1);
  const bool is_irq = (cause & irq_bit) != 0;
  // In CLIC mode the cause register packs mpil/mpp/mpie above the exception
  // code, which occupies the low 12 bits.
  const uint64_t code = cause & 0xFFFull;
  if (is_irq) {
    switch (code) {
      case 1:  return "S_SW_INTERRUPT";
      case 3:  return "M_SW_INTERRUPT";
      case 5:  return "S_TIMER_INTERRUPT";
      case 7:  return "M_TIMER_INTERRUPT";
      case 9:  return "S_EXT_INTERRUPT";
      case 11: return "M_EXT_INTERRUPT";
      case 2:  return "VS_SW_INTERRUPT";
      case 6:  return "VS_TIMER_INTERRUPT";
      case 10: return "VS_EXT_INTERRUPT";
      case 12: return "S_GUEST_EXT_INTERRUPT";
      default: return fmt("INTERRUPT_%llu", (unsigned long long)code);
    }
  }
  switch (code) {
    case 0:  return "INSTR_ADDR_MISALIGNED";
    case 1:  return "INSTR_ACCESS_FAULT";
    case 2:  return "ILLEGAL_INSTR";
    case 3:  return "BREAKPOINT";
    case 4:  return "LD_ADDR_MISALIGNED";
    case 5:  return "LD_ACCESS_FAULT";
    case 6:  return "ST_ADDR_MISALIGNED";
    case 7:  return "ST_ACCESS_FAULT";
    case 8:  return "ENV_CALL_UMODE";
    case 9:  return "ENV_CALL_SMODE";
    case 10: return "ENV_CALL_VSMODE";
    case 11: return "ENV_CALL_MMODE";
    case 12: return "INSTR_PAGE_FAULT";
    case 13: return "LOAD_PAGE_FAULT";
    case 15: return "STORE_PAGE_FAULT";
    case 20: return "INSTR_GUEST_PAGE_FAULT";
    case 21: return "LOAD_GUEST_PAGE_FAULT";
    case 22: return "VIRTUAL_INSTR";
    case 23: return "STORE_GUEST_PAGE_FAULT";
    default: return fmt("EXCEPTION_%llu", (unsigned long long)code);
  }
}

// ---------------------------------------------------------------------------
// operand formatting, mirroring the legacy instr_trace_item print* functions
// ---------------------------------------------------------------------------

static std::string pc_expr(int64_t imm) {
  // the legacy tracer renders a non-positive offset as "pc - N"
  if (imm > 0) return fmt("pc + %lld", (long long)imm);
  return fmt("pc - %lld", (long long)(-imm));
}

static const char *fp_fmt_str(uint32_t f) {
  static const char *const s[4] = {"s", "d", "h", "b"};
  return s[f & 3];
}

static const char *fmv_fmt_str(uint32_t f) {
  static const char *const s[4] = {"w", "d", "h", "b"};
  return s[f & 3];
}

static const char *int_fmt_str(uint32_t f) {
  static const char *const s[4] = {"w", "wu", "l", "lu"};
  return s[f & 3];
}

static const char *fp_rm_str(uint32_t rm) {
  switch (rm) {
    case 0: return "rne";
    case 1: return "rtz";
    case 2: return "rdn";
    case 3: return "rup";
    case 4: return "rmm";
    case 7: return "dyn";
    default: return "rm?";
  }
}

static inline void add_dst(decoded_t &d, reg_kind_t k, unsigned idx) {
  d.dst.kind = k;
  d.dst.idx = (uint8_t)idx;
}

static inline void add_src(decoded_t &d, reg_kind_t k, unsigned idx) {
  if (d.n_src < 3) {
    d.src[d.n_src].kind = k;
    d.src[d.n_src].idx = (uint8_t)idx;
    d.n_src++;
  }
}

static inline const char *reg_name(reg_kind_t k, unsigned idx) {
  return k == REG_FPR ? rv_fpr_name(idx) : rv_gpr_name(idx);
}

static void p_mnemonic(decoded_t &d, const char *mn) { d.text = mn; }

static void p_r(decoded_t &d, const char *mn, unsigned rd, unsigned rs1, unsigned rs2) {
  add_dst(d, REG_GPR, rd);
  add_src(d, REG_GPR, rs1);
  add_src(d, REG_GPR, rs2);
  d.text = fmt("%-12s %4s, %s, %s", mn, rv_gpr_name(rd), rv_gpr_name(rs1), rv_gpr_name(rs2));
}

static void p_i(decoded_t &d, const char *mn, unsigned rd, unsigned rs1, int64_t imm) {
  add_dst(d, REG_GPR, rd);
  add_src(d, REG_GPR, rs1);
  if (rs1 == 0)
    d.text = fmt("%-12s %4s, %lld", mn, rv_gpr_name(rd), (long long)imm);
  else
    d.text = fmt("%-12s %4s, %s, %lld", mn, rv_gpr_name(rd), rv_gpr_name(rs1), (long long)imm);
}

static void p_iu(decoded_t &d, const char *mn, unsigned rd, unsigned rs1, uint64_t imm) {
  add_dst(d, REG_GPR, rd);
  add_src(d, REG_GPR, rs1);
  d.text = fmt("%-12s %4s, %s, 0x%llx", mn, rv_gpr_name(rd), rv_gpr_name(rs1),
               (unsigned long long)imm);
}

static void p_sb(decoded_t &d, const char *mn, unsigned rs1, unsigned rs2, int64_t imm) {
  add_src(d, REG_GPR, rs1);
  add_src(d, REG_GPR, rs2);
  if (rs2 == 0)
    d.text = fmt("%-12s %4s, %s", mn, rv_gpr_name(rs1), pc_expr(imm).c_str());
  else
    d.text = fmt("%-12s %4s, %s, %s", mn, rv_gpr_name(rs1), rv_gpr_name(rs2),
                 pc_expr(imm).c_str());
}

static void p_u(decoded_t &d, const char *mn, unsigned rd, uint32_t imm_field) {
  add_dst(d, REG_GPR, rd);
  d.text = fmt("%-12s %4s, 0x%x", mn, rv_gpr_name(rd), imm_field);
}

static void p_uj(decoded_t &d, const char *mn, unsigned rd, int64_t imm) {
  add_dst(d, REG_GPR, rd);
  if (rd == 0)
    d.text = fmt("%-12s   %s", mn, pc_expr(imm).c_str());
  else
    d.text = fmt("%-12s %4s, %s", mn, rv_gpr_name(rd), pc_expr(imm).c_str());
}

static void p_load(decoded_t &d, const char *mn, reg_kind_t dk, unsigned rd, unsigned rs1,
                   int64_t imm, unsigned bytes) {
  add_dst(d, dk, rd);
  add_src(d, REG_GPR, rs1);
  d.is_load = true;
  d.mem_bytes = bytes;
  d.text = fmt("%-12s %4s, %lld(%s)", mn, reg_name(dk, rd), (long long)imm, rv_gpr_name(rs1));
}

static void p_store(decoded_t &d, const char *mn, reg_kind_t sk, unsigned rs2, unsigned rs1,
                    int64_t imm, unsigned bytes) {
  add_src(d, sk, rs2);
  add_src(d, REG_GPR, rs1);
  d.is_store = true;
  d.mem_bytes = bytes;
  d.text = fmt("%-12s %4s, %lld(%s)", mn, reg_name(sk, rs2), (long long)imm, rv_gpr_name(rs1));
}

static void p_csr(decoded_t &d, const char *mn, unsigned rd, unsigned rs1, uint16_t csr,
                  bool immediate_form) {
  add_dst(d, REG_GPR, rd);
  d.is_csr = true;
  d.csr_addr = csr;
  const std::string cn = rv_csr_name(csr);
  if (!immediate_form) {
    add_src(d, REG_GPR, rs1);
    if (rd != 0 && rs1 != 0)
      d.text = fmt("%-12s %4s, %s, %s", mn, rv_gpr_name(rd), rv_gpr_name(rs1), cn.c_str());
    else if (rd == 0)
      d.text = fmt("%-12s %4s, %s", mn, rv_gpr_name(rs1), cn.c_str());
    else
      d.text = fmt("%-12s %4s, %s", mn, rv_gpr_name(rd), cn.c_str());
  } else {
    if (rd != 0 && rs1 != 0)
      d.text = fmt("%-12s %4s, %d, %s", mn, rv_gpr_name(rd), rs1, cn.c_str());
    else if (rd == 0)
      d.text = fmt("%-14s %2d, %s", mn, rs1, cn.c_str());
    else
      d.text = fmt("%-12s %4s, %s", mn, rv_gpr_name(rd), cn.c_str());
  }
}

// single source operand, e.g. the Zbb count and sign extend instructions
static void p_r1(decoded_t &d, const char *mn, unsigned rd, unsigned rs1) {
  add_dst(d, REG_GPR, rd);
  add_src(d, REG_GPR, rs1);
  d.text = fmt("%-12s %4s, %s", mn, rv_gpr_name(rd), rv_gpr_name(rs1));
}

// hypervisor load: the address is a bare register, there is no offset field
static void p_hload(decoded_t &d, const char *mn, unsigned rd, unsigned rs1, unsigned bytes) {
  add_dst(d, REG_GPR, rd);
  add_src(d, REG_GPR, rs1);
  d.is_load = true;
  d.mem_bytes = bytes;
  d.text = fmt("%-12s %4s, (%s)", mn, rv_gpr_name(rd), rv_gpr_name(rs1));
}

static void p_hstore(decoded_t &d, const char *mn, unsigned rs2, unsigned rs1, unsigned bytes) {
  add_src(d, REG_GPR, rs2);
  add_src(d, REG_GPR, rs1);
  d.is_store = true;
  d.mem_bytes = bytes;
  d.text = fmt("%-12s %4s, (%s)", mn, rv_gpr_name(rs2), rv_gpr_name(rs1));
}

// hfence.vvma / hfence.gvma, which take an address and an id
static void p_hfence(decoded_t &d, const char *mn, unsigned rs1, unsigned rs2) {
  add_src(d, REG_GPR, rs1);
  add_src(d, REG_GPR, rs2);
  d.text = fmt("%-12s %4s, %s", mn, rv_gpr_name(rs1), rv_gpr_name(rs2));
}

// cache block operations, whose only operand is the base register
static void p_cbo(decoded_t &d, const char *mn, unsigned rs1, unsigned bytes) {
  add_src(d, REG_GPR, rs1);
  d.mem_bytes = bytes;
  d.text = fmt("%-12s (%s)", mn, rv_gpr_name(rs1));
}

static void p_amo(decoded_t &d, const char *mn, unsigned rd, unsigned rs2, unsigned rs1,
                  unsigned bytes) {
  add_dst(d, REG_GPR, rd);
  add_src(d, REG_GPR, rs2);
  add_src(d, REG_GPR, rs1);
  d.is_amo = true;
  d.mem_bytes = bytes;
  d.text = fmt("%-16s %s, %s,(%s)", mn, rv_gpr_name(rd), rv_gpr_name(rs2), rv_gpr_name(rs1));
}

// floating point helpers -----------------------------------------------------

static void p_fp1(decoded_t &d, const char *base, uint32_t insn, reg_kind_t dk, reg_kind_t s1k,
                  bool use_rnd) {
  const unsigned rd = bits(insn, 11, 7), rs1 = bits(insn, 19, 15), rm = bits(insn, 14, 12);
  add_dst(d, dk, rd);
  add_src(d, s1k, rs1);
  const std::string mn = fmt("%s.%s", base, fp_fmt_str(bits(insn, 26, 25)));
  if (use_rnd && rm != 7)
    d.text = fmt("%-12s %4s, %s, %s", mn.c_str(), reg_name(dk, rd), reg_name(s1k, rs1),
                 fp_rm_str(rm));
  else
    d.text = fmt("%-12s %4s, %s", mn.c_str(), reg_name(dk, rd), reg_name(s1k, rs1));
}

static void p_fp2(decoded_t &d, const char *base, uint32_t insn, reg_kind_t dk, reg_kind_t s1k,
                  reg_kind_t s2k, bool use_rnd) {
  const unsigned rd = bits(insn, 11, 7), rs1 = bits(insn, 19, 15), rs2 = bits(insn, 24, 20);
  const unsigned rm = bits(insn, 14, 12);
  add_dst(d, dk, rd);
  add_src(d, s1k, rs1);
  add_src(d, s2k, rs2);
  const std::string mn = fmt("%s.%s", base, fp_fmt_str(bits(insn, 26, 25)));
  if (use_rnd && rm != 7)
    d.text = fmt("%-12s %4s, %s, %s, %s", mn.c_str(), reg_name(dk, rd), reg_name(s1k, rs1),
                 reg_name(s2k, rs2), fp_rm_str(rm));
  else
    d.text = fmt("%-12s %4s, %s, %s", mn.c_str(), reg_name(dk, rd), reg_name(s1k, rs1),
                 reg_name(s2k, rs2));
}

static void p_fp_r4(decoded_t &d, const char *base, uint32_t insn) {
  const unsigned rd = bits(insn, 11, 7), rs1 = bits(insn, 19, 15);
  const unsigned rs2 = bits(insn, 24, 20), rs3 = bits(insn, 31, 27);
  add_dst(d, REG_FPR, rd);
  add_src(d, REG_FPR, rs1);
  add_src(d, REG_FPR, rs2);
  add_src(d, REG_FPR, rs3);
  const std::string mn = fmt("%s.%s", base, fp_fmt_str(bits(insn, 26, 25)));
  d.text = fmt("%-12s %4s, %s, %s, %s, %s", mn.c_str(), rv_fpr_name(rd), rv_fpr_name(rs1),
               rv_fpr_name(rs2), rv_fpr_name(rs3), fp_rm_str(bits(insn, 14, 12)));
}

static void decode_op_fp(decoded_t &d, uint32_t insn) {
  const unsigned f5 = bits(insn, 31, 27), rm = bits(insn, 14, 12);
  const unsigned rd = bits(insn, 11, 7), rs1 = bits(insn, 19, 15);
  const unsigned f = bits(insn, 26, 25), f2 = bits(insn, 21, 20);

  switch (f5) {
    case 0x00: p_fp2(d, "fadd", insn, REG_FPR, REG_FPR, REG_FPR, true); return;
    case 0x01: p_fp2(d, "fsub", insn, REG_FPR, REG_FPR, REG_FPR, true); return;
    case 0x02: p_fp2(d, "fmul", insn, REG_FPR, REG_FPR, REG_FPR, true); return;
    case 0x03: p_fp2(d, "fdiv", insn, REG_FPR, REG_FPR, REG_FPR, true); return;
    case 0x0B: p_fp1(d, "fsqrt", insn, REG_FPR, REG_FPR, true); return;
    case 0x04:
      p_fp2(d, rm == 0 ? "fsgnj" : rm == 1 ? "fsgnjn" : "fsgnjx", insn, REG_FPR, REG_FPR,
            REG_FPR, false);
      return;
    case 0x05:
      p_fp2(d, rm == 0 ? "fmin" : "fmax", insn, REG_FPR, REG_FPR, REG_FPR, false);
      return;
    case 0x14:
      p_fp2(d, rm == 0 ? "fle" : rm == 1 ? "flt" : "feq", insn, REG_GPR, REG_FPR, REG_FPR,
            false);
      return;
    case 0x08:  // fcvt.<fmt>.<fmt>
      add_dst(d, REG_FPR, rd);
      add_src(d, REG_FPR, rs1);
      d.text = fmt("%-12s %4s, %s, %s", fmt("fcvt.%s.%s", fp_fmt_str(f), fp_fmt_str(f2)).c_str(),
                   rv_fpr_name(rd), rv_fpr_name(rs1), fp_rm_str(rm));
      return;
    case 0x18:  // fcvt.<int>.<fmt>
      add_dst(d, REG_GPR, rd);
      add_src(d, REG_FPR, rs1);
      d.text = fmt("%-12s %4s, %s, %s", fmt("fcvt.%s.%s", int_fmt_str(f2), fp_fmt_str(f)).c_str(),
                   rv_gpr_name(rd), rv_fpr_name(rs1), fp_rm_str(rm));
      return;
    case 0x1A:  // fcvt.<fmt>.<int>
      add_dst(d, REG_FPR, rd);
      add_src(d, REG_GPR, rs1);
      d.text = fmt("%-12s %4s, %s, %s", fmt("fcvt.%s.%s", fp_fmt_str(f), int_fmt_str(f2)).c_str(),
                   rv_fpr_name(rd), rv_gpr_name(rs1), fp_rm_str(rm));
      return;
    case 0x1C:
      if (rm == 0) {
        add_dst(d, REG_GPR, rd);
        add_src(d, REG_FPR, rs1);
        d.text = fmt("%-12s %4s, %s", fmt("fmv.x.%s", fmv_fmt_str(f)).c_str(), rv_gpr_name(rd),
                     rv_fpr_name(rs1));
      } else {
        p_fp1(d, "fclass", insn, REG_GPR, REG_FPR, false);
      }
      return;
    case 0x1E:
      add_dst(d, REG_FPR, rd);
      add_src(d, REG_GPR, rs1);
      d.text = fmt("%-12s %4s, %s", fmt("fmv.%s.x", fmv_fmt_str(f)).c_str(), rv_fpr_name(rd),
                   rv_gpr_name(rs1));
      return;
    default: p_mnemonic(d, "INVALID"); return;
  }
}

// ---------------------------------------------------------------------------
// uncompressed instructions
// ---------------------------------------------------------------------------

static void decode_32(decoded_t &d, uint32_t insn, int xlen) {
  const unsigned opcode = bits(insn, 6, 0);
  const unsigned rd = bits(insn, 11, 7);
  const unsigned rs1 = bits(insn, 19, 15);
  const unsigned rs2 = bits(insn, 24, 20);
  const unsigned f3 = bits(insn, 14, 12);
  const unsigned f7 = bits(insn, 31, 25);
  const int64_t imm_i = sext(bits(insn, 31, 20), 12);
  const int64_t imm_s = sext((bits(insn, 31, 25) << 5) | bits(insn, 11, 7), 12);
  const int64_t imm_b = sext((bits(insn, 31, 31) << 12) | (bits(insn, 7, 7) << 11) |
                                 (bits(insn, 30, 25) << 5) | (bits(insn, 11, 8) << 1),
                             13);
  const int64_t imm_j = sext((bits(insn, 31, 31) << 20) | (bits(insn, 19, 12) << 12) |
                                 (bits(insn, 20, 20) << 11) | (bits(insn, 30, 21) << 1),
                             21);

  if (insn == 0x00000013u) { p_mnemonic(d, "nop"); return; }

  switch (opcode) {
    case 0x37: p_u(d, "lui", rd, bits(insn, 31, 12)); return;
    case 0x17: p_u(d, "auipc", rd, bits(insn, 31, 12)); return;

    case 0x6F:  // jal
      d.is_jump = true;
      if (rd == 0) p_uj(d, "j", rd, imm_j);
      else p_i(d, "jal", rd, 0, imm_j);
      return;

    case 0x67:  // jalr
      if (f3 != 0) { p_mnemonic(d, "INVALID"); return; }
      d.is_jump = true;
      if (rd == 0 && (rs1 == 1 || rs1 == 5)) { p_mnemonic(d, "ret"); add_src(d, REG_GPR, rs1); return; }
      p_i(d, "jalr", rd, rs1, imm_i);
      return;

    case 0x63:  // branch
      d.is_branch = true;
      switch (f3) {
        case 0: p_sb(d, rs2 == 0 ? "beqz" : "beq", rs1, rs2, imm_b); return;
        case 1: p_sb(d, rs2 == 0 ? "bnez" : "bne", rs1, rs2, imm_b); return;
        case 4: p_sb(d, rs2 == 0 ? "bltz" : "blt", rs1, rs2, imm_b); return;
        case 5: p_sb(d, rs2 == 0 ? "bgez" : "bge", rs1, rs2, imm_b); return;
        case 6: p_sb(d, "bltu", rs1, rs2, imm_b); return;
        case 7: p_sb(d, "bgeu", rs1, rs2, imm_b); return;
        default: p_mnemonic(d, "INVALID"); return;
      }

    case 0x13: {  // op-imm
      const unsigned f6 = bits(insn, 31, 26);
      const unsigned f12 = bits(insn, 31, 20);
      const uint64_t shamt = xlen == 64 ? bits(insn, 25, 20) : bits(insn, 24, 20);
      switch (f3) {
        case 0: p_i(d, rs1 == 0 ? "li" : "addi", rd, rs1, imm_i); return;
        case 2: p_i(d, "slti", rd, rs1, imm_i); return;
        case 3: p_i(d, "sltiu", rd, rs1, imm_i); return;
        case 4: p_i(d, "xori", rd, rs1, imm_i); return;
        case 6: p_i(d, "ori", rd, rs1, imm_i); return;
        case 7: p_i(d, "andi", rd, rs1, imm_i); return;
        case 1:
          switch (f12) {  // Zbb single operand forms
            case 0x600: p_r1(d, "clz", rd, rs1); return;
            case 0x601: p_r1(d, "ctz", rd, rs1); return;
            case 0x602: p_r1(d, "cpop", rd, rs1); return;
            case 0x604: p_r1(d, "sext.b", rd, rs1); return;
            case 0x605: p_r1(d, "sext.h", rd, rs1); return;
            default: break;
          }
          switch (f6) {
            case 0x0A: p_iu(d, "bseti", rd, rs1, shamt); return;  // Zbs
            case 0x12: p_iu(d, "bclri", rd, rs1, shamt); return;
            case 0x1A: p_iu(d, "binvi", rd, rs1, shamt); return;
            default: p_iu(d, "slli", rd, rs1, shamt); return;
          }
        case 5:
          if (f12 == 0x287) { p_r1(d, "orc.b", rd, rs1); return; }            // Zbb
          if (f12 == (xlen == 64 ? 0x6B8u : 0x698u)) { p_r1(d, "rev8", rd, rs1); return; }
          switch (f6) {
            case 0x12: p_iu(d, "bexti", rd, rs1, shamt); return;  // Zbs
            case 0x18: p_iu(d, "rori", rd, rs1, shamt); return;   // Zbb
            case 0x10: p_iu(d, "srai", rd, rs1, shamt); return;
            default: p_iu(d, "srli", rd, rs1, shamt); return;
          }
        default: p_mnemonic(d, "INVALID"); return;
      }
    }

    case 0x1B:  // op-imm-32
      switch (f3) {
        case 0: p_i(d, "addiw", rd, rs1, imm_i); return;
        case 1:
          switch (bits(insn, 31, 20)) {  // Zbb word forms
            case 0x600: p_r1(d, "clzw", rd, rs1); return;
            case 0x601: p_r1(d, "ctzw", rd, rs1); return;
            case 0x602: p_r1(d, "cpopw", rd, rs1); return;
            default: break;
          }
          // Zba slli.uw takes a six bit shift amount, slliw a five bit one
          if (bits(insn, 31, 26) == 0x02) { p_iu(d, "slli.uw", rd, rs1, bits(insn, 25, 20)); return; }
          p_iu(d, "slliw", rd, rs1, bits(insn, 24, 20));
          return;
        case 5:
          if (f7 == 0x20) { p_iu(d, "sraiw", rd, rs1, bits(insn, 24, 20)); return; }
          if (f7 == 0x30) { p_iu(d, "roriw", rd, rs1, bits(insn, 24, 20)); return; }  // Zbb
          p_iu(d, "srliw", rd, rs1, bits(insn, 24, 20));
          return;
        default: p_mnemonic(d, "INVALID"); return;
      }

    case 0x33:  // op
      switch (f7) {
        case 0x00:
          switch (f3) {
            case 0: p_r(d, "add", rd, rs1, rs2); return;
            case 1: p_r(d, "sll", rd, rs1, rs2); return;
            case 2: p_r(d, "slt", rd, rs1, rs2); return;
            case 3: p_r(d, "sltu", rd, rs1, rs2); return;
            case 4: p_r(d, "xor", rd, rs1, rs2); return;
            case 5: p_r(d, "srl", rd, rs1, rs2); return;
            case 6: p_r(d, "or", rd, rs1, rs2); return;
            default: p_r(d, "and", rd, rs1, rs2); return;
          }
        case 0x01: {
          static const char *const m[8] = {"mul", "mulh", "mulhsu", "mulhu",
                                           "div", "divu", "rem",    "remu"};
          p_r(d, m[f3], rd, rs1, rs2);
          return;
        }
        case 0x20:
          switch (f3) {
            case 0: p_r(d, "sub", rd, rs1, rs2); return;
            case 4: p_r(d, "xnor", rd, rs1, rs2); return;   // Zbb
            case 5: p_r(d, "sra", rd, rs1, rs2); return;
            case 6: p_r(d, "orn", rd, rs1, rs2); return;    // Zbb
            case 7: p_r(d, "andn", rd, rs1, rs2); return;   // Zbb
            default: p_mnemonic(d, "INVALID"); return;
          }
        case 0x04:  // Zbb zext.h is the RV32 encoding, RV64 puts it in op-32
          if (f3 == 4 && rs2 == 0 && xlen == 32) { p_r1(d, "zext.h", rd, rs1); return; }
          p_mnemonic(d, "INVALID");
          return;
        case 0x05:
          switch (f3) {
            case 1: p_r(d, "clmul", rd, rs1, rs2); return;   // Zbc
            case 2: p_r(d, "clmulr", rd, rs1, rs2); return;
            case 3: p_r(d, "clmulh", rd, rs1, rs2); return;
            case 4: p_r(d, "min", rd, rs1, rs2); return;     // Zbb
            case 5: p_r(d, "minu", rd, rs1, rs2); return;
            case 6: p_r(d, "max", rd, rs1, rs2); return;
            case 7: p_r(d, "maxu", rd, rs1, rs2); return;
            default: p_mnemonic(d, "INVALID"); return;
          }
        case 0x07:  // Zicond
          if (f3 == 5) { p_r(d, "czero.eqz", rd, rs1, rs2); return; }
          if (f3 == 7) { p_r(d, "czero.nez", rd, rs1, rs2); return; }
          p_mnemonic(d, "INVALID");
          return;
        case 0x10:  // Zba
          switch (f3) {
            case 2: p_r(d, "sh1add", rd, rs1, rs2); return;
            case 4: p_r(d, "sh2add", rd, rs1, rs2); return;
            case 6: p_r(d, "sh3add", rd, rs1, rs2); return;
            default: p_mnemonic(d, "INVALID"); return;
          }
        case 0x14:  // Zbs
          if (f3 == 1) { p_r(d, "bset", rd, rs1, rs2); return; }
          p_mnemonic(d, "INVALID");
          return;
        case 0x24:  // Zbs
          if (f3 == 1) { p_r(d, "bclr", rd, rs1, rs2); return; }
          if (f3 == 5) { p_r(d, "bext", rd, rs1, rs2); return; }
          p_mnemonic(d, "INVALID");
          return;
        case 0x30:  // Zbb
          if (f3 == 1) { p_r(d, "rol", rd, rs1, rs2); return; }
          if (f3 == 5) { p_r(d, "ror", rd, rs1, rs2); return; }
          p_mnemonic(d, "INVALID");
          return;
        case 0x34:  // Zbs
          if (f3 == 1) { p_r(d, "binv", rd, rs1, rs2); return; }
          p_mnemonic(d, "INVALID");
          return;
        default: p_mnemonic(d, "INVALID"); return;
      }

    case 0x3B:  // op-32
      switch (f7) {
        case 0x00:
          switch (f3) {
            case 0: p_r(d, "addw", rd, rs1, rs2); return;
            case 1: p_r(d, "sllw", rd, rs1, rs2); return;
            case 5: p_r(d, "srlw", rd, rs1, rs2); return;
            default: p_mnemonic(d, "INVALID"); return;
          }
        case 0x01:
          switch (f3) {
            case 0: p_r(d, "mulw", rd, rs1, rs2); return;
            case 4: p_r(d, "divw", rd, rs1, rs2); return;
            case 5: p_r(d, "divuw", rd, rs1, rs2); return;
            case 6: p_r(d, "remw", rd, rs1, rs2); return;
            case 7: p_r(d, "remuw", rd, rs1, rs2); return;
            default: p_mnemonic(d, "INVALID"); return;
          }
        case 0x20:
          if (f3 == 0) { p_r(d, "subw", rd, rs1, rs2); return; }
          if (f3 == 5) { p_r(d, "sraw", rd, rs1, rs2); return; }
          p_mnemonic(d, "INVALID");
          return;
        case 0x04:
          if (f3 == 0) { p_r(d, "add.uw", rd, rs1, rs2); return; }              // Zba
          if (f3 == 4 && rs2 == 0) { p_r1(d, "zext.h", rd, rs1); return; }      // Zbb
          p_mnemonic(d, "INVALID");
          return;
        case 0x10:  // Zba
          switch (f3) {
            case 2: p_r(d, "sh1add.uw", rd, rs1, rs2); return;
            case 4: p_r(d, "sh2add.uw", rd, rs1, rs2); return;
            case 6: p_r(d, "sh3add.uw", rd, rs1, rs2); return;
            default: p_mnemonic(d, "INVALID"); return;
          }
        case 0x30:  // Zbb
          if (f3 == 1) { p_r(d, "rolw", rd, rs1, rs2); return; }
          if (f3 == 5) { p_r(d, "rorw", rd, rs1, rs2); return; }
          p_mnemonic(d, "INVALID");
          return;
        default: p_mnemonic(d, "INVALID"); return;
      }

    case 0x03:  // load
      switch (f3) {
        case 0: p_load(d, "lb", REG_GPR, rd, rs1, imm_i, 1); return;
        case 1: p_load(d, "lh", REG_GPR, rd, rs1, imm_i, 2); return;
        case 2: p_load(d, "lw", REG_GPR, rd, rs1, imm_i, 4); return;
        case 3: p_load(d, "ld", REG_GPR, rd, rs1, imm_i, 8); return;
        case 4: p_load(d, "lbu", REG_GPR, rd, rs1, imm_i, 1); return;
        case 5: p_load(d, "lhu", REG_GPR, rd, rs1, imm_i, 2); return;
        case 6: p_load(d, "lwu", REG_GPR, rd, rs1, imm_i, 4); return;
        default: p_mnemonic(d, "INVALID"); return;
      }

    case 0x07:  // load-fp
      switch (f3) {
        case 2: p_load(d, "flw", REG_FPR, rd, rs1, imm_i, 4); return;
        case 3: p_load(d, "fld", REG_FPR, rd, rs1, imm_i, 8); return;
        case 4: p_load(d, "flq", REG_FPR, rd, rs1, imm_i, 16); return;
        case 1: p_load(d, "flh", REG_FPR, rd, rs1, imm_i, 2); return;
        default: p_mnemonic(d, "INVALID"); return;
      }

    case 0x23:  // store
      switch (f3) {
        case 0: p_store(d, "sb", REG_GPR, rs2, rs1, imm_s, 1); return;
        case 1: p_store(d, "sh", REG_GPR, rs2, rs1, imm_s, 2); return;
        case 2: p_store(d, "sw", REG_GPR, rs2, rs1, imm_s, 4); return;
        case 3: p_store(d, "sd", REG_GPR, rs2, rs1, imm_s, 8); return;
        default: p_mnemonic(d, "INVALID"); return;
      }

    case 0x27:  // store-fp
      switch (f3) {
        case 2: p_store(d, "fsw", REG_FPR, rs2, rs1, imm_s, 4); return;
        case 3: p_store(d, "fsd", REG_FPR, rs2, rs1, imm_s, 8); return;
        case 4: p_store(d, "fsq", REG_FPR, rs2, rs1, imm_s, 16); return;
        case 1: p_store(d, "fsh", REG_FPR, rs2, rs1, imm_s, 2); return;
        default: p_mnemonic(d, "INVALID"); return;
      }

    case 0x2F: {  // AMO
      const unsigned f5 = bits(insn, 31, 27);
      const char *suffix = f3 == 2 ? ".w" : f3 == 3 ? ".d" : nullptr;
      if (!suffix) { p_mnemonic(d, "INVALID"); return; }
      const char *base = nullptr;
      switch (f5) {
        case 0x00: base = "amoadd"; break;
        case 0x01: base = "amoswap"; break;
        case 0x02: base = "lr"; break;
        case 0x03: base = "sc"; break;
        case 0x04: base = "amoxor"; break;
        case 0x08: base = "amoor"; break;
        case 0x0C: base = "amoand"; break;
        case 0x10: base = "amomin"; break;
        case 0x14: base = "amomax"; break;
        case 0x18: base = "amominu"; break;
        case 0x1C: base = "amomaxu"; break;
        default: p_mnemonic(d, "INVALID"); return;
      }
      p_amo(d, fmt("%s%s", base, suffix).c_str(), rd, rs2, rs1, f3 == 2 ? 4 : 8);
      return;
    }

    case 0x0F:  // misc-mem
      if (f3 == 1) { p_mnemonic(d, "fence.i"); return; }
      if (f3 == 2) {  // Zicbom / Zicboz cache block operations
        switch (bits(insn, 31, 20)) {
          case 0x000: p_cbo(d, "cbo.inval", rs1, 0); return;
          case 0x001: p_cbo(d, "cbo.clean", rs1, 0); return;
          case 0x002: p_cbo(d, "cbo.flush", rs1, 0); return;
          case 0x004: p_cbo(d, "cbo.zero", rs1, 0); return;
          default: p_mnemonic(d, "INVALID"); return;
        }
      }
      p_mnemonic(d, "fence");
      return;

    case 0x73:  // system
      switch (f3) {
        case 0:
          switch (bits(insn, 31, 20)) {
            case 0x000: p_mnemonic(d, "ecall"); return;
            case 0x001: p_mnemonic(d, "ebreak"); return;
            case 0x302: p_mnemonic(d, "mret"); return;
            case 0x102: p_mnemonic(d, "sret"); return;
            case 0x7B2: p_mnemonic(d, "dret"); return;
            case 0x105: p_mnemonic(d, "wfi"); return;
            default:
              // the legacy tracer printed sfence.vma without operands, so it is
              // left alone; the hypervisor fences have no such precedent
              if (f7 == 0x09) { p_mnemonic(d, "sfence.vma"); return; }
              if (f7 == 0x11) { p_hfence(d, "hfence.vvma", rs1, rs2); return; }
              if (f7 == 0x31) { p_hfence(d, "hfence.gvma", rs1, rs2); return; }
              p_mnemonic(d, "INVALID");
              return;
          }
        case 4:  // hypervisor loads and stores
          switch (f7) {
            case 0x30:
              if (rs2 == 0) { p_hload(d, "hlv.b", rd, rs1, 1); return; }
              if (rs2 == 1) { p_hload(d, "hlv.bu", rd, rs1, 1); return; }
              break;
            case 0x31: p_hstore(d, "hsv.b", rs2, rs1, 1); return;
            case 0x32:
              if (rs2 == 0) { p_hload(d, "hlv.h", rd, rs1, 2); return; }
              if (rs2 == 1) { p_hload(d, "hlv.hu", rd, rs1, 2); return; }
              if (rs2 == 3) { p_hload(d, "hlvx.hu", rd, rs1, 2); return; }
              break;
            case 0x33: p_hstore(d, "hsv.h", rs2, rs1, 2); return;
            case 0x34:
              if (rs2 == 0) { p_hload(d, "hlv.w", rd, rs1, 4); return; }
              if (rs2 == 1) { p_hload(d, "hlv.wu", rd, rs1, 4); return; }
              if (rs2 == 3) { p_hload(d, "hlvx.wu", rd, rs1, 4); return; }
              break;
            case 0x35: p_hstore(d, "hsv.w", rs2, rs1, 4); return;
            case 0x36:
              if (rs2 == 0) { p_hload(d, "hlv.d", rd, rs1, 8); return; }
              break;
            case 0x37: p_hstore(d, "hsv.d", rs2, rs1, 8); return;
            default: break;
          }
          p_mnemonic(d, "INVALID");
          return;
        case 1: p_csr(d, rd == 0 ? "csrw" : "csrrw", rd, rs1, (uint16_t)bits(insn, 31, 20), false); return;
        // the legacy tracer listed csrs/csrc but its casez ordering made those
        // patterns unreachable, so they never appeared; they are restored here
        case 2:
          p_csr(d, rs1 == 0 ? "csrr" : (rd == 0 ? "csrs" : "csrrs"), rd, rs1,
                (uint16_t)bits(insn, 31, 20), false);
          return;
        case 3:
          p_csr(d, rd == 0 ? "csrc" : "csrrc", rd, rs1, (uint16_t)bits(insn, 31, 20), false);
          return;
        case 5: p_csr(d, rd == 0 ? "csrwi" : "csrrwi", rd, rs1, (uint16_t)bits(insn, 31, 20), true); return;
        case 6: p_csr(d, rd == 0 ? "csrsi" : "csrrsi", rd, rs1, (uint16_t)bits(insn, 31, 20), true); return;
        case 7: p_csr(d, rd == 0 ? "csrci" : "csrrci", rd, rs1, (uint16_t)bits(insn, 31, 20), true); return;
        default: p_mnemonic(d, "INVALID"); return;
      }

    case 0x43: p_fp_r4(d, "fmadd", insn); return;
    case 0x47: p_fp_r4(d, "fmsub", insn); return;
    case 0x4B: p_fp_r4(d, "fnmsub", insn); return;
    case 0x4F: p_fp_r4(d, "fnmadd", insn); return;
    case 0x53: decode_op_fp(d, insn); return;

    default: p_mnemonic(d, "INVALID"); return;
  }
}

// ---------------------------------------------------------------------------
// compressed instructions
//
// The mnemonic is the compressed one ("c.addi"), while the operands are those
// of the expanded instruction -- this is what the legacy tracer printed, since
// it matched on the compressed encoding but took registers and immediates from
// the decompressed scoreboard entry.
// ---------------------------------------------------------------------------

static void decode_16(decoded_t &d, uint32_t insn, int xlen, unsigned ext) {
  const unsigned op = bits(insn, 1, 0);
  const unsigned f3 = bits(insn, 15, 13);
  const unsigned rd = bits(insn, 11, 7);    // CI / CR destination
  const unsigned rs2 = bits(insn, 6, 2);    // CR source
  const unsigned rdp = 8 + bits(insn, 4, 2);   // CL/CS/CIW destination (rd')
  const unsigned rs1p = 8 + bits(insn, 9, 7);  // CL/CS/CB base (rs1')
  const unsigned rs2p = 8 + bits(insn, 4, 2);  // CS source (rs2')
  const bool rv64 = xlen == 64;

  // immediates
  const uint64_t uimm_w = (bits(insn, 5, 5) << 6) | (bits(insn, 12, 10) << 3) |
                          (bits(insn, 6, 6) << 2);                                  // CL/CS word
  const uint64_t uimm_d = (bits(insn, 6, 5) << 6) | (bits(insn, 12, 10) << 3);      // CL/CS double
  const int64_t imm_ci = sext((bits(insn, 12, 12) << 5) | bits(insn, 6, 2), 6);     // CI signed
  const uint64_t shamt = (bits(insn, 12, 12) << 5) | bits(insn, 6, 2);              // CI shift
  const uint64_t uimm_wsp = (bits(insn, 3, 2) << 6) | (bits(insn, 12, 12) << 5) |
                            (bits(insn, 6, 4) << 2);                                // c.lwsp
  const uint64_t uimm_dsp = (bits(insn, 4, 2) << 6) | (bits(insn, 12, 12) << 5) |
                            (bits(insn, 6, 5) << 3);                                // c.ldsp
  const uint64_t uimm_wssp = (bits(insn, 8, 7) << 6) | (bits(insn, 12, 9) << 2);    // c.swsp
  const uint64_t uimm_dssp = (bits(insn, 9, 7) << 6) | (bits(insn, 12, 10) << 3);   // c.sdsp
  const uint64_t uimm_4spn = (bits(insn, 10, 7) << 6) | (bits(insn, 12, 11) << 4) |
                             (bits(insn, 5, 5) << 3) | (bits(insn, 6, 6) << 2);     // c.addi4spn
  const int64_t imm_16sp = sext((bits(insn, 12, 12) << 9) | (bits(insn, 4, 3) << 7) |
                                    (bits(insn, 5, 5) << 6) | (bits(insn, 2, 2) << 5) |
                                    (bits(insn, 6, 6) << 4),
                                10);
  const int64_t imm_j = sext((bits(insn, 12, 12) << 11) | (bits(insn, 8, 8) << 10) |
                                 (bits(insn, 10, 9) << 8) | (bits(insn, 6, 6) << 7) |
                                 (bits(insn, 7, 7) << 6) | (bits(insn, 2, 2) << 5) |
                                 (bits(insn, 11, 11) << 4) | (bits(insn, 5, 3) << 1),
                             12);
  const int64_t imm_b = sext((bits(insn, 12, 12) << 8) | (bits(insn, 6, 5) << 6) |
                                 (bits(insn, 2, 2) << 5) | (bits(insn, 11, 10) << 3) |
                                 (bits(insn, 4, 3) << 1),
                             9);

  switch (op) {
    case 0:  // quadrant 0
      switch (f3) {
        case 0:
          if (insn == 0) { p_mnemonic(d, "INVALID"); return; }  // illegal, all-zero
          p_i(d, "c.addi4spn", rdp, 2, (int64_t)uimm_4spn);
          return;
        case 1: p_load(d, "c.fld", REG_FPR, rdp, rs1p, (int64_t)uimm_d, 8); return;
        case 2: p_load(d, "c.lw", REG_GPR, rdp, rs1p, (int64_t)uimm_w, 4); return;
        case 3:
          if (rv64) p_load(d, "c.ld", REG_GPR, rdp, rs1p, (int64_t)uimm_d, 8);
          else p_load(d, "c.flw", REG_FPR, rdp, rs1p, (int64_t)uimm_w, 4);
          return;
        case 4: {  // Zcb byte and halfword accesses
          const uint64_t uimm_b = (bits(insn, 5, 5) << 1) | bits(insn, 6, 6);
          const uint64_t uimm_h = bits(insn, 5, 5) << 1;
          switch (bits(insn, 12, 10)) {
            case 0: p_load(d, "c.lbu", REG_GPR, rdp, rs1p, (int64_t)uimm_b, 1); return;
            case 1:
              if (bits(insn, 6, 6)) p_load(d, "c.lh", REG_GPR, rdp, rs1p, (int64_t)uimm_h, 2);
              else p_load(d, "c.lhu", REG_GPR, rdp, rs1p, (int64_t)uimm_h, 2);
              return;
            case 2: p_store(d, "c.sb", REG_GPR, rs2p, rs1p, (int64_t)uimm_b, 1); return;
            case 3: p_store(d, "c.sh", REG_GPR, rs2p, rs1p, (int64_t)uimm_h, 2); return;
            default: p_mnemonic(d, "INVALID"); return;
          }
        }
        case 5: p_store(d, "c.fsd", REG_FPR, rs2p, rs1p, (int64_t)uimm_d, 8); return;
        case 6: p_store(d, "c.sw", REG_GPR, rs2p, rs1p, (int64_t)uimm_w, 4); return;
        case 7:
          if (rv64) p_store(d, "c.sd", REG_GPR, rs2p, rs1p, (int64_t)uimm_d, 8);
          else p_store(d, "c.fsw", REG_FPR, rs2p, rs1p, (int64_t)uimm_w, 4);
          return;
        default: p_mnemonic(d, "INVALID"); return;
      }

    case 1:  // quadrant 1
      switch (f3) {
        case 0:
          if (rd == 0) p_mnemonic(d, "c.nop");
          else p_i(d, "c.addi", rd, rd, imm_ci);
          return;
        case 1:
          if (rv64) { p_i(d, "c.addiw", rd, rd, imm_ci); return; }
          d.is_jump = true;
          p_i(d, "c.jal", 1, 0, imm_j);
          return;
        case 2: p_i(d, "c.li", rd, 0, imm_ci); return;
        case 3:
          if (rd == 2) p_i(d, "c.addi16sp", 2, 2, imm_16sp);
          else p_u(d, "c.lui", rd, (uint32_t)(imm_ci & 0xFFFFF));
          return;
        case 4:
          switch (bits(insn, 11, 10)) {
            case 0: p_i(d, "c.srli", rs1p, rs1p, (int64_t)shamt); return;
            case 1: p_i(d, "c.srai", rs1p, rs1p, (int64_t)shamt); return;
            case 2: p_i(d, "c.andi", rs1p, rs1p, imm_ci); return;
            default:
              if (bits(insn, 12, 12) == 0) {
                switch (bits(insn, 6, 5)) {
                  case 0: p_r(d, "c.sub", rs1p, rs1p, rs2p); return;
                  case 1: p_r(d, "c.xor", rs1p, rs1p, rs2p); return;
                  case 2: p_r(d, "c.or", rs1p, rs1p, rs2p); return;
                  default: p_r(d, "c.and", rs1p, rs1p, rs2p); return;
                }
              } else {
                switch (bits(insn, 6, 5)) {
                  case 0: p_r(d, "c.subw", rs1p, rs1p, rs2p); return;
                  case 1: p_r(d, "c.addw", rs1p, rs1p, rs2p); return;
                  case 2: p_r(d, "c.mul", rs1p, rs1p, rs2p); return;  // Zcb
                  default:  // Zcb single operand forms, rd' is also the source
                    switch (bits(insn, 4, 2)) {
                      case 0: p_r1(d, "c.zext.b", rs1p, rs1p); return;
                      case 1: p_r1(d, "c.sext.b", rs1p, rs1p); return;
                      case 2: p_r1(d, "c.zext.h", rs1p, rs1p); return;
                      case 3: p_r1(d, "c.sext.h", rs1p, rs1p); return;
                      case 4: p_r1(d, "c.zext.w", rs1p, rs1p); return;
                      case 5: p_r1(d, "c.not", rs1p, rs1p); return;
                      default: p_mnemonic(d, "INVALID"); return;
                    }
                }
              }
          }
        case 5: d.is_jump = true; p_i(d, "c.j", 0, 0, imm_j); return;
        case 6: d.is_branch = true; p_sb(d, "c.beqz", rs1p, 0, imm_b); return;
        case 7: d.is_branch = true; p_sb(d, "c.bnez", rs1p, 0, imm_b); return;
        default: p_mnemonic(d, "INVALID"); return;
      }

    case 2:  // quadrant 2
      switch (f3) {
        case 0: p_i(d, "c.slli", rd, rd, (int64_t)shamt); return;
        case 1: p_load(d, "c.fldsp", REG_FPR, rd, 2, (int64_t)uimm_dsp, 8); return;
        case 2: p_load(d, "c.lwsp", REG_GPR, rd, 2, (int64_t)uimm_wsp, 4); return;
        case 3:
          if (rv64) p_load(d, "c.ldsp", REG_GPR, rd, 2, (int64_t)uimm_dsp, 8);
          else p_load(d, "c.flwsp", REG_FPR, rd, 2, (int64_t)uimm_wsp, 4);
          return;
        case 4:
          if (bits(insn, 12, 12) == 0) {
            if (rs2 == 0) { d.is_jump = true; p_i(d, "c.jr", 0, rd, 0); }
            else p_r(d, "c.mv", rd, 0, rs2);
          } else {
            if (rd == 0 && rs2 == 0) p_mnemonic(d, "c.ebreak");
            else if (rs2 == 0) { d.is_jump = true; p_i(d, "c.jalr", 1, rd, 0); }
            else p_r(d, "c.add", rd, rd, rs2);
          }
          return;
        case 5:
          // cm.jt / cm.jalt occupy the c.fsdsp encoding, so only one of the two
          // can exist in a given configuration
          if ((ext & RV_EXT_ZCMT) && bits(insn, 12, 10) == 0) {
            const unsigned index = bits(insn, 9, 2);
            if (index >= 32) add_dst(d, REG_GPR, 1);  // cm.jalt links ra
            d.text = fmt("%-12s %4u", index >= 32 ? "cm.jalt" : "cm.jt", index);
            return;
          }
          p_store(d, "c.fsdsp", REG_FPR, rs2, 2, (int64_t)uimm_dssp, 8);
          return;
        case 6: p_store(d, "c.swsp", REG_GPR, rs2, 2, (int64_t)uimm_wssp, 4); return;
        case 7:
          if (rv64) p_store(d, "c.sdsp", REG_GPR, rs2, 2, (int64_t)uimm_dssp, 8);
          else p_store(d, "c.fswsp", REG_FPR, rs2, 2, (int64_t)uimm_wssp, 4);
          return;
        default: p_mnemonic(d, "INVALID"); return;
      }

    default: p_mnemonic(d, "INVALID"); return;
  }
}

// ---------------------------------------------------------------------------

// Replaces the legacy text with spike's spelling, see rv_disasm_spike.cc.
void render_spike(decoded_t &d, uint32_t insn, int xlen, unsigned ext);

decoded_t rv_decode(uint32_t insn, int xlen, unsigned ext, rv_style_t style) {
  decoded_t d;
  d.has_target = false;
  d.target_offset = 0;
  d.target_pos = 0;
  d.dst.kind = REG_NONE;
  d.dst.idx = 0;
  for (unsigned i = 0; i < 3; i++) { d.src[i].kind = REG_NONE; d.src[i].idx = 0; }
  d.n_src = 0;
  d.is_load = d.is_store = d.is_amo = d.is_csr = false;
  d.is_branch = d.is_jump = false;
  d.csr_addr = 0;
  d.mem_bytes = 0;

  if ((insn & 0x3u) != 0x3u) decode_16(d, insn & 0xFFFFu, xlen, ext);
  else decode_32(d, insn, xlen);
  if (style == RV_STYLE_SPIKE) render_spike(d, insn, xlen, ext);
  return d;
}

}  // namespace cva6tb_tracer

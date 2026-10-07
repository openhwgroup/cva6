// Copyright 2026 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51
//
// Author: Enrico Zelioli <ezelioli@iis.ee.ethz.ch>
//
// The output formats and the factory that picks between them.

#include "rv_format.h"

#include <algorithm>
#include <cstdarg>
#include <cstring>
#include <string>

#include "cva6tb_tracer_dpi.h"

namespace cva6tb_tracer {

namespace {

char priv_char(unsigned char priv) {
  switch (priv & 3) {
    case 0: return 'U';
    case 1: return 'S';
    case 2: return 'D';  // cva6 reports debug mode as 2'b10 on rvfi.mode
    default: return 'M';
  }
}

// The mode an instruction ran in: the privilege level and the virtualisation
// bit together, since the privilege level alone cannot tell HS from VS or U
// from VU. One or two characters, so callers pad to two to keep a trace of
// virtualised code lined up with one that is not.
const char *mode_name(unsigned char priv, bool virt) {
  if (!virt) {
    switch (priv & 3) {
      case 0: return "U";
      case 1: return "S";
      case 2: return "D";
      default: return "M";
    }
  }
  switch (priv & 3) {
    case 0: return "VU";
    case 1: return "VS";
    default: return "?";  // machine and debug mode are never virtualised
  }
}

// Human readable cause, in the wording the legacy ex_trace_item used.
// The exception code lives in the low 12 bits; in CLIC mode the bits above it
// carry the saved interrupt level and privilege, so they must be masked off.
const char *cause_text(uint64_t cause, int xlen) {
  const uint64_t irq_bit = 1ull << (xlen - 1);
  const uint64_t code = cause & 0xFFFull;
  if (cause & irq_bit) {
    switch (code) {
      case 1:  return "Supervisor Software Interrupt";
      case 3:  return "Machine Software Interrupt";
      case 5:  return "Supervisor Timer Interrupt";
      case 7:  return "Machine Timer Interrupt";
      case 9:  return "Supervisor External Interrupt";
      case 11: return "Machine External Interrupt";
      case 2:  return "Virtual Supervisor Software Interrupt";
      case 6:  return "Virtual Supervisor Timer Interrupt";
      case 10: return "Virtual Supervisor External Interrupt";
      case 12: return "Supervisor Guest External Interrupt";
      default: return "Interrupt";
    }
  }
  switch (code) {
    case 0:  return "Instruction Address Misaligned";
    case 1:  return "Instruction Access Fault";
    case 2:  return "Illegal Instruction";
    case 3:  return "Breakpoint";
    case 4:  return "Load Address Misaligned";
    case 5:  return "Load Access Fault";
    case 6:  return "Store Address Misaligned";
    case 7:  return "Store Access Fault";
    case 8:  return "Environment Call User Mode";
    case 9:  return "Environment Call Supervisor Mode";
    case 10: return "Environment Call Virtual Supervisor Mode";
    case 11: return "Environment Call Machine Mode";
    case 12: return "Instruction Page Fault";
    case 13: return "Load Page Fault";
    case 15: return "Store Page Fault";
    case 20: return "Instruction Guest Page Fault";
    case 21: return "Load Guest Page Fault";
    case 22: return "Virtual Instruction";
    case 23: return "Store Guest Page Fault";
    default: return "Unknown Exception";
  }
}

// tval carries no information for environment calls and interrupts
bool cause_has_tval(uint64_t cause, int xlen) {
  if (cause & (1ull << (xlen - 1))) return false;
  const uint64_t code = cause & 0xFFFull;
  return !(code >= 8 && code <= 11);  // environment calls
}

// Appending helper: keeps track of how much of `buf` is already used.
struct line_t {
  char   buf[1024];
  size_t n = 0;

  void add(const char *f, ...) __attribute__((format(printf, 2, 3))) {
    if (n >= sizeof(buf) - 1) return;
    va_list ap;
    va_start(ap, f);
    int w = vsnprintf(buf + n, sizeof(buf) - n, f, ap);
    va_end(ap);
    if (w > 0) n += ((size_t)w < sizeof(buf) - n) ? (size_t)w : (sizeof(buf) - n - 1);
  }
};

// Match a decoded source operand against the two operand slots RVFI reports.
// Integer code matches by register number; for the few cva6 instructions whose
// scoreboard operand slots do not line up with the architectural rs1/rs2 (most
// notably the FP ops) we fall back to consuming the slots in order.
struct src_values_t {
  uint8_t  addr[2];
  uint64_t val[2];
  bool     used[2];

  bool lookup(const reg_ref_t &r, uint64_t *out) {
    for (int i = 0; i < 2; i++)
      if (!used[i] && addr[i] == r.idx) { used[i] = true; *out = val[i]; return true; }
    for (int i = 0; i < 2; i++)
      if (!used[i]) { used[i] = true; *out = val[i]; return true; }
    return false;
  }
};

}  // namespace

// ---------------------------------------------------------------------------
// trace: the default, one plain text line per instruction, meant to be read
//
// Every column before the sources has a fixed width, with time and cycle right
// aligned, so the lines align in any editor. Instruction lines are indented
// under the symbol headers, which start in column 0; time only grows, so their
// indentation never increases, and an editor folding by indentation folds one
// function at a time. The disassembly is spike's, with branch and jump targets
// as absolute addresses. The effects say what the instruction changed, with
// values in hex and no leading zeros and register names padded so that their
// `=` line up, and the sources what it read. Traps and interrupts are marked
// `!!`.
// ---------------------------------------------------------------------------

namespace {

constexpr int TRACE_TIME_WIDTH = 11;
constexpr int TRACE_CYCLE_WIDTH = 10;
constexpr int TRACE_MNEMONIC_WIDTH = 10;
constexpr int TRACE_DISASM_WIDTH = 40;
constexpr int TRACE_EFFECTS_WIDTH = 36;

std::string hex(uint64_t v) {
  char buf[24];
  snprintf(buf, sizeof(buf), "0x%llx", (unsigned long long)v);
  return buf;
}

// A register written, its name padded to the longest name of its register
// file so that the `=` of every register lines up.
std::string written_reg(const reg_ref_t &reg, uint64_t v) {
  char buf[48];
  if (reg.kind == REG_FPR)
    snprintf(buf, sizeof(buf), "%-4s = 0x%llx", rv_fpr_name(reg.idx), (unsigned long long)v);
  else
    snprintf(buf, sizeof(buf), "%-3s = 0x%llx", rv_gpr_name(reg.idx), (unsigned long long)v);
  return buf;
}

std::string lowercase(const char *s) {
  std::string out(s);
  for (char &c : out)
    if (c >= 'A' && c <= 'Z') c = (char)(c - 'A' + 'a');
  return out;
}

std::string csr_effects(const csr_write_t *w, unsigned n) {
  std::string out;
  for (unsigned i = 0; i < n; i++) {
    if (!out.empty()) out += "  ";
    out += rv_csr_name(w[i].addr) + " = " + hex(w[i].value);
  }
  return out;
}

std::string symbol_ref(const symbol_t *sym, uint64_t addr) {
  if (!sym) return std::string();
  const uint64_t off = addr - sym->addr;
  return off ? "<" + sym->name + "+" + hex(off) + ">" : "<" + sym->name + ">";
}

class trace_formatter_t : public formatter_t {
 public:
  explicit trace_formatter_t(const format_config_t &cfg) : cfg_(cfg) {}

  rv_style_t style() const override { return RV_STYLE_SPIKE; }

  void header(FILE *f) override {
    fprintf(f, "# cva6 trace: RV%d, hart %u, verbosity %d\n", cfg_.xlen, cfg_.hart_id,
            cfg_.verbosity);
    fprintf(f, "# %*s %*s  %-2s %-*s  %-8s  %-*s  %-*s  %s\n", TRACE_TIME_WIDTH, "time",
            TRACE_CYCLE_WIDTH, "cycle", "md", cfg_.pc_digits, "pc", "encoding",
            TRACE_DISASM_WIDTH, "disassembly", TRACE_EFFECTS_WIDTH, "effects", "sources");
  }

  void retire(FILE *f, const retire_info_t &r) override;
  void trap(FILE *f, const trap_info_t &t) override;

 private:
  // time, cycle and mode, the columns every line starts with
  void lead(line_t &l, uint64_t time_ns, uint64_t cycle, uint8_t priv, bool virt) const {
    char t[32];
    snprintf(t, sizeof(t), "%lluns", (unsigned long long)time_ns);
    l.add("  %*s %*llu  %-2s ", TRACE_TIME_WIDTH, t, TRACE_CYCLE_WIDTH,
          (unsigned long long)cycle, mode_name(priv, virt));
  }

  // pc, encoding and disassembly
  void instruction(line_t &l, uint64_t pc, uint32_t insn, const decoded_t &d,
                   const symbol_t *target_sym, bool more) const {
    if ((insn & 0x3u) != 0x3u)
      l.add("%0*llx      %04x  ", cfg_.pc_digits, (unsigned long long)pc, insn & 0xFFFFu);
    else
      l.add("%0*llx  %08x  ", cfg_.pc_digits, (unsigned long long)pc, insn);
    std::string text = d.mnemonic;
    if (!d.operands.empty()) {
      text.resize(text.size() < TRACE_MNEMONIC_WIDTH ? TRACE_MNEMONIC_WIDTH : text.size() + 1, ' ');
      if (d.has_target) {
        const uint64_t target = rv_target_address(d, pc, cfg_.xlen);
        text += d.operands.substr(0, d.target_pos) + hex(target);
        if (target_sym) text += " " + symbol_ref(target_sym, target);
      } else {
        text += d.operands;
      }
    }
    if (more) l.add("%-*s  ", TRACE_DISASM_WIDTH, text.c_str());
    else l.add("%s", text.c_str());
  }

  std::string mem_ref(const retire_info_t &r) const {
    if (r.mem_paddr == r.mem_vaddr) return "mem[" + hex(r.mem_vaddr) + "]";
    return "mem[" + hex(r.mem_vaddr) + " pa=" + hex(r.mem_paddr) + "]";
  }

  format_config_t cfg_;
};

void trace_formatter_t::retire(FILE *f, const retire_info_t &r) {
  const decoded_t &d = *r.dec;
  const bool       virt = (r.flags & CVA6_TRACE_FLAG_VIRT) != 0;
  line_t           l;

  // CSR writes from cycles in which nothing retired: the entry into an
  // interrupt handler is one, and they go on the interrupt line
  const std::string earlier = csr_effects(r.csr.earlier, r.csr.n_earlier);
  if ((r.flags & CVA6_TRACE_FLAG_TRAP_ENTRY) && (r.flags & CVA6_TRACE_FLAG_INTERRUPT)) {
    lead(l, r.sim_time_ns, r.cycle, r.priv, virt);
    l.add("!! interrupt%s%s\n", earlier.empty() ? "" : "  ", earlier.c_str());
  } else if (!earlier.empty()) {
    lead(l, r.sim_time_ns, r.cycle, r.priv, virt);
    l.add("-- %s\n", earlier.c_str());
  }

  // what the instruction changed
  std::string effects;
  auto        effect = [&effects](const std::string &e) {
    if (!effects.empty()) effects += "  ";
    effects += e;
  };
  std::string written;
  if (d.dst.kind == REG_FPR || (d.dst.kind == REG_GPR && d.dst.idx != 0))
    written = written_reg(d.dst, r.rd_wdata);

  // RVFI reports every AMO, LR and SC as a write; show what each one does
  const unsigned funct5 = r.insn >> 27;
  const bool     lr = d.is_amo && funct5 == 0x02;
  const bool     sc = d.is_amo && funct5 == 0x03;
  const bool     reads = d.is_amo ? !sc : r.mem_rmask != 0;
  const bool     writes = d.is_amo ? !lr && !(sc && r.rd_wdata != 0) : r.mem_wmask != 0;
  if (reads) written += (written.empty() ? "<- " : " <- ") + mem_ref(r);
  if (!written.empty()) effect(written);
  if (writes) {
    const unsigned bytes = (d.mem_bytes && d.mem_bytes < 8) ? d.mem_bytes : 8;
    const uint64_t mask = bytes == 8 ? ~0ull : (1ull << (bytes * 8)) - 1;
    effect(mem_ref(r) + " <- " + hex(r.mem_wdata & mask));
  }
  if (r.insn == 0x00000073u) effect(std::string("!! ecall from ") + mode_name(r.priv, virt));
  if (r.csr.n_made) effect(csr_effects(r.csr.made, r.csr.n_made));

  if (r.flags & CVA6_TRACE_FLAG_BRANCH) {
    const bool mispredicted = (r.flags & CVA6_TRACE_FLAG_MISPREDICT) != 0;
    if (d.is_branch)
      effect(std::string((r.flags & CVA6_TRACE_FLAG_TAKEN) ? "taken" : "not taken") +
             (mispredicted ? ", mispredicted" : ""));
    else if (mispredicted)
      effect("mispredicted");
  }
  if (r.sym) effect(symbol_ref(r.sym, r.pc));

  // what it read
  std::string sources;
  src_values_t srcs = {{r.rs1_addr, r.rs2_addr}, {r.rs1_rdata, r.rs2_rdata}, {false, false}};
  for (unsigned i = 0; i < d.n_src; i++) {
    const reg_ref_t &reg = d.src[i];
    if (reg.kind == REG_GPR && reg.idx == 0) continue;
    uint64_t v = 0;
    const bool known = srcs.lookup(reg, &v);
    if (!sources.empty()) sources += " ";
    sources += std::string(reg.kind == REG_FPR ? rv_fpr_name(reg.idx) : rv_gpr_name(reg.idx)) +
               "=" + (known ? hex(v) : std::string("?"));
  }

  // where it retired, for dual issue questions
  std::string comment;
  if (cfg_.verbosity >= 1)
    comment = "p" + std::to_string(r.commit_port) + " #" + std::to_string(r.order);

  lead(l, r.sim_time_ns, r.cycle, r.priv, virt);
  const bool after_effects = !sources.empty() || !comment.empty();
  instruction(l, r.pc, r.insn, d, r.target_sym, !effects.empty() || after_effects);
  if (after_effects) l.add("%-*s  ", TRACE_EFFECTS_WIDTH, effects.c_str());
  else l.add("%s", effects.c_str());
  if (!sources.empty()) l.add("%s", sources.c_str());
  if (!comment.empty()) l.add("%s# %s", sources.empty() ? "" : "  ", comment.c_str());
  l.add("\n");
  fwrite(l.buf, 1, l.n, f);
}

void trace_formatter_t::trap(FILE *f, const trap_info_t &t) {
  line_t l;
  const std::string earlier = csr_effects(t.csr.earlier, t.csr.n_earlier);
  if (!earlier.empty()) {
    lead(l, t.sim_time_ns, t.cycle, t.priv, t.virt != 0);
    l.add("-- %s\n", earlier.c_str());
  }
  lead(l, t.sim_time_ns, t.cycle, t.priv, t.virt != 0);
  instruction(l, t.pc, t.insn, *t.dec, nullptr, true);
  l.add("!! %s", lowercase(cause_text(t.cause, cfg_.xlen)).c_str());
  if (cause_has_tval(t.cause, cfg_.xlen)) l.add(", tval %s", hex(t.tval).c_str());
  if (t.csr.n_made) l.add("  %s", csr_effects(t.csr.made, t.csr.n_made).c_str());
  l.add("\n");
  fwrite(l.buf, 1, l.n, f);
}

}  // namespace

// ---------------------------------------------------------------------------
// legacy: the format of common/local/util/instr_tracer.sv
// ---------------------------------------------------------------------------

namespace {

class legacy_formatter_t : public formatter_t {
 public:
  explicit legacy_formatter_t(const format_config_t &cfg) : cfg_(cfg) {}

  void header(FILE *f) override {
    if (cfg_.verbosity <= 0) return;
    fprintf(f, "# cva6 tracer: RV%d, verbosity=%d\n", cfg_.xlen, cfg_.verbosity);
    fprintf(f, "# time cycle priv pc mispredict insn%s disassembly  <written reg>  <read regs>\n",
            cfg_.verbosity >= 2 ? " [port #order]" : "");
  }

  void retire(FILE *f, const retire_info_t &r) override;
  void trap(FILE *f, const trap_info_t &t) override;

 private:
  format_config_t cfg_;
};

void legacy_formatter_t::retire(FILE *f, const retire_info_t &r) {
  const decoded_t &d = *r.dec;
  const uint32_t insn_print = ((r.insn & 0x3u) != 0x3u) ? (r.insn & 0xFFFFu) : r.insn;

  line_t l;
  l.add("%8lluns %8llu %c %0*llx %llu %08x ", r.sim_time_ns, r.cycle, priv_char(r.priv),
        cfg_.pc_digits, r.pc, (unsigned long long)(r.flags & CVA6_TRACE_FLAG_MISPREDICT),
        insn_print);
  if (cfg_.verbosity >= 2) l.add("[p%u #%llu] ", (unsigned)r.commit_port, r.order);
  l.add("%-36s", d.text.c_str());

  // destination register, with the value RVFI reports for it
  if (d.dst.kind == REG_FPR) {
    l.add(" %-4s:%016llx", rv_fpr_name(d.dst.idx), r.rd_wdata);
  } else if (d.dst.kind == REG_GPR && d.dst.idx != 0) {
    l.add(" %-4s:%016llx", rv_gpr_name(d.dst.idx), r.rd_wdata);
  }

  // source registers
  src_values_t srcs = {{r.rs1_addr, r.rs2_addr}, {r.rs1_rdata, r.rs2_rdata}, {false, false}};
  for (unsigned i = 0; i < d.n_src; i++) {
    const reg_ref_t &reg = d.src[i];
    uint64_t v = 0;
    const bool known = srcs.lookup(reg, &v);
    if (reg.kind == REG_FPR) {
      if (known) l.add(" %-4s:%016llx", rv_fpr_name(reg.idx), (unsigned long long)v);
      else l.add(" %-4s:%16s", rv_fpr_name(reg.idx), "----------------");
    } else if (reg.kind == REG_GPR && reg.idx != 0) {
      if (known) l.add(" %-4s:%016llx", rv_gpr_name(reg.idx), (unsigned long long)v);
      else l.add(" %-4s:%16s", rv_gpr_name(reg.idx), "----------------");
    }
  }

  // addresses: the legacy tracer printed these for plain loads and stores only
  const bool show_addr = d.is_load || d.is_store || (cfg_.verbosity >= 1 && d.is_amo);
  if (show_addr && (r.mem_rmask || r.mem_wmask)) {
    l.add(" VA: %0*llx PA: %0*llx", cfg_.pc_digits, r.mem_vaddr, cfg_.pa_digits, r.mem_paddr);
  }

  if (cfg_.verbosity >= 1) {
    const unsigned bytes = d.mem_bytes ? d.mem_bytes : 8;
    const uint64_t mask = (bytes >= 8) ? ~0ull : ((1ull << (bytes * 8)) - 1);
    if (r.mem_wmask) l.add(" ST:0x%0*llx", (int)(bytes * 2), r.mem_wdata & mask);
    if (r.mem_rmask) l.add(" LD:0x%0*llx", (int)(bytes * 2), r.mem_rdata & mask);
    if (d.is_csr) {
      l.add(" csr:%s", rv_csr_name(d.csr_addr).c_str());
      const unsigned f3 = (r.insn >> 12) & 7;
      const unsigned rs1_field = (r.insn >> 15) & 0x1F;
      const uint64_t operand = ((f3 & 4) != 0) ? rs1_field : r.rs1_rdata;
      const bool     writes = (f3 & 3) == 1 || rs1_field != 0;
      const bool     old_known = r.rd_addr != 0;
      // the value written, as RVFI reports it, or else reconstructed from the operands
      const csr_write_t *reported = nullptr;
      for (unsigned i = 0; i < r.csr.n_made; i++)
        if (r.csr.made[i].addr == d.csr_addr) reported = &r.csr.made[i];
      if (writes && reported) {
        l.add(" <-%016llx", reported->value);
      } else if (writes) {
        switch (f3 & 3) {
          case 1: l.add(" <-%016llx", (unsigned long long)operand); break;
          case 2:
            if (old_known) l.add(" <-%016llx", (unsigned long long)(r.rd_wdata | operand));
            break;
          case 3:
            if (old_known) l.add(" <-%016llx", (unsigned long long)(r.rd_wdata & ~operand));
            break;
          default: break;
        }
      }
    }
  }

  // branch outcome, which only a resolved control flow instruction carries
  if (cfg_.verbosity >= 1 && (r.flags & CVA6_TRACE_FLAG_BRANCH)) {
    l.add(" br:%s%s", (r.flags & CVA6_TRACE_FLAG_TAKEN) ? "taken" : "not-taken",
          (r.flags & CVA6_TRACE_FLAG_MISPREDICT) ? ",mispredicted" : "");
  }

  if (cfg_.verbosity >= 1 && (r.flags & CVA6_TRACE_FLAG_TRAP_ENTRY))
    l.add((r.flags & CVA6_TRACE_FLAG_INTERRUPT) ? "  <- interrupt entry" : "  <- trap entry");

  if (r.sym) {
    const uint64_t off = r.pc - r.sym->addr;
    if (off) l.add(" <%s+0x%llx>", r.sym->name.c_str(), (unsigned long long)off);
    else l.add(" <%s>", r.sym->name.c_str());
  }

  l.add("\n");
  fwrite(l.buf, 1, l.n, f);
}

void legacy_formatter_t::trap(FILE *f, const trap_info_t &t) {
  line_t l;
  l.add("Exception @%10lluns, PC: %0*llx, Cause: %s", t.sim_time_ns, cfg_.pc_digits, t.pc,
        cause_text(t.cause, cfg_.xlen));
  if (cause_has_tval(t.cause, cfg_.xlen)) l.add(", \n\t\t\t\ttval: %016llx", t.tval);
  if (cfg_.verbosity >= 1) {
    const uint32_t insn_print = ((t.insn & 0x3u) != 0x3u) ? (t.insn & 0xFFFFu) : t.insn;
    l.add("\n#%8lluns %8llu %c %0*llx - %08x %-36s [%s cause:%016llx]", t.sim_time_ns, t.cycle,
          priv_char(t.priv), cfg_.pc_digits, t.pc, insn_print, t.dec->text.c_str(),
          rv_cause_name(t.cause, cfg_.xlen).c_str(), t.cause);
  }
  l.add("\n");
  fwrite(l.buf, 1, l.n, f);
}

}  // namespace

// ---------------------------------------------------------------------------
// The commit log, in two dialects.
//
// Two lines per instruction: the first names it, the second says what it
// changed. `spike` reproduces what `spike -l --log-commits` writes, down to the
// per line `core N:` prefix and the register column, so the two logs diff
// against each other directly. `rvfi` is the same information in the spelling
// corev_apu/tb/rvfi_tracer.sv uses, which is what some of the converters under
// verif/sim/ were written against.
//
// Both carry the disassembly spike-dasm would print, produced here, so there is
// no DASM() placeholder and no spike-dasm pass to run.
// ---------------------------------------------------------------------------

namespace {

// spike's wording for a trap, which is what the converters' ILLE_RE looks for
const char *spike_cause_name(uint64_t cause, int xlen) {
  if (cause & (1ull << (xlen - 1))) return "interrupt";
  switch (cause & 0xFFFull) {
    case 0:  return "trap_instruction_address_misaligned";
    case 1:  return "trap_instruction_access_fault";
    case 2:  return "trap_illegal_instruction";
    case 3:  return "trap_breakpoint";
    case 4:  return "trap_load_address_misaligned";
    case 5:  return "trap_load_access_fault";
    case 6:  return "trap_store_address_misaligned";
    case 7:  return "trap_store_access_fault";
    case 8:  return "trap_user_ecall";
    case 9:  return "trap_supervisor_ecall";
    case 10: return "trap_virtual_supervisor_ecall";
    case 11: return "trap_machine_ecall";
    case 12: return "trap_instruction_page_fault";
    case 13: return "trap_load_page_fault";
    case 15: return "trap_store_page_fault";
    case 20: return "trap_instruction_guest_page_fault";
    case 21: return "trap_load_guest_page_fault";
    case 22: return "trap_virtual_instruction";
    case 23: return "trap_store_guest_page_fault";
    default: return "trap_unknown";
  }
}

class commit_log_formatter_t : public formatter_t {
 public:
  enum dialect_t { SPIKE, RVFI };

  commit_log_formatter_t(const format_config_t &cfg, dialect_t dialect)
      : cfg_(cfg), dialect_(dialect) {}

  bool machine_readable() const override { return true; }
  rv_style_t style() const override { return RV_STYLE_SPIKE; }

  void retire(FILE *f, const retire_info_t &r) override {
    line_t l;
    if (dialect_ == SPIKE) spike_lines(l, r);
    else rvfi_lines(l, r);
    fwrite(l.buf, 1, l.n, f);
  }

  void trap(FILE *f, const trap_info_t &t) override {
    if (dialect_ == SPIKE) {
      const int xdigits = cfg_.xlen / 4;
      fprintf(f, "core %3u: 0x%0*llx (0x%08x) %s\n", cfg_.hart_id, cfg_.pc_digits, t.pc, t.insn,
              t.dec->text.c_str());
      fprintf(f, "core %3u: exception %s, epc 0x%0*llx\n", cfg_.hart_id,
              spike_cause_name(t.cause, cfg_.xlen), xdigits, t.pc);
      if (cause_has_tval(t.cause, cfg_.xlen))
        fprintf(f, "core %3u:           tval 0x%0*llx\n", cfg_.hart_id, xdigits, t.tval);
      return;
    }
    const uint32_t insn_short = ((t.insn & 0x3u) != 0x3u) ? (t.insn & 0xFFFFu) : t.insn;
    fprintf(f, "%s exception @ 0x%0*llx (0x%x)\n", rv_cause_name(t.cause, cfg_.xlen).c_str(),
            cfg_.pc_digits, t.pc, insn_short);
  }

 private:
  // What spike writes: the register written, then the memory read, then the
  // memory written, each value at its own width. RVFI reports every AMO, LR
  // and SC as a write; spike logs what each of them actually does.
  void spike_lines(line_t &l, const retire_info_t &r) const {
    const decoded_t &d = *r.dec;
    const bool       compressed = (r.insn & 0x3u) != 0x3u;
    const int        xdigits = cfg_.xlen / 4;
    l.add("core %3u: 0x%0*llx (0x%08x) %s\n", cfg_.hart_id, cfg_.pc_digits, r.pc, r.insn,
          d.text.c_str());
    // spike takes an ecall as a trap rather than a retirement, and logs it so.
    // The cause depends on the mode the ecall came from: VS mode has its own,
    // and VU mode raises the same cause as U mode.
    if (r.insn == 0x00000073u) {
      const bool     virt = (r.flags & CVA6_TRACE_FLAG_VIRT) != 0;
      const uint64_t cause = (r.priv & 3) == 1 ? (virt ? 10 : 9) : ((r.priv & 3) == 3 ? 11 : 8);
      l.add("core %3u: exception %s, epc 0x%0*llx\n", cfg_.hart_id,
            spike_cause_name(cause, cfg_.xlen), xdigits, r.pc);
      return;
    }
    // the privilege digit is spike's `state->prv` and carries no virtualisation
    // bit, so VS prints as 1 here even though the trace format calls it VS
    l.add("core %3u: %x 0x%0*llx (0x%0*x)", cfg_.hart_id, r.priv & 3, cfg_.pc_digits, r.pc,
          compressed ? 4 : 8, compressed ? (r.insn & 0xFFFFu) : r.insn);

    // registers and CSRs in the order spike keeps them: by number, with an x
    // register ahead of the f register of the same number, and a CSR after both
    struct record_t {
      uint32_t key;
      char     text[64];
    };
    record_t records[16];
    unsigned n = 0;
    if (d.dst.kind == REG_FPR) {
      records[n].key = (uint32_t)d.dst.idx << 4 | 1;
      snprintf(records[n++].text, sizeof(records[0].text), " f%-2u 0x%0*llx", (unsigned)d.dst.idx,
               xdigits, r.rd_wdata);
    } else if (d.dst.kind == REG_GPR && d.dst.idx != 0) {
      records[n].key = (uint32_t)d.dst.idx << 4;
      snprintf(records[n++].text, sizeof(records[0].text), " x%-2u 0x%0*llx", (unsigned)d.dst.idx,
               xdigits, r.rd_wdata);
    }
    for (unsigned i = 0; i < r.csr.n_made && n < 16; i++) {
      const csr_write_t &w = r.csr.made[i];
      records[n].key = (uint32_t)w.addr << 4 | 4;
      snprintf(records[n++].text, sizeof(records[0].text), " c%u_%s 0x%0*llx", (unsigned)w.addr,
               rv_csr_name(w.addr).c_str(), xdigits, w.value);
    }
    std::sort(records, records + n,
              [](const record_t &a, const record_t &b) { return a.key < b.key; });
    for (unsigned i = 0; i < n; i++) l.add("%s", records[i].text);

    const unsigned funct5 = r.insn >> 27;
    const bool     lr = d.is_amo && funct5 == 0x02;
    const bool     sc = d.is_amo && funct5 == 0x03;
    const bool     reads = d.is_amo ? !sc : r.mem_rmask != 0;
    const bool     writes = d.is_amo ? !lr && !(sc && r.rd_wdata != 0) : r.mem_wmask != 0;
    if (reads) l.add(" mem 0x%0*llx", cfg_.pc_digits, r.mem_vaddr);
    if (writes) {
      const unsigned bytes = (d.mem_bytes && d.mem_bytes < 8) ? d.mem_bytes : 8;
      const uint64_t mask = bytes == 8 ? ~0ull : (1ull << (bytes * 8)) - 1;
      l.add(" mem 0x%0*llx 0x%0*llx", cfg_.pc_digits, r.mem_vaddr, (int)bytes * 2,
            (unsigned long long)(r.mem_wdata & mask));
    }
    l.add("\n");
  }

  // What corev_apu/tb/rvfi_tracer.sv writes, with the disassembly filled in.
  void rvfi_lines(line_t &l, const retire_info_t &r) const {
    const decoded_t &d = *r.dec;
    const bool       compressed = (r.insn & 0x3u) != 0x3u;
    l.add("core %s%u: 0x%0*llx (0x%08x) %s\n",
          (r.flags & CVA6_TRACE_FLAG_INTERRUPT) ? "  INTERRUPT " : "  ", cfg_.hart_id,
          cfg_.pc_digits, r.pc, r.insn, d.text.c_str());
    l.add("%x 0x%0*llx (0x%0*x)", r.priv & 3, cfg_.pc_digits, r.pc, compressed ? 4 : 8,
          compressed ? (r.insn & 0xFFFFu) : r.insn);
    if (d.dst.kind == REG_FPR) {
      l.add(" %c%2u 0x%016llx", 'f', (unsigned)d.dst.idx, r.rd_wdata);
    } else if (d.dst.kind == REG_GPR && d.dst.idx != 0) {
      l.add(" %c%2u 0x%016llx", 'x', (unsigned)d.dst.idx, r.rd_wdata);
      if (r.mem_rmask) l.add(" mem 0x%0*llx", cfg_.pc_digits, r.mem_vaddr);
    }
    if (r.mem_wmask) l.add(" mem 0x%0*llx 0x%016llx", cfg_.pc_digits, r.mem_vaddr, r.mem_wdata);
    l.add("\n");
  }

  format_config_t cfg_;
  dialect_t       dialect_;
};

}  // namespace

// ---------------------------------------------------------------------------
// binary: fixed size little endian records
//
// Meant for tools, not for people. A short header names the geometry, then one
// record per event, all the same size and all naturally aligned, so a reader
// maps the file and indexes into it instead of parsing anything:
//
//   import numpy as np
//   rec = np.dtype([('cycle','<u8'), ('time_ns','<u8'), ...])
//   data = np.fromfile(path, dtype=rec, offset=64)
//
// The layout is documented in util/read_trace.py, which is both the reference
// reader and a converter. Fields keep their meaning across record kinds except
// where the table there says otherwise, and `reserved` leaves room to add
// fields without moving the ones already there.
// ---------------------------------------------------------------------------

namespace {

constexpr uint16_t BINARY_VERSION = 1;
constexpr uint16_t BINARY_RECORD_SIZE = 96;
constexpr uint8_t  BINARY_KIND_RETIRE = 0;
constexpr uint8_t  BINARY_KIND_TRAP = 1;
constexpr uint8_t  BINARY_KIND_CSR = 2;

// What the instruction is, so that a reader does not need a RISC-V decoder to
// answer the questions a decoder would otherwise be needed for.
constexpr uint8_t BINARY_CLASS_LOAD = 0x01;
constexpr uint8_t BINARY_CLASS_STORE = 0x02;
constexpr uint8_t BINARY_CLASS_AMO = 0x04;
constexpr uint8_t BINARY_CLASS_CSR = 0x08;
constexpr uint8_t BINARY_CLASS_BRANCH = 0x10;
constexpr uint8_t BINARY_CLASS_JUMP = 0x20;
constexpr uint8_t BINARY_CLASS_COMPRESSED = 0x40;

uint8_t binary_class_of(const decoded_t &d, uint32_t insn) {
  uint8_t c = 0;
  if (d.is_load) c |= BINARY_CLASS_LOAD;
  if (d.is_store) c |= BINARY_CLASS_STORE;
  if (d.is_amo) c |= BINARY_CLASS_AMO;
  if (d.is_csr) c |= BINARY_CLASS_CSR;
  if (d.is_branch) c |= BINARY_CLASS_BRANCH;
  if (d.is_jump) c |= BINARY_CLASS_JUMP;
  if ((insn & 0x3u) != 0x3u) c |= BINARY_CLASS_COMPRESSED;
  return c;
}

#pragma pack(push, 1)
struct binary_header_t {
  char     magic[8];  // "CVA6TRC"
  uint16_t version;
  uint16_t record_size;
  uint8_t  xlen;
  uint8_t  vlen;
  uint8_t  plen;
  uint8_t  hart_id;
  uint8_t  reserved[48];
};

struct binary_record_t {
  uint64_t cycle;
  uint64_t time_ns;
  uint64_t pc;
  uint64_t rd_wdata;   // trap: cause
  uint64_t rs1_rdata;  // trap: tval
  uint64_t rs2_rdata;  // trap: unused
  uint64_t mem_vaddr;
  uint64_t mem_paddr;
  uint64_t mem_wdata;
  uint64_t mem_rdata;
  uint32_t insn;
  uint8_t  kind;
  uint8_t  priv;
  uint8_t  flags;
  uint8_t  rd_addr;
  uint8_t  rs1_addr;
  uint8_t  rs2_addr;
  uint8_t  commit_port;
  uint8_t  mem_rmask;
  uint8_t  mem_wmask;
  uint8_t  klass;  // BINARY_CLASS_*, so no decoder is needed downstream
  uint16_t csr;    // the CSR address of a csr record
};
#pragma pack(pop)

static_assert(sizeof(binary_header_t) == 64, "binary header must stay 64 bytes");
static_assert(sizeof(binary_record_t) == BINARY_RECORD_SIZE, "record size must match the header");

class binary_formatter_t : public formatter_t {
 public:
  explicit binary_formatter_t(const format_config_t &cfg) : cfg_(cfg) {}

  bool machine_readable() const override { return true; }

  void header(FILE *f) override {
    binary_header_t h;
    memset(&h, 0, sizeof(h));
    memcpy(h.magic, "CVA6TRC", 7);
    h.version = BINARY_VERSION;
    h.record_size = BINARY_RECORD_SIZE;
    h.xlen = (uint8_t)cfg_.xlen;
    h.vlen = (uint8_t)(cfg_.pc_digits * 4);
    h.plen = (uint8_t)(cfg_.pa_digits * 4);
    h.hart_id = (uint8_t)cfg_.hart_id;
    fwrite(&h, sizeof(h), 1, f);
  }

  void retire(FILE *f, const retire_info_t &r) override {
    csr_records(f, r.csr.earlier, r.csr.n_earlier, r.pc, r.insn, r.priv);
    binary_record_t rec;
    memset(&rec, 0, sizeof(rec));
    rec.kind = BINARY_KIND_RETIRE;
    rec.cycle = r.cycle;
    rec.time_ns = r.sim_time_ns;
    rec.pc = r.pc;
    rec.rd_wdata = r.rd_wdata;
    rec.rs1_rdata = r.rs1_rdata;
    rec.rs2_rdata = r.rs2_rdata;
    rec.mem_vaddr = r.mem_vaddr;
    rec.mem_paddr = r.mem_paddr;
    rec.mem_wdata = r.mem_wdata;
    rec.mem_rdata = r.mem_rdata;
    rec.insn = r.insn;
    rec.priv = r.priv;
    rec.flags = r.flags;
    rec.rd_addr = r.rd_addr;
    rec.rs1_addr = r.rs1_addr;
    rec.rs2_addr = r.rs2_addr;
    rec.commit_port = r.commit_port;
    rec.mem_rmask = (uint8_t)r.mem_rmask;
    rec.mem_wmask = (uint8_t)r.mem_wmask;
    rec.klass = binary_class_of(*r.dec, r.insn);
    fwrite(&rec, sizeof(rec), 1, f);
    csr_records(f, r.csr.made, r.csr.n_made, r.pc, r.insn, r.priv);
  }

  void trap(FILE *f, const trap_info_t &t) override {
    csr_records(f, t.csr.earlier, t.csr.n_earlier, t.pc, t.insn, t.priv);
    binary_record_t rec;
    memset(&rec, 0, sizeof(rec));
    rec.kind = BINARY_KIND_TRAP;
    rec.cycle = t.cycle;
    rec.time_ns = t.sim_time_ns;
    rec.pc = t.pc;
    rec.rd_wdata = t.cause;
    rec.rs1_rdata = t.tval;
    rec.insn = t.insn;
    rec.priv = t.priv;
    rec.flags = (t.is_interrupt ? CVA6_TRACE_FLAG_INTERRUPT : 0) |
                (t.virt ? CVA6_TRACE_FLAG_VIRT : 0);
    rec.klass = binary_class_of(*t.dec, t.insn);
    fwrite(&rec, sizeof(rec), 1, f);
    csr_records(f, t.csr.made, t.csr.n_made, t.pc, t.insn, t.priv);
  }

 private:
  // one record per CSR write, carrying the pc of the event it goes with
  void csr_records(FILE *f, const csr_write_t *w, unsigned n, uint64_t pc, uint32_t insn,
                   uint8_t priv) {
    for (unsigned i = 0; i < n; i++) {
      binary_record_t rec;
      memset(&rec, 0, sizeof(rec));
      rec.kind = BINARY_KIND_CSR;
      rec.cycle = w[i].cycle;
      rec.time_ns = w[i].sim_time_ns;
      rec.pc = pc;
      rec.insn = insn;
      rec.priv = priv;
      rec.rd_wdata = w[i].value;
      rec.csr = w[i].addr;
      fwrite(&rec, sizeof(rec), 1, f);
    }
  }

  format_config_t cfg_;
};

}  // namespace

// ---------------------------------------------------------------------------

formatter_t *make_formatter(const char *name, const format_config_t &cfg) {
  const std::string n(name ? name : "");
  if (n.empty() || n == "trace") return new trace_formatter_t(cfg);
  if (n == "legacy") return new legacy_formatter_t(cfg);
  if (n == "spike") return new commit_log_formatter_t(cfg, commit_log_formatter_t::SPIKE);
  if (n == "rvfi") return new commit_log_formatter_t(cfg, commit_log_formatter_t::RVFI);
  if (n == "binary") return new binary_formatter_t(cfg);
  return nullptr;
}

const char *formatter_names() { return "trace, legacy, spike, rvfi, binary"; }

}  // namespace cva6tb_tracer

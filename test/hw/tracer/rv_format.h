// Copyright 2026 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51
//
// Author: Enrico Zelioli <ezelioli@iis.ee.ethz.ch>
//
// Output formats.
//
// The tracer decides *what* to report -- it owns the window, the symbol table
// and the decoder -- and a formatter decides *how* a report looks. Everything a
// line could possibly need is gathered into retire_info_t and trap_info_t and
// handed over, so adding a format means writing one class here and naming it in
// the factory at the bottom of rv_format.cc. Nothing in cva6tb_tracer.cc changes.
//
//   trace   plain text in fixed columns, meant to be read; the default
//   legacy  the format of common/local/util/instr_tracer.sv
//   spike   the commit log that spike -l --log-commits produces, which the
//           converters in verif/sim/ and the rest of the RISC-V tooling parse
//   rvfi    the same commit log in corev_apu/tb/rvfi_tracer.sv's spelling
//   binary  fixed size little endian records, for tools rather than for people

#ifndef CVA6TB_TRACER_RV_FORMAT_H
#define CVA6TB_TRACER_RV_FORMAT_H

#include <cstdint>
#include <cstdio>

#include "rv_disasm.h"
#include "rv_symbols.h"

namespace cva6tb_tracer {

// Fixed for the life of the trace file.
struct format_config_t {
  int      xlen = 64;
  int      verbosity = 0;
  int      pc_digits = 16;  // hex digits of a virtual address, from VLEN
  int      pa_digits = 14;  // hex digits of a physical address, from PLEN
  unsigned hart_id = 0;
};

// One retirement, already decoded and looked up by the tracer. The wide fields
// are spelled the way the DPI hands them over, so they cross into a printf
// without a conversion at every call site.
using trace_u64 = unsigned long long;

// A CSR write, as RVFI reports it: the value after the write.
struct csr_write_t {
  uint16_t  addr = 0;
  trace_u64 value = 0;
  trace_u64 cycle = 0;
  trace_u64 sim_time_ns = 0;
};

// The CSR writes that go with one retirement or trap.
struct csr_writes_t {
  const csr_write_t *made = nullptr;     // by this instruction or trap, in its cycle
  unsigned           n_made = 0;
  const csr_write_t *earlier = nullptr;  // since the last event, by no instruction,
  unsigned           n_earlier = 0;      // such as the entry into an interrupt handler
};

struct retire_info_t {
  trace_u64 cycle = 0;
  trace_u64 sim_time_ns = 0;
  trace_u64 order = 0;
  trace_u64 pc = 0;
  uint32_t insn = 0;
  uint8_t  commit_port = 0;
  uint8_t  priv = 0;
  uint8_t  flags = 0;  // CVA6_TRACE_FLAG_*
  uint8_t  rd_addr = 0;
  uint8_t  rs1_addr = 0;
  uint8_t  rs2_addr = 0;
  trace_u64 rd_wdata = 0;
  trace_u64 rs1_rdata = 0;
  trace_u64 rs2_rdata = 0;
  trace_u64 mem_vaddr = 0;
  trace_u64 mem_paddr = 0;
  trace_u64 mem_wdata = 0;
  trace_u64 mem_rdata = 0;
  uint32_t mem_rmask = 0;
  uint32_t mem_wmask = 0;

  const decoded_t *dec = nullptr;         // never null
  const symbol_t  *sym = nullptr;         // set only when inline annotation is wanted
  const symbol_t  *target_sym = nullptr;  // symbol at the branch or jump target, when annotating
  csr_writes_t     csr;
};

struct trap_info_t {
  trace_u64 cycle = 0;
  trace_u64 sim_time_ns = 0;
  trace_u64 pc = 0;
  trace_u64 cause = 0;
  trace_u64 tval = 0;
  uint32_t insn = 0;
  uint8_t  priv = 0;
  uint8_t  virt = 0;
  uint8_t  is_interrupt = 0;

  const decoded_t *dec = nullptr;  // never null
  csr_writes_t     csr;
};

class formatter_t {
 public:
  virtual ~formatter_t() = default;

  virtual void retire(FILE *f, const retire_info_t &r) = 0;
  virtual void trap(FILE *f, const trap_info_t &t) = 0;

  // Written once when the file is opened. Default: nothing.
  virtual void header(FILE *f) { (void)f; }

  // True for a format meant to be parsed rather than read, where interleaving
  // symbol header lines would corrupt the stream. The tracer suppresses them.
  virtual bool machine_readable() const { return false; }

  // How the disassembly in `retire_info_t::dec` is spelled for this format.
  virtual rv_style_t style() const { return RV_STYLE_LEGACY; }
};

// Returns nullptr for an unknown name. The caller owns the result.
formatter_t *make_formatter(const char *name, const format_config_t &cfg);

// Comma separated list of what make_formatter accepts, for error messages.
const char *formatter_names();

}  // namespace cva6tb_tracer

#endif  // CVA6TB_TRACER_RV_FORMAT_H

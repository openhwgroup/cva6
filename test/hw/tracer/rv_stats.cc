// Copyright 2026 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51
//
// Author: Enrico Zelioli <ezelioli@iis.ee.ethz.ch>

#include "rv_stats.h"

#include <algorithm>
#include <vector>

#include "cva6tb_tracer_dpi.h"

namespace cva6tb_tracer {

namespace {

// count the bits set in a byte mask, which is how many bytes an access moved
unsigned popcount8(uint32_t mask) {
  unsigned n = 0;
  for (unsigned i = 0; i < 8; i++)
    if (mask & (1u << i)) n++;
  return n;
}

void percent(FILE *f, const char *label, uint64_t n, uint64_t total) {
  if (total == 0) return;
  fprintf(f, "  %-24s %12llu  %5.1f%%\n", label, (unsigned long long)n,
          100.0 * (double)n / (double)total);
}

}  // namespace

void stats_t::record(const retire_info_t &r, const symbol_t *sym) {
  const decoded_t &d = *r.dec;

  retired_++;
  if (!have_first_) {
    first_cycle_ = r.cycle;
    have_first_ = true;
  }
  last_cycle_ = r.cycle;

  mode_[(r.priv & 3) | ((r.flags & CVA6_TRACE_FLAG_VIRT) ? 4 : 0)]++;
  if ((r.insn & 0x3u) != 0x3u) compressed_++;

  if (d.is_load) { loads_++; load_bytes_ += popcount8(r.mem_rmask); }
  if (d.is_store) { stores_++; store_bytes_ += popcount8(r.mem_wmask); }
  if (d.is_amo) amos_++;
  if (d.is_csr) csrs_++;
  if (d.is_branch) branches_++;
  if (d.is_jump) jumps_++;

  if (r.flags & CVA6_TRACE_FLAG_BRANCH) {
    resolved_++;
    if (r.flags & CVA6_TRACE_FLAG_TAKEN) taken_++;
    if (r.flags & CVA6_TRACE_FLAG_MISPREDICT) mispredicted_++;
  }

  if (sym) per_symbol_[sym->name]++;
}

void stats_t::record(const trap_info_t &t, const std::string &cause_name) {
  traps_++;
  if (t.is_interrupt) interrupts_++;
  trap_causes_[cause_name]++;
}

void stats_t::report(FILE *f, const format_config_t &cfg) const {
  const uint64_t cycles = have_first_ ? (last_cycle_ - first_cycle_ + 1) : 0;

  fprintf(f, "CVA6 trace statistics\n");
  fprintf(f, "=====================\n\n");

  fprintf(f, "Execution\n");
  fprintf(f, "  %-24s %12llu\n", "instructions", (unsigned long long)retired_);
  fprintf(f, "  %-24s %12llu\n", "cycles spanned", (unsigned long long)cycles);
  if (cycles) fprintf(f, "  %-24s %12.3f\n", "instructions per cycle",
                      (double)retired_ / (double)cycles);
  fprintf(f, "  %-24s %12llu\n", "traps", (unsigned long long)traps_);
  if (interrupts_) fprintf(f, "  %-24s %12llu\n", "of which interrupts",
                           (unsigned long long)interrupts_);
  fprintf(f, "\n");

  fprintf(f, "Mode\n");
  static const char *const names[6] = {"user", "supervisor", "debug", "machine",
                                       "virtual user", "virtual supervisor"};
  for (int i = 0; i < 4; i++) percent(f, names[i], mode_[i], retired_);
  // the virtualised modes exist only under H, so they are shown only if reached
  for (int i = 4; i < 6; i++)
    if (mode_[i]) percent(f, names[i], mode_[i], retired_);
  fprintf(f, "\n");

  fprintf(f, "Instruction mix\n");
  percent(f, "compressed", compressed_, retired_);
  percent(f, "loads", loads_, retired_);
  percent(f, "stores", stores_, retired_);
  percent(f, "atomics", amos_, retired_);
  percent(f, "branches", branches_, retired_);
  percent(f, "jumps", jumps_, retired_);
  percent(f, "csr accesses", csrs_, retired_);
  fprintf(f, "  %-24s %12llu\n", "bytes loaded", (unsigned long long)load_bytes_);
  fprintf(f, "  %-24s %12llu\n", "bytes stored", (unsigned long long)store_bytes_);
  fprintf(f, "\n");

  if (resolved_) {
    fprintf(f, "Branch prediction\n");
    percent(f, "resolved control flow", resolved_, retired_);
    percent(f, "of those taken", taken_, resolved_);
    percent(f, "of those mispredicted", mispredicted_, resolved_);
    fprintf(f, "\n");
  } else {
    fprintf(f, "Branch prediction\n  no resolution reported; the core is built without the\n"
               "  mispredict probe, or its inputs are tied off\n\n");
  }

  if (!trap_causes_.empty()) {
    fprintf(f, "Traps by cause\n");
    for (const auto &kv : trap_causes_)
      fprintf(f, "  %-24s %12llu\n", kv.first.c_str(), (unsigned long long)kv.second);
    fprintf(f, "\n");
  }

  if (!per_symbol_.empty()) {
    std::vector<std::pair<std::string, uint64_t>> top(per_symbol_.begin(), per_symbol_.end());
    std::sort(top.begin(), top.end(), [](const auto &a, const auto &b) {
      if (a.second != b.second) return a.second > b.second;
      return a.first < b.first;
    });
    fprintf(f, "Where the instructions went (%zu symbols, top %zu)\n", per_symbol_.size(),
            std::min<size_t>(top.size(), 15));
    for (size_t i = 0; i < top.size() && i < 15; i++)
      percent(f, top[i].first.c_str(), top[i].second, retired_);
    fprintf(f, "\n");
  }

  fprintf(f, "Configuration\n");
  fprintf(f, "  %-24s %12s\n", "xlen", cfg.xlen == 32 ? "RV32" : "RV64");
  fprintf(f, "  %-24s %12u\n", "hart", cfg.hart_id);
}

}  // namespace cva6tb_tracer

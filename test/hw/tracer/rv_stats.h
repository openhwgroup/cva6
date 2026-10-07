// Copyright 2026 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51
//
// Author: Enrico Zelioli <ezelioli@iis.ee.ethz.ch>
//
// End of run statistics.
//
// A collector watches the same retirements the formatter sees and summarises
// them when the run ends. It is entirely optional: nothing is counted and
// nothing is written unless a report file is configured, and the report goes to
// that file rather than into the trace, so a trace stays a trace.
//
// It observes rather than formats, which keeps it independent of how lines are
// spelled: the same numbers come out whichever output format is in use, and a
// second collector counting something else would hang off the same two record()
// calls without touching the tracer or the formatters.

#ifndef CVA6TB_TRACER_RV_STATS_H
#define CVA6TB_TRACER_RV_STATS_H

#include <cstdint>
#include <cstdio>
#include <map>
#include <string>

#include "rv_format.h"
#include "rv_symbols.h"

namespace cva6tb_tracer {

class stats_t {
 public:
  // `sym` is the symbol covering the pc, or nullptr when none is known; it is
  // what turns the report's profile section on.
  void record(const retire_info_t &r, const symbol_t *sym);
  void record(const trap_info_t &t, const std::string &cause_name);

  bool empty() const { return retired_ == 0 && traps_ == 0; }

  void report(FILE *f, const format_config_t &cfg) const;

 private:
  uint64_t retired_ = 0;
  uint64_t first_cycle_ = 0;
  uint64_t last_cycle_ = 0;
  bool     have_first_ = false;

  // indexed by the mode: U, S, debug, M, then VU and VS, which only a
  // hypervisor configuration ever reaches
  uint64_t mode_[6] = {0, 0, 0, 0, 0, 0};

  uint64_t loads_ = 0, stores_ = 0, amos_ = 0, csrs_ = 0;
  uint64_t load_bytes_ = 0, store_bytes_ = 0;
  uint64_t compressed_ = 0;
  uint64_t branches_ = 0, jumps_ = 0;

  // resolved control flow, which only a core with the mispredict probe reports
  uint64_t resolved_ = 0, taken_ = 0, mispredicted_ = 0;

  uint64_t traps_ = 0, interrupts_ = 0;
  std::map<std::string, uint64_t> trap_causes_;
  std::map<std::string, uint64_t> per_symbol_;
};

}  // namespace cva6tb_tracer

#endif  // CVA6TB_TRACER_RV_STATS_H

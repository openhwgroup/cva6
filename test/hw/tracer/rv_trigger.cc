// Copyright 2026 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51
//
// Author: Enrico Zelioli <ezelioli@iis.ee.ethz.ch>

#include "rv_trigger.h"

#include <cctype>
#include <cstdio>
#include <cstdlib>
#include <cstring>

namespace cva6tb_tracer {

bool condition_t::parse(const char *spec, const symbol_table_t &syms) {
  if (!spec || !*spec) { kind_ = None; return true; }

  if (strncmp(spec, "pc:", 3) == 0) {
    char *end = nullptr;
    const uint64_t v = strtoull(spec + 3, &end, 0);
    if (end == spec + 3) return false;
    kind_ = Pc;
    value_ = v;
    return true;
  }

  if (strncmp(spec, "sym:", 4) == 0) {
    // a symbol trigger fires at the symbol's entry point, so the table is
    // searched by name rather than by address
    const char     *name = spec + 4;
    const symbol_t *s = syms.find(name);
    if (!s) {
      fprintf(stderr, "*** [cva6tb_tracer] ERROR: no symbol named '%s'\n", name);
      return false;
    }
    kind_ = Pc;
    value_ = s->addr;
    return true;
  }

  const char *num = spec;
  if (strncmp(spec, "cycle:", 6) == 0) num = spec + 6;
  if (!isdigit((unsigned char)*num)) return false;
  char *end = nullptr;
  const uint64_t v = strtoull(num, &end, 0);
  if (end == num) return false;
  kind_ = Cycle;
  value_ = v;
  return true;
}

bool condition_t::matches(uint64_t cycle, uint64_t pc) const {
  switch (kind_) {
    case Cycle: return cycle >= value_;
    case Pc:    return pc == value_;
    default:    return false;
  }
}

bool window_t::set_start(const char *spec, const symbol_table_t &syms) {
  if (!start_.parse(spec, syms)) return false;
  if (start_.armed()) open_ = false;  // now it takes a trigger to open
  return true;
}

bool window_t::set_stop(const char *spec, const symbol_table_t &syms) {
  return stop_.parse(spec, syms);
}

bool window_t::active(uint64_t cycle, uint64_t pc) {
  if (!open_ && start_.matches(cycle, pc)) open_ = true;
  if (open_ && stop_.matches(cycle, pc)) {
    open_ = false;
    return false;  // the instruction that stops the window is outside it
  }
  return open_;
}

}  // namespace cva6tb_tracer

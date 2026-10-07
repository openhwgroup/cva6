// Copyright 2026 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51
//
// Author: Enrico Zelioli <ezelioli@iis.ee.ethz.ch>
//
// Start and stop triggers, and the window they delimit.
//
// A window is whatever is switched on between a start condition being met and a
// stop condition being met. The tracer uses one for tracing itself and another
// for symbol annotation, and anything added later can have its own without
// touching this file. Conditions are written as text so the same syntax works
// for every one of them:
//
//   1000          the cycle counter reaches 1000
//   cycle:1000    the same, spelled out
//   pc:0x80000100 the program counter is this address
//   sym:main      the program counter is the entry point of this symbol
//
// A window with no start condition is open from the first instruction; one with
// no stop condition never closes. The instruction that meets the start
// condition is inside the window, the one that meets the stop condition is not.
// Both conditions keep being evaluated, so a pc or symbol trigger reopens the
// window every time execution passes through it.

#ifndef CVA6TB_TRACER_RV_TRIGGER_H
#define CVA6TB_TRACER_RV_TRIGGER_H

#include <cstdint>

#include "rv_symbols.h"

namespace cva6tb_tracer {

class condition_t {
 public:
  // Returns false if the text is malformed or names an unknown symbol.
  bool parse(const char *spec, const symbol_table_t &syms);
  bool armed() const { return kind_ != None; }
  bool matches(uint64_t cycle, uint64_t pc) const;

 private:
  enum kind_t { None, Cycle, Pc };
  kind_t   kind_ = None;
  uint64_t value_ = 0;
};

class window_t {
 public:
  bool set_start(const char *spec, const symbol_table_t &syms);
  bool set_stop(const char *spec, const symbol_table_t &syms);

  // Evaluates both conditions and returns whether this instruction is inside.
  bool active(uint64_t cycle, uint64_t pc);

  // True when neither end is armed, i.e. the window is always open.
  bool unbounded() const { return !start_.armed() && !stop_.armed(); }

 private:
  condition_t start_;
  condition_t stop_;
  bool        open_ = true;  // no start condition means open from the beginning
};

}  // namespace cva6tb_tracer

#endif  // CVA6TB_TRACER_RV_TRIGGER_H

// Copyright 2026 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51
//
// Author: Enrico Zelioli <ezelioli@iis.ee.ethz.ch>
//
// Symbol table for the CVA6 tracer: maps a program counter to the function it
// belongs to, so a trace can be read as `<main+0x24>` rather than a bare
// address.
//
// The table is deliberately separate from both the tracer and the
// disassembler, and is fed by loaders rather than owning any one file format.
// `add_elf` is the only loader today; adding another (an nm dump, a map file, a
// build system manifest) means writing one function that calls `add`, and
// nothing else has to change.
//
// Every loader takes a `bias`, which is added to the addresses it reads. That
// is what makes an image built from several separately linked binaries work:
// load each one's symbols with the bias it was placed at.

#ifndef CVA6TB_TRACER_RV_SYMBOLS_H
#define CVA6TB_TRACER_RV_SYMBOLS_H

#include <cstdint>
#include <string>
#include <vector>

namespace cva6tb_tracer {

struct symbol_t {
  uint64_t    addr;  // first address covered, after bias
  uint64_t    size;  // 0 when the loader does not know it
  std::string name;
};

class symbol_table_t {
 public:
  // Add one symbol. Loaders are expected to go through here.
  void add(uint64_t addr, uint64_t size, const std::string &name);

  // Read the symbol table of an ELF file (32 or 64 bit, little endian) and add
  // its function and label symbols, each shifted by `bias`. Returns the number
  // of symbols added, or -1 if the file could not be opened or is not an ELF.
  int add_elf(const char *path, uint64_t bias = 0);

  // Load a comma separated list of sources, each `path` or `path@<bias>`, where
  // the bias is a C style integer literal. Returns the total number of symbols
  // added, or -1 if any source failed. Whitespace around entries is ignored.
  //
  //   "fw.elf"                       one binary at its link address
  //   "boot.elf,payload.elf@0x80000000"   two, the second placed by hand
  int add_sources(const char *spec);

  // Innermost symbol containing `addr`, or nullptr if none does. A symbol whose
  // size is unknown is taken to extend to the next symbol.
  const symbol_t *lookup(uint64_t addr) const;

  // Exact match by name, for callers that start from a name rather than an
  // address, such as a `sym:` trigger. Returns the lowest address of that name.
  const symbol_t *find(const std::string &name) const;

  bool   empty() const { return syms_.empty(); }
  size_t size() const { return syms_.size(); }

 private:
  void sort_if_needed() const;

  mutable std::vector<symbol_t> syms_;
  mutable bool                  sorted_ = false;
};

}  // namespace cva6tb_tracer

#endif  // CVA6TB_TRACER_RV_SYMBOLS_H

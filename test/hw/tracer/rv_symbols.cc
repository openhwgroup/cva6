// Copyright 2026 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51
//
// Author: Enrico Zelioli <ezelioli@iis.ee.ethz.ch>
//
// Symbol table and its ELF loader. The ELF reading here is deliberately
// minimal and self contained: it walks the section headers, finds the symbol
// table and its string table, and keeps the function and label symbols. There
// is no dependency on libelf, bfd or fesvr.

#include "rv_symbols.h"

#include <algorithm>
#include <cstdio>
#include <cstdlib>
#include <cstring>

namespace cva6tb_tracer {

namespace {

// little endian readers, bounds checked against the end of the image
template <typename T>
bool read_le(const std::vector<uint8_t> &buf, size_t off, T *out) {
  if (off + sizeof(T) > buf.size()) return false;
  T v = 0;
  for (size_t i = 0; i < sizeof(T); i++) v |= (T)buf[off + i] << (8 * i);
  *out = v;
  return true;
}

bool read_file(const char *path, std::vector<uint8_t> &buf) {
  FILE *f = fopen(path, "rb");
  if (!f) return false;
  fseek(f, 0, SEEK_END);
  const long n = ftell(f);
  fseek(f, 0, SEEK_SET);
  if (n <= 0) { fclose(f); return false; }
  buf.resize((size_t)n);
  const size_t got = fread(buf.data(), 1, buf.size(), f);
  fclose(f);
  return got == buf.size();
}

// What one section header tells us that we care about.
struct section_t {
  uint32_t type = 0;
  uint64_t flags = 0;
  uint64_t offset = 0;
  uint64_t size = 0;
  uint32_t link = 0;
  uint64_t entsize = 0;
  bool     is_code() const {  // SHF_ALLOC | SHF_EXECINSTR
    return (flags & 0x2) && (flags & 0x4);
  }
};

// A name is worth keeping if it belongs to code: functions, plus untyped
// symbols, which is what hand written assembly labels such as _start are. The
// section has to be one that is loaded and executed, which drops the many
// symbols that live in debug sections, and names beginning with '$' are RISC-V
// mapping symbols describing the ISA of a region rather than labelling it.
bool keep_symbol(uint8_t info, uint16_t shndx, const char *name,
                 const std::vector<section_t> &sections) {
  const uint8_t type = info & 0xF;
  if (type != 2 /* STT_FUNC */ && type != 0 /* STT_NOTYPE */) return false;
  if (shndx == 0 /* SHN_UNDEF */ || shndx >= 0xFF00 /* reserved, e.g. SHN_ABS */) return false;
  if (shndx >= sections.size() || !sections[shndx].is_code()) return false;
  return name && name[0] != '\0' && name[0] != '$';
}

// trim leading and trailing whitespace
std::string trim(const std::string &s) {
  size_t b = 0, e = s.size();
  while (b < e && isspace((unsigned char)s[b])) b++;
  while (e > b && isspace((unsigned char)s[e - 1])) e--;
  return s.substr(b, e - b);
}

}  // namespace

void symbol_table_t::add(uint64_t addr, uint64_t size, const std::string &name) {
  syms_.push_back(symbol_t{addr, size, name});
  sorted_ = false;
}

int symbol_table_t::add_elf(const char *path, uint64_t bias) {
  std::vector<uint8_t> buf;
  if (!read_file(path, buf) || buf.size() < 64) return -1;
  if (memcmp(buf.data(), "\x7F" "ELF", 4) != 0) return -1;

  const bool is64 = buf[4] == 2;
  if (buf[5] != 1) return -1;  // big endian images are not produced for RISC-V

  // section header table location, whose layout differs between the two classes
  uint64_t shoff = 0;
  uint16_t shentsize = 0, shnum = 0;
  if (is64) {
    if (!read_le<uint64_t>(buf, 0x28, &shoff)) return -1;
    if (!read_le<uint16_t>(buf, 0x3A, &shentsize)) return -1;
    if (!read_le<uint16_t>(buf, 0x3C, &shnum)) return -1;
  } else {
    uint32_t off32 = 0;
    if (!read_le<uint32_t>(buf, 0x20, &off32)) return -1;
    shoff = off32;
    if (!read_le<uint16_t>(buf, 0x2E, &shentsize)) return -1;
    if (!read_le<uint16_t>(buf, 0x30, &shnum)) return -1;
  }

  // first pass: remember every section header, so symbols can be filtered by
  // the section they live in
  std::vector<section_t> sections((size_t)shnum);
  for (uint16_t i = 0; i < shnum; i++) {
    const size_t sh = (size_t)shoff + (size_t)i * shentsize;
    section_t   &sec = sections[i];
    if (is64) {
      uint32_t t = 0, l = 0;
      if (!read_le<uint32_t>(buf, sh + 0x04, &t)) return -1;
      if (!read_le<uint64_t>(buf, sh + 0x08, &sec.flags)) return -1;
      if (!read_le<uint64_t>(buf, sh + 0x18, &sec.offset)) return -1;
      if (!read_le<uint64_t>(buf, sh + 0x20, &sec.size)) return -1;
      if (!read_le<uint32_t>(buf, sh + 0x28, &l)) return -1;
      if (!read_le<uint64_t>(buf, sh + 0x38, &sec.entsize)) return -1;
      sec.type = t;
      sec.link = l;
    } else {
      uint32_t t = 0, fl = 0, o = 0, sz = 0, l = 0, e = 0;
      if (!read_le<uint32_t>(buf, sh + 0x04, &t)) return -1;
      if (!read_le<uint32_t>(buf, sh + 0x08, &fl)) return -1;
      if (!read_le<uint32_t>(buf, sh + 0x10, &o)) return -1;
      if (!read_le<uint32_t>(buf, sh + 0x14, &sz)) return -1;
      if (!read_le<uint32_t>(buf, sh + 0x18, &l)) return -1;
      if (!read_le<uint32_t>(buf, sh + 0x24, &e)) return -1;
      sec.type = t; sec.flags = fl; sec.offset = o; sec.size = sz; sec.link = l; sec.entsize = e;
    }
  }

  // second pass: walk each symbol table, naming code addresses
  int added = 0;
  for (const section_t &sec : sections) {
    if (sec.type != 2 /* SHT_SYMTAB */ || sec.entsize == 0) continue;
    if (sec.link >= sections.size()) continue;
    const section_t &str = sections[sec.link];
    if (str.offset + str.size > buf.size()) continue;

    for (uint64_t off = 0; off + sec.entsize <= sec.size; off += sec.entsize) {
      const size_t sym = (size_t)sec.offset + (size_t)off;
      uint32_t st_name = 0;
      uint64_t st_value = 0, st_size = 0;
      uint8_t  st_info = 0;
      uint16_t st_shndx = 0;
      if (is64) {
        if (sym + 0x18 > buf.size()) break;
        if (!read_le<uint32_t>(buf, sym + 0x00, &st_name)) break;
        st_info = buf[sym + 0x04];
        if (!read_le<uint16_t>(buf, sym + 0x06, &st_shndx)) break;
        if (!read_le<uint64_t>(buf, sym + 0x08, &st_value)) break;
        if (!read_le<uint64_t>(buf, sym + 0x10, &st_size)) break;
      } else {
        uint32_t v = 0, z = 0;
        if (sym + 0x10 > buf.size()) break;
        if (!read_le<uint32_t>(buf, sym + 0x00, &st_name)) break;
        if (!read_le<uint32_t>(buf, sym + 0x04, &v)) break;
        if (!read_le<uint32_t>(buf, sym + 0x08, &z)) break;
        st_info = buf[sym + 0x0C];
        if (!read_le<uint16_t>(buf, sym + 0x0E, &st_shndx)) break;
        st_value = v; st_size = z;
      }
      if (str.offset + st_name >= buf.size()) continue;
      const char *name = (const char *)buf.data() + str.offset + st_name;
      if (!keep_symbol(st_info, st_shndx, name, sections)) continue;
      add(st_value + bias, st_size, name);
      added++;
    }
  }
  return added;
}

int symbol_table_t::add_sources(const char *spec) {
  if (!spec || !*spec) return 0;
  int  total = 0;
  const std::string all(spec);
  size_t pos = 0;
  while (pos <= all.size()) {
    const size_t comma = all.find(',', pos);
    const std::string entry = trim(all.substr(pos, comma == std::string::npos ? std::string::npos
                                                                              : comma - pos));
    pos = (comma == std::string::npos) ? all.size() + 1 : comma + 1;
    if (entry.empty()) continue;

    // "path" or "path@<bias>"
    std::string path = entry;
    uint64_t    bias = 0;
    const size_t at = entry.rfind('@');
    if (at != std::string::npos) {
      path = trim(entry.substr(0, at));
      bias = strtoull(entry.c_str() + at + 1, nullptr, 0);
    }
    const int n = add_elf(path.c_str(), bias);
    if (n < 0) {
      fprintf(stderr, "*** [cva6tb_tracer] ERROR: cannot read symbols from '%s'\n", path.c_str());
      return -1;
    }
    total += n;
  }
  return total;
}

void symbol_table_t::sort_if_needed() const {
  if (sorted_) return;
  std::sort(syms_.begin(), syms_.end(), [](const symbol_t &a, const symbol_t &b) {
    if (a.addr != b.addr) return a.addr < b.addr;
    // at the same address prefer the one that knows its size
    return a.size > b.size;
  });
  sorted_ = true;
}

const symbol_t *symbol_table_t::find(const std::string &name) const {
  sort_if_needed();  // sorted by address, so this returns the lowest one
  for (const symbol_t &s : syms_)
    if (s.name == name) return &s;
  return nullptr;
}

const symbol_t *symbol_table_t::lookup(uint64_t addr) const {
  if (syms_.empty()) return nullptr;
  sort_if_needed();
  // last symbol whose address is <= addr
  auto it = std::upper_bound(syms_.begin(), syms_.end(), addr,
                             [](uint64_t a, const symbol_t &s) { return a < s.addr; });
  if (it == syms_.begin()) return nullptr;
  --it;
  // a known size bounds the symbol; an unknown one runs to the next symbol,
  // which is what upper_bound already gave us
  if (it->size != 0 && addr >= it->addr + it->size) return nullptr;
  return &*it;
}

}  // namespace cva6tb_tracer

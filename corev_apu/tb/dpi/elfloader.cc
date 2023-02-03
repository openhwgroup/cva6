#include <fesvr/elf.h>
#include <fesvr/memif.h>

#include <svdpi.h>

#include <cstring>
#include <string>
#include <sys/stat.h>
#include <fcntl.h>
#include <sys/mman.h>
#include <assert.h>
#include <unistd.h>
#include <stdlib.h>
#include <stdio.h>
#include <vector>
#include <map>
#include <iostream>

#define SHT_PROGBITS 0x1
#define SHT_GROUP 0x11

// Name of the ELF file (NULL if not loaded yet or invalid)
const char *loaded_filename = NULL;

// address and size
std::vector<std::pair<reg_t, reg_t>> sections;
std::map<std::string, uint64_t> symbols;
// memory based address and content
std::map<reg_t, std::vector<uint8_t>> mems;
reg_t entry;
int section_index = 0;

void write (uint64_t address, uint64_t len, uint8_t* buf) {
    uint64_t datum;
    std::vector<uint8_t> mem;
    for (int i = 0; i < len; i++) {
        mem.push_back(buf[i]);
    }
    mems.insert(std::make_pair(address, mem));
}

extern "C" void read_elf(const char *);

// Return the value of symbol 'tohost' if present in symbol table,
// and NULL otherwise.
extern "C" unsigned long int dtm_get_tohost_addr(const char *filename)
{
  // Read the file if not already done: we may have been called from an 'initial'
  // block of RVFI_TRACER before actual memory preload starts.
  if (!loaded_filename)
    read_elf(filename);
  else if (strcmp(filename, loaded_filename)) {
    std::cerr << "*** Disctinct, multiple PRELOAD values, exiting!\n";
    exit(1);
  }

  std::cerr << "### Dumping symbol table of '" << filename << "' (size " << symbols.size() << "elts):\n";
  for (auto i : symbols) {
    std::cerr << "### Symbol '" << i.first << "', value = 0x" << std::hex << i.second << std::dec << std::endl;
  }

  if (symbols.count("tohost")) {
    return (unsigned long int) symbols["tohost"];
  } else {
    if (loaded_filename)
      std::cerr << "### Symbol 'tohost' not present in ELF file '" << loaded_filename << "'";
    else
      std::cerr << "### ELF file not loaded";
    std::cerr << "\n### Termination possible only by timeout or Ctrl-C!\n";
    return 0;
  }
}

// Pass exit code of the test to the sim environment.
// The code follows HTIF conventions:
// - code[0]        == 1 ('test result' marker instead of a payload pointer)
// - code[XLEN-1:1] == actual return value of test
extern "C" void dtm_set_exitcode(unsigned long int code)
{
  std::cerr << "### NOT IMPLEMENTED YET: pass return code " << std::dec << code
	    << "(0x" << std::hex << code << std::dec << ") to environment\n";
}

// Communicate the section address and len
// Returns:
// 0 if there are no more sections
// 1 if there are more sections to load
extern "C" char get_section (long long* address, long long* len) {
    if (section_index < sections.size()) {
      *address = sections[section_index].first;
      *len = sections[section_index].second;
      section_index++;
      return 1;
    } else return 0;
}

extern "C" void read_section (long long address, const svOpenArrayHandle buffer) {
    // get actual poitner
    void* buf = svGetArrayPtr(buffer);
    // check that the address points to a section
    assert(mems.count(address) > 0);
    // copy array
    int i = 0;
    for (auto &datum : mems.find(address)->second) {
      *((char *) buf + i) = datum;
      i++;
    }
}

extern "C" void read_elf(const char* filename) {
    // Check if a file of the same name was loaded already
    // and skip loading if that's the case.
    if (loaded_filename && !strcmp(filename, loaded_filename))
      return;

    int fd = open(filename, O_RDONLY);
    struct stat s;
    assert(fd != -1);
    if (fstat(fd, &s) < 0)
        abort();
    // 'filename' designates a valid file.
    loaded_filename = filename;
    size_t size = s.st_size;

    char* buf = (char*)mmap(NULL, size, PROT_READ, MAP_PRIVATE, fd, 0);
    assert(buf != MAP_FAILED);
    close(fd);

    assert(size >= sizeof(Elf64_Ehdr));
    const Elf64_Ehdr* eh64 = (const Elf64_Ehdr*)buf;
    assert(IS_ELF32(*eh64) || IS_ELF64(*eh64));



    std::vector<uint8_t> zeros;
    std::map<std::string, uint64_t> symbols;

    #define LOAD_ELF(ehdr_t, phdr_t, shdr_t, sym_t) do { \
    ehdr_t* eh = (ehdr_t*)buf; \
    phdr_t* ph = (phdr_t*)(buf + eh->e_phoff); \
    entry = eh->e_entry; \
    assert(size >= eh->e_phoff + eh->e_phnum*sizeof(*ph)); \
    for (unsigned i = 0; i < eh->e_phnum; i++) { \
      if(ph[i].p_type == PT_LOAD && ph[i].p_memsz) { \
        if (ph[i].p_filesz) { \
          assert(size >= ph[i].p_offset + ph[i].p_filesz); \
          sections.push_back(std::make_pair(ph[i].p_paddr, ph[i].p_memsz)); \
          write(ph[i].p_paddr, ph[i].p_filesz, (uint8_t*)buf + ph[i].p_offset); \
        } \
        zeros.resize(ph[i].p_memsz - ph[i].p_filesz); \
      } \
    } \
    shdr_t* sh = (shdr_t*)(buf + eh->e_shoff); \
    assert(size >= eh->e_shoff + eh->e_shnum*sizeof(*sh)); \
    assert(eh->e_shstrndx < eh->e_shnum); \
    assert(size >= sh[eh->e_shstrndx].sh_offset + sh[eh->e_shstrndx].sh_size); \
    char *shstrtab = buf + sh[eh->e_shstrndx].sh_offset; \
    unsigned strtabidx = 0, symtabidx = 0; \
    for (unsigned i = 0; i < eh->e_shnum; i++) { \
      unsigned max_len = sh[eh->e_shstrndx].sh_size - sh[i].sh_name; \
      if ((sh[i].sh_type & SHT_GROUP) && strcmp(shstrtab + sh[i].sh_name, ".strtab") != 0 && strcmp(shstrtab + sh[i].sh_name, ".shstrtab") != 0) \
      assert(strnlen(shstrtab + sh[i].sh_name, max_len) < max_len); \
      if (sh[i].sh_type & SHT_PROGBITS) continue; \
      if (strcmp(shstrtab + sh[i].sh_name, ".strtab") == 0) \
        strtabidx = i; \
      if (strcmp(shstrtab + sh[i].sh_name, ".symtab") == 0) \
        symtabidx = i; \
    } \
    if (strtabidx && symtabidx) { \
      char* strtab = buf + sh[strtabidx].sh_offset; \
      sym_t* sym = (sym_t*)(buf + sh[symtabidx].sh_offset); \
      for (unsigned i = 0; i < sh[symtabidx].sh_size/sizeof(sym_t); i++) { \
        unsigned max_len = sh[strtabidx].sh_size - sym[i].st_name; \
        assert(sym[i].st_name < sh[strtabidx].  sh_size); \
        assert(strnlen(strtab + sym[i].st_name, max_len) < max_len); \
        symbols[strtab + sym[i].st_name] = sym[i].st_value; \
      } \
    } \
    } while(0)

  if (IS_ELF32(*eh64))
    LOAD_ELF(Elf32_Ehdr, Elf32_Phdr, Elf32_Shdr, Elf32_Sym);
  else
    LOAD_ELF(Elf64_Ehdr, Elf64_Phdr, Elf64_Shdr, Elf64_Sym);

  munmap(buf, size);
}

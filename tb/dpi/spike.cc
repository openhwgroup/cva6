#include <fesvr/elf.h>
#include <fesvr/memif.h>

#include "sim_spike.h"
#include "msim_helper.h"

#include <vpi_user.h>
#include "svdpi.h"

#include <stdio.h>
#include <stdlib.h>
#include <vector>
#include <string>
#include <memory>
#include <sys/mman.h>
#include <sys/stat.h>
#include <fcntl.h>

#include <assert.h>
#include <unistd.h>
#include <map>
#include <iostream>

sim_spike_t* sim;
std::vector<std::pair<reg_t, mem_t*>> mem;
commit_log_t commit_log_val;

#define SHT_PROGBITS 0x1
#define SHT_GROUP 0x11

void write_spike_mem (reg_t address, size_t len, uint8_t* buf) {
    memcpy(mem[0].second->contents() + (address & ~(1 << 31)), buf,len);
}

void read_elf(const char* filename) {
    int fd = open(filename, O_RDONLY);
    struct stat s;
    assert(fd != -1);
    if (fstat(fd, &s) < 0)
    abort();
    size_t size = s.st_size;

    char* buf = (char*)mmap(NULL, size, PROT_READ, MAP_PRIVATE, fd, 0);
    assert(buf != MAP_FAILED);
    close(fd);

    assert(size >= sizeof(Elf64_Ehdr));
    const Elf64_Ehdr* eh64 = (const Elf64_Ehdr*)buf;
    assert(IS_ELF32(*eh64) || IS_ELF64(*eh64));

    std::vector<uint8_t> zeros;

    #define LOAD_ELF(ehdr_t, phdr_t, shdr_t, sym_t) do { \
    ehdr_t* eh = (ehdr_t*)buf; \
    phdr_t* ph = (phdr_t*)(buf + eh->e_phoff); \
    assert(size >= eh->e_phoff + eh->e_phnum*sizeof(*ph)); \
    for (unsigned i = 0; i < eh->e_phnum; i++) { \
      if(ph[i].p_type == PT_LOAD && ph[i].p_memsz) { \
        if (ph[i].p_filesz) { \
          assert(size >= ph[i].p_offset + ph[i].p_filesz); \
          write_spike_mem(ph[i].p_paddr, ph[i].p_filesz, (uint8_t*)buf + ph[i].p_offset); \
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
      } \
    } \
    } while(0)

  if (IS_ELF32(*eh64))
    LOAD_ELF(Elf32_Ehdr, Elf32_Phdr, Elf32_Shdr, Elf32_Sym);
  else
    LOAD_ELF(Elf64_Ehdr, Elf64_Phdr, Elf64_Shdr, Elf64_Sym);

  munmap(buf, size);
}

extern "C" void spike_create(const char* filename, uint64_t dram_base, unsigned int size)
{

    mem = std::vector<std::pair<reg_t, mem_t*>>(1, std::make_pair(reg_t(dram_base), new mem_t(size)));
    // zero out memory
    memset(mem[0].second->contents(), 0, size_t(size));

    read_elf(filename);

    if (!sim) {
      std::vector<std::string> htif_args = sanitize_args();

      sim = new sim_spike_t("rv64imac", 1, mem, htif_args);
    }
}

// advance Spike and get the retired instruction
extern "C" void spike_tick(commit_log_t* commit_log)
{
  commit_log_val = sim->tick(1);
  commit_log->priv = commit_log_val.priv;
  commit_log->pc = commit_log_val.pc;
  commit_log->is_fp = commit_log_val.is_fp;
  commit_log->rd = commit_log_val.rd;
  commit_log->data = commit_log_val.data;
  commit_log->instr = commit_log_val.instr;
  commit_log->was_exception = commit_log_val.was_exception;
}

extern "C" void clint_tick()
{
  sim->clint_tick();
}
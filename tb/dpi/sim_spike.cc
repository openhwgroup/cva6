// See LICENSE for license details.

#include "sim_spike.h"
#include "mmu.h"
#include "dts.h"
#include <map>
#include <iostream>
#include <sstream>
#include <climits>
#include <cstdlib>
#include <cassert>
#include <signal.h>
#include <unistd.h>
#include <sys/wait.h>
#include <sys/types.h>
#include <inttypes.h>

sim_spike_t::sim_spike_t(const char* isa, size_t nprocs,
             std::vector<std::pair<reg_t, mem_t*>> mems,
             const std::vector<std::string>& args)
  : mems(mems), procs(std::max(nprocs, size_t(1))),
  current_step(0), current_proc(0), debug(false), log(true),
    histogram_enabled(false), dtb_enabled(true), remote_bitbang(NULL)
{

  for (auto& x : mems)
    bus.add_device(x.first, x.second);

  debug_mmu = new mmu_t(this, NULL);

  for (size_t i = 0; i < procs.size(); i++) {
    procs[i] = new processor_t(isa, this, i, false);
  }

  clint.reset(new clint_t(procs));
  // we need to bring the clint to a reproducible default value
  clint.get()->reset();
  bus.add_device(CLINT_BASE, clint.get());
  uart.reset(new uart_t());
  bus.add_device(UART_BASE, uart.get());
  make_bootrom();
  set_procs_debug(true);
}

sim_spike_t::~sim_spike_t()
{
  for (size_t i = 0; i < procs.size(); i++)
    delete procs[i];
  delete debug_mmu;
}

commit_log_t sim_spike_t::tick(size_t n)
{
  commit_log_t commit_log;

  reg_t pc = procs[0]->get_state()->pc;
  auto& reg = procs[0]->get_state()->log_reg_write;
  // execute instruction
  procs[0]->step(n);
  int priv = procs[0]->get_state()->last_inst_priv;
  int xlen = procs[0]->get_state()->last_inst_xlen;
  int flen = procs[0]->get_state()->last_inst_flen;

  commit_log.priv = priv;
  commit_log.pc = pc;
  commit_log.is_fp = reg.addr & 1;
  commit_log.rd = reg.addr >> 1;
  commit_log.data = reg.data.v[0];
  commit_log.instr = procs[0]->get_state()->last_insn;
  commit_log.was_exception = procs[0]->get_state()->was_exception;

  return commit_log;
}

void sim_spike_t::clint_tick() {
  clint->increment(1);
}

void sim_spike_t::set_debug(bool value)
{
  debug = value;
}

void sim_spike_t::set_log(bool value)
{
  log = value;
}

void sim_spike_t::set_histogram(bool value)
{
  histogram_enabled = value;
  for (size_t i = 0; i < procs.size(); i++) {
    procs[i]->set_histogram(histogram_enabled);
  }
}

void sim_spike_t::set_procs_debug(bool value)
{
  for (size_t i=0; i< procs.size(); i++)
    procs[i]->set_debug(value);
}

bool sim_spike_t::mmio_load(reg_t addr, size_t len, uint8_t* bytes)
{
  if (addr + len < addr)
    return false;
  return bus.load(addr, len, bytes);
}

bool sim_spike_t::mmio_store(reg_t addr, size_t len, const uint8_t* bytes)
{
  if (addr + len < addr)
    return false;
  return bus.store(addr, len, bytes);
}

void sim_spike_t::make_bootrom()
{
  start_pc = 0x80000000;

  #include "bootrom.h"

  std::vector<char> rom((char*)reset_vec, (char*)reset_vec + sizeof(reset_vec));

  boot_rom.reset(new rom_device_t(rom));
  bus.add_device(DEFAULT_RSTVEC, boot_rom.get());
}

char* sim_spike_t::addr_to_mem(reg_t addr) {
  auto desc = bus.find_device(addr);
  if (auto mem = dynamic_cast<mem_t*>(desc.second))
    if (addr - desc.first < mem->size())
      return mem->contents() + (addr - desc.first);
  return NULL;
}
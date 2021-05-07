// See LICENSE for license details.

#ifndef _RISCV_SPIKE_H
#define _RISCV_SPIKE_H

#include "processor.h"
#include "devices.h"
#include "debug_module.h"
#include "simif.h"
#include <fesvr/htif.h>
#include <fesvr/context.h>
#include <vector>
#include <string>
#include <memory>
#include <thread>

class mmu_t;
class remote_bitbang_t;

typedef struct
{
  char     priv;
  uint64_t pc;
  char     is_fp;
  char     rd;
  uint64_t data;
  uint32_t instr;
  char     was_exception;
} commit_log_t;

// this class encapsulates the processors and memory in a RISC-V machine.
class sim_spike_t : public simif_t
{
public:
  sim_spike_t(const char* isa, size_t _nprocs,
        std::vector<std::pair<reg_t, mem_t*>> mems,
        const std::vector<std::string>& args);
  ~sim_spike_t();

  int init_sim();
  void producer_thread();
  void clint_tick();
  commit_log_t tick(size_t n); // step through simulation
  void set_debug(bool value);
  void set_log(bool value);
  void set_histogram(bool value);
  void set_procs_debug(bool value);
  void set_dtb_enabled(bool value) {
    this->dtb_enabled = value;
  }
  void set_remote_bitbang(remote_bitbang_t* remote_bitbang) {
    this->remote_bitbang = remote_bitbang;
  }
  const char* get_dts() { return dts.c_str(); }
  processor_t* get_core(size_t i) { return procs.at(i); }
  unsigned nprocs() const { return procs.size(); }

private:
  std::vector<std::pair<reg_t, mem_t*>> mems;
  mmu_t* debug_mmu;  // debug port into main memory
  std::vector<processor_t*> procs;
  reg_t start_pc;
  std::string dts;
  std::unique_ptr<rom_device_t> boot_rom;
  std::unique_ptr<clint_t> clint;
  std::unique_ptr<uart_t> uart;
  bus_t bus;
  std::thread t1;

  processor_t* get_core(const std::string& i);
  static const size_t INTERLEAVE = 5000;
  static const size_t INSNS_PER_RTC_TICK = 100; // 10 MHz clock for 1 BIPS core
  static const size_t CPU_HZ = 1000000000; // 1GHz CPU
  size_t current_step;
  size_t current_proc;
  bool debug;
  bool log;
  bool histogram_enabled; // provide a histogram of PCs
  bool dtb_enabled;
  remote_bitbang_t* remote_bitbang;

  // memory-mapped I/O routines
  char* addr_to_mem(reg_t addr);
  bool mmio_load(reg_t addr, size_t len, uint8_t* bytes);
  bool mmio_store(reg_t addr, size_t len, const uint8_t* bytes);
  void proc_reset(unsigned id) {};

  void make_bootrom();

public:

};


#endif
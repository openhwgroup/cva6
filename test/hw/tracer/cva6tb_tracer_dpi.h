// Copyright 2026 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// Description: DPI-C entry points of the CVA6 instruction tracer. The RTL side
//              (corev_apu/tb/tracer/cva6tb_tracer.sv) only samples RVFI and calls
//              these functions; all decoding, formatting and file I/O happens
//              here. Plain C linkage and scalar arguments only, so the same
//              backend works with Verilator, Questa, VCS and Xcelium.

#ifndef CVA6TB_TRACER_DPI_H
#define CVA6TB_TRACER_DPI_H

#ifdef __cplusplus
extern "C" {
#endif

// Open a trace file. Returns a non-negative handle, or -1 if the file could not
// be opened (in which case the tracer silently does nothing).
//   filename  : output file
//   xlen      : 32 or 64, selects RV32/RV64 decoding
//   vlen      : virtual address width, sets the PC / VA column width
//   plen      : physical address width, sets the PA column width
//   verbosity : detail level, 0 to 2, for the formats meant to be read; what
//               each level adds is up to the format, see the README
//   extensions: mask of rv_ext_t, for extensions whose encodings collide with
//               something else (currently only Zcmt)
int cva6tb_tracer_open(const char *filename, int xlen, int vlen, int plen, int verbosity,
                       int extensions);

// Set one option by name. Everything optional is reached through here, so
// adding an option later means handling a new key and forwarding one more
// plusarg, with no change to this interface. Returns 0 on success and -1 on an
// unknown key or a value that could not be parsed.
//
//   "symbols"      comma separated list of ELF files, each optionally
//                  "@<bias>", whose symbols annotate the trace. Setting this is
//                  what turns annotation on; it is off otherwise.
//   "symbol_mode"  "header" (default) prints an objdump style
//                  "<addr> <name>:" line whenever execution enters a different
//                  symbol, "inline" appends "<name+0x..>" to every line,
//                  "both" does both.
//   "format"       output format: trace, legacy, spike, rvfi or binary
//   "stats"        file for the end of run summary; unset means none is kept
//   "start"        trigger opening the trace window, see rv_trigger.h
//   "stop"         trigger closing it
//   "symbol_start" trigger opening the annotation window, same syntax
//   "symbol_stop"  trigger closing it
//
// "symbols" must be set before any trigger that names a symbol.
int cva6tb_tracer_config(int handle, const char *key, const char *value);

// Bits of the `flags` argument of cva6tb_tracer_retire.
#define CVA6_TRACE_FLAG_MISPREDICT 0x1u  // branch was mispredicted
#define CVA6_TRACE_FLAG_TRAP_ENTRY 0x2u  // first instruction of a trap handler
#define CVA6_TRACE_FLAG_INTERRUPT  0x4u  // that trap handler was entered from an interrupt
#define CVA6_TRACE_FLAG_BRANCH     0x8u  // a resolved control flow instruction
#define CVA6_TRACE_FLAG_TAKEN      0x10u // and it was taken
// The instruction ran with the virtualisation bit set, so an S or U privilege
// level means VS or VU. RVFI's mode field is two bits and cannot say this.
#define CVA6_TRACE_FLAG_VIRT       0x20u

// One retired instruction. All values are already zero/sign-extended to 64 bit
// by the RTL side.
void cva6tb_tracer_retire(int handle, unsigned long long cycle, unsigned long long sim_time_ns,
                          unsigned char commit_port, unsigned long long order, unsigned char priv,
                          unsigned char flags, unsigned long long pc, unsigned int insn,
                          unsigned char rd_addr, unsigned long long rd_wdata,
                          unsigned char rs1_addr, unsigned long long rs1_rdata,
                          unsigned char rs2_addr,
                          unsigned long long rs2_rdata, unsigned long long mem_vaddr,
                          unsigned long long mem_paddr, unsigned int mem_rmask,
                          unsigned int mem_wmask, unsigned long long mem_wdata,
                          unsigned long long mem_rdata);

// One trap taken instead of a retirement.
void cva6tb_tracer_trap(int handle, unsigned long long cycle, unsigned long long sim_time_ns,
                        unsigned char priv, unsigned char virt, unsigned long long pc,
                        unsigned int insn, unsigned long long cause, unsigned long long tval,
                        unsigned char is_interrupt);

// One CSR value. With `initial_value` set it is part of the snapshot of every
// CSR taken at the first cycle; otherwise the CSR changed in `cycle`. Changes
// come before the retirements and traps of the same cycle, which is how they
// are attached to the instruction that made them.
void cva6tb_tracer_csr(int handle, unsigned long long cycle, unsigned long long sim_time_ns,
                       unsigned short addr, unsigned long long value,
                       unsigned char initial_value);

// Number of instructions traced so far (for end-of-simulation reporting).
unsigned long long cva6tb_tracer_count(int handle);

// Flush and close. Safe to call more than once.
void cva6tb_tracer_close(int handle);

#ifdef __cplusplus
}
#endif

#endif  // CVA6TB_TRACER_DPI_H

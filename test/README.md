# CVA6 standalone testbench

A self-contained SoC testbench for CVA6, independent from the OpenHW `verif/` flow.
It wraps the core in a minimal AXI/regbus SoC, preloads a program image into simulation
memory and polls an end-of-computation register to decide pass or fail.

Verilator is the default simulator: it is open source, so every flow described here is
reproducible without a license. QuestaSim is supported by the same [Makefile](Makefile) for
those who have access to it.

## Directory layout

| Path | Content |
| --- | --- |
| [hw/](hw/) | Testbench SoC and its peripherals (SystemVerilog) |
| &nbsp;&nbsp;&nbsp;&nbsp;[bootrom/](hw/bootrom/) | Boot ROM sources and the generated `cva6tb_bootrom.sv` |
| &nbsp;&nbsp;&nbsp;&nbsp;[tracer/](hw/tracer/) | RVFI instruction tracer and its DPI backend |
| [sw/](sw/) | Bare-metal test programs, support library and linker script |
| &nbsp;&nbsp;&nbsp;&nbsp;[deps/](sw/deps/) | External sources fetched on demand (`printf`, `riscv-tests`, `riscv-hyp-tests`, `riscv-arch-test`, Sail) and their patches |
| &nbsp;&nbsp;&nbsp;&nbsp;[include/](sw/include/) | Headers of the support library and inline CSR helpers |
| &nbsp;&nbsp;&nbsp;&nbsp;[lib/](sw/lib/) | Support library sources: startup code, console driver, CLIC helpers |
| &nbsp;&nbsp;&nbsp;&nbsp;[link/](sw/link/) | Linker script: memory regions and peripheral base addresses |
| &nbsp;&nbsp;&nbsp;&nbsp;[tests/](sw/tests/) | Test programs, one binary per `.c`/`.S` file |
| [util/](util/) | Boot ROM generator, ACT generation, regression runners for the tests in `sw/`, `riscv-tests` and the ACTs, spike log comparison, binary trace reader and Perfetto export |
| [verilator/](verilator/) | Verilator build directory and simulation logs |
| [vsim/](vsim/) | QuestaSim build directory, simulation logs and wave scripts |

## Prerequisites

- [Bender](https://github.com/pulp-platform/bender) 0.30 or later, for dependency and file list handling
- `riscv64-unknown-elf-` GCC 14 or later (override the search path with `RV_BINROOT`)
- [Verilator](https://github.com/verilator/verilator) 5.042 or later (`VERILATOR` sets the command)
- Optionally QuestaSim (`QUESTA` sets a prefix for its commands, such as a wrapper that sets it up)
- Python 3.12 for the hardware generators; the environment is pinned with
  [uv](https://docs.astral.sh/uv/) (see [pyproject.toml](pyproject.toml)) — run `uv sync`
  in this directory and activate `.venv` before building

Dependencies must be checked out once from the repository root, along with the HPDCache
submodule that Bender needs in order to parse the root manifest:

```sh
git submodule update --init core/cache_subsystem/hpdcache
bender checkout
```

At IIS, `source util/iis-env.sh` sets up the usual environment, and its header shows how
simulations run there.

## Quick start

```sh
make -C sw all                     # build the test programs under sw/tests
make verilator-build               # elaborate the testbench
make verilator-run HEXFILE=sw/out/hello.hex MAX_CYCLES=100000
```

If you have access to QuestaSim, the flow is symmetric:

```sh
make vsim-build
make vsim-run HEXFILE=sw/out/hello.hex
make vsim-run DEBUG=1               # GUI-friendly: +acc, full signal logging to cva6tb.wlf
```

`make clean` removes both build directories.

### Rebuilding

Neither edits to the RTL sources nor changes to the Makefile variables are detected: the existing
build is considered up to date and the next run simulates the previously elaborated design. Clean
explicitly before rebuilding:

```sh
make verilator-clean
make verilator-build CVA6_CONFIG=cv64a6_imafdchxhclic_sv39_wb
```

(`make vsim-clean` for QuestaSim.)

### Makefile variables

| Variable | Default | Meaning |
| --- | --- | --- |
| `CVA6_CONFIG` | `cv64a6_imafdchsclic_sv39_wb` | CVA6 configuration target passed to Bender; a 64-bit one, with CLIC for the CLIC tests |
| `HEXFILE` | `sw/out/hello.hex` | Verilog hex image to preload |
| `MAX_CYCLES` | `10000` | Simulation timeout in core cycles |
| `MEM_DELAY` | `10` | Main memory delay per AXI channel, 0 to 100, passed as `+MemDelay` |
| `TEST` | `test_simple` | Testbench top (currently the only one) |
| `ZERO_SIM_MEM` | unset | Initialise simulation memories to zero instead of random |
| `TRACER` | `0` | Build in the [instruction tracer](hw/tracer/) (`1` also elaborates `cva6_rvfi`) |
| `LEGACY_TRACE` | `0` | Re-enable CVA6's own built-in tracing (`instr_tracer` under vsim, a `.dasm` dump under Verilator) |
| `WAVES` | `0` | Compile in waveform support; then `+fst` at run time actually dumps |
| `THREADS` | `2` | Verilator threads for the model; use `1` for parallel regressions |
| `SIM_ARGS` | empty | Extra plusargs forwarded to the simulation |
| `TRACE_FORMAT`, `TRACE_FILE`, `TRACE_VERBOSE`, `TRACE_START`, `TRACE_STOP`, `TRACE_STATS`, `TRACE_SYMBOLS` | see [hw/tracer/](hw/tracer/) | Tracer settings, each passed as its plusarg |
| `VERILATOR_JOBS` | `0` | Verilator parallelism (`0` = all cores) |
| `DEBUG` | `0` | QuestaSim only: enable access and waveform logging |

## Testbench structure

[hw/cva6tb_test_simple.sv](hw/cva6tb_test_simple.sv) is the simulation top. It generates the
1 GHz core clock and the 1 MHz RTC, instantiates the SoC, preloads the binary, then polls the
EOC register every cycle until it is set or `MaxCycles` elapses.

[hw/cva6tb_soc.sv](hw/cva6tb_soc.sv) is the device under test: CVA6 as the single AXI master,
an AXI crossbar with four slaves (error slave, regbus bridge, SPM, main memory), and a regbus
demux fanning out to the peripherals. Atomics are handled by `axi_riscv_atomics` in front of
both memories, and main memory sits behind an AXI delayer (a 10-cycle channel delay by default,
set with `+MemDelay`) to emulate realistic latency. Accesses to the uncached DRAM alias at
`0x4000_0000` are remapped onto the cached region before reaching the memory model.

Parameters, types and the address map live in [hw/cva6tb_pkg.sv](hw/cva6tb_pkg.sv).

### Address map

| Region | Base | Size |
| --- | --- | --- |
| AXI error slave | `0x0000_0000` | 64 KiB |
| Boot ROM | `0x0001_0000` | 4 KiB |
| CLINT | `0x0204_0000` | 256 KiB |
| PLIC | `0x0C00_0000` | 64 MiB |
| Platform control registers | `0x1000_0000` | 4 KiB |
| Simulation console | `0x1000_1000` | 4 KiB |
| RTC timer | `0x1000_2000` | 4 KiB |
| CLIC | `0x1004_0000` | 192 KiB |
| SPM | `0x2000_0000` | 1 MiB |
| DRAM (uncached alias) | `0x4000_0000` | 256 MiB |
| DRAM | `0x8000_0000` | 256 MiB |

### Peripherals

- **[cva6tb_regs.sv](hw/cva6tb_regs.sv)** — platform control registers. Offset `0x0` is the
  read-only boot mode; offset `0x4` is the EOC register: bit 0 signals end of computation,
  bits 31:1 carry the return code. Offset `0x8` drives the core's external interrupt lines,
  ORed with the PLIC's: bit 0 the M-mode one, bit 1 the S-mode one, so a test can raise and
  lower them directly.
- **[cva6tb_sim_console.sv](hw/cva6tb_sim_console.sv)** — byte-write character sink. Writes
  are buffered and flushed to stdout as `[CON]` lines on newline.
- **[cva6tb_rtc_timer.sv](hw/cva6tb_rtc_timer.sv)** — RTC-driven 64-bit counter with a compare
  register, wired to both the CLIC and the PLIC.
- **[cva6tb_clk_rst_gen.sv](hw/cva6tb_clk_rst_gen.sv)** — clock and reset generation.
- **CLIC / CLINT / PLIC** — external IPs. Interrupt lines 0–17 (CLIC) and 0–15 (PLIC) are
  reserved for internal sources (`msip`, `mtip`, RTC timer); the remaining lines are exposed
  as SoC inputs and currently tied off.

The PLIC is regenerated from [hw/rv_plic.cfg.hjson](hw/rv_plic.cfg.hjson) and the CLINT from
`clint.mk`; both run automatically as part of the build.

### Boot flow

The testbench reads the first line of the hex image to determine its load address:

- image at `0x2000_0000` → loaded into the SPM, boot mode `1`
- anything else → loaded into main memory, boot mode `0`

The core always resets into the boot ROM ([hw/bootrom/cva6tb_bootrom.S](hw/bootrom/cva6tb_bootrom.S)),
which clears the register file, sets up `sp`/`gp` and a trap handler, reads the boot mode
register and jumps to the corresponding memory. When the program returns, the boot ROM writes
its return code into the EOC register and parks in a `wfi` loop.

Regenerate the boot ROM after editing it with `make bootrom` (`make bootrom-clean` to reset).

### Pass/fail protocol

The testbench passes when the EOC register is set and the return code equals `RetCodeSuccess`
(default `0`); it fails on a mismatching code or on timeout. The result is printed as
`**SIMULATION PASSED**` or `**SIMULATION FAILED**`.

### Simulator plusargs

| Plusarg | Default | Meaning |
| --- | --- | --- |
| `+binary=<path>` | — | Verilog hex image to preload |
| `+MaxCycles=<n>` | `10000` | Cycle timeout |
| `+RetCodeSuccess=<n>` | `0` | Return code that counts as a pass |
| `+MemDelay=<n>` | `10` | Main memory delay per AXI channel, 0 to 100; each channel takes n+2 cycles |

The [instruction tracer](hw/tracer/) adds `+notrace`, `+trace_file=`, `+trace_verbose=`,
`+trace_format=`, `+trace_stats=`, `+trace_start=`, `+trace_stop=`, `+trace_symbols=`, `+trace_symbol_mode=`,
`+trace_symbol_start=` and `+trace_symbol_stop=` when the model is built with `TRACER=1`, the
everyday ones also as the `TRACE_*` variables above.

## Test software

[sw/](sw/) builds every `.c` and `.S` file under [sw/tests/](sw/tests/) into an ELF, a
disassembly and a hex image in `sw/out/`. Programs are linked against `libcva6.a`, built from
[sw/lib/](sw/lib/) (startup code, console driver, CLIC helpers) plus a vendored `printf`, and
placed by [sw/link/link.ld](sw/link/link.ld), which also exports the peripheral base addresses
used by the headers in [sw/include/](sw/include/).

```sh
make -C sw all       # build all tests
make -C sw clean     # remove sw/out
```

[util/run-pulp-tests.sh](util/run-pulp-tests.sh) runs some of them on the model last built for
either simulator, one after the other, which is how the internal CI runs them. It keeps each test's log
in `<simulator>/logs/pulp-tests/` and writes a summary there:

```sh
./util/run-pulp-tests.sh vsim hello clic_simple
./util/run-pulp-tests.sh verilator hello clic_simple
```

## External test suites

`riscv-tests` and `riscv-hyp-tests` are cloned into `sw/deps/` and patched for this platform
on first build:

```sh
make -C sw riscv-tests           # clone, patch and build the ISA tests
make -C sw riscv-hyp-tests       # clone, patch and build the hypervisor tests
```

The ISA regression is driven by [util/run-riscv-tests.sh](util/run-riscv-tests.sh), which runs
the selected tests in parallel on the Verilator binary and summarises the results. It expects a
model with zero-initialised memory, which the `-v` (virtual memory) variants need, and one thread
per simulation since they run in parallel:

```sh
make verilator-build ZERO_SIM_MEM=1 THREADS=1
cd verilator && NJOBS=8 ../util/run-riscv-tests.sh
```

Per-test logs are written to `verilator/logs/`. Note that the suite uses `+RetCodeSuccess=1`,
matching the `riscv-tests` convention.

The hypervisor tests produce a single image that can be run directly:

```sh
make verilator-run HEXFILE=sw/deps/riscv-hyp-tests/build/cva6/rvh_test.hex MAX_CYCLES=2200000
```

### Architectural Certification Tests

[sw/arch-test/](sw/arch-test/) describes this testbench to the
[ACT4 framework](https://github.com/riscv-non-isa/riscv-arch-test), which generates
self-checking ELFs for this core and computes their expected results on the Sail reference
model configured as the core. They cover Zba/Zbb/Zbs, Zcb, Zicond and the privileged corners.

```sh
make -C sw arch-test CVA6_CONFIG=<cfg> ACT_RV_BINROOT=/path/to/riscv-gcc-15/bin   # clones the tests and Sail, then generates
make verilator-build CVA6_CONFIG=<cfg> ZERO_SIM_MEM=1 THREADS=1
NJOBS=8 ./util/run-arch-tests.sh                                                    # runs <cfg>'s ELFs
```

Generation needs a RISC-V GCC 15 or later and a Ruby 3.2 or later with development headers.
Each ELF ends by writing the EOC register, so the testbench's own pass/fail protocol is
the verdict and nothing has to parse a signature. See [sw/arch-test/README.md](sw/arch-test/) for
the requirements, how the DUT is described, and the configurations covered.

## Instruction tracing

Building with `TRACER=1` adds an RVFI driven instruction tracer that writes one line per
retired instruction, in plain text columns meant to be read in an editor:

```sh
make verilator-build TRACER=1
make verilator-run   TRACER=1 HEXFILE=sw/out/hello.hex TRACE_VERBOSE=1
```

The trace is written to `verilator/cva6tb_trace_hart_0.trace`, annotated with the symbol names
of the program's ELF. Tracing and annotation can be narrowed to a window delimited by a cycle
count, a program counter or a symbol:

```sh
make verilator-run TRACER=1 HEXFILE=sw/out/hello.hex TRACE_START=sym:main
```

`TRACE_FORMAT=legacy` writes the format of CVA6's legacy `instr_tracer` instead.
`TRACE_FORMAT=spike` switches the output to spike's own commit log format, which
[util/cmp_spike_trace.py](util/cmp_spike_trace.py) diffs against a real spike run;
`TRACE_FORMAT=rvfi` writes the same information in the spelling the converters under
`verif/sim/` expect; `TRACE_FORMAT=binary` writes fixed size records for tools, read by
[util/read_trace.py](util/read_trace.py). `TRACE_STATS=<path>` adds an end of run summary in a
separate file.

See [hw/tracer/](hw/tracer/) for the output formats, the verbosity levels, the trigger syntax
and what RVFI can and cannot report. The tracer is opt-in
because it also pulls in `cva6_rvfi`; a default build is unaffected.

## Waveforms

Build with `WAVES=1` and pass `+fst` (or `+fst=<file>`) to dump `cva6tb.fst` into
[verilator/](verilator/), viewable with GTKWave or Surfer. Restricting the dump to a subtree
does not work at run time: Verilator's `--binary` mode silently ignores the scope arguments of
`$dumpvars`, so scoping has to be done at build time. On QuestaSim, run with `DEBUG=1` and
load the wave scripts in [vsim/waves/](vsim/waves/):

```tcl
do ../waves/cva6.tcl
do ../waves/clic.tcl
```

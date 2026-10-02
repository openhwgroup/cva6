# RISC-V Architectural Certification Tests

The [ACTs](https://github.com/riscv-non-isa/riscv-arch-test) cover the ISA in breadth —
Zba/Zbb/Zbs, Zcb, Zicond and the privileged corners — and are generated *for one specific DUT*.

ACT4 takes a description of the DUT, selects the tests that apply, computes their expected results
on the [Sail](https://github.com/riscv/sail-riscv) reference model configured to match, and
compiles the answers into self-checking ELFs. Each ELF ends by writing the EOC register, so the
testbench's own pass/fail protocol is the verdict and nothing has to parse a signature.

## Running

```sh
# Ruby >= 3.2 with development headers on PATH (see Tools)
export PATH="<ruby>/bin:$PATH"

CFG=cv64a6_imafdch_sv39_wb
make -C test/sw arch-test CVA6_CONFIG=$CFG ACT_RV_BINROOT=/path/to/riscv-gcc-15/bin
make -C test verilator-build CVA6_CONFIG=$CFG ZERO_SIM_MEM=1 THREADS=1
cd test && NJOBS=8 ./util/run-arch-tests.sh
```

`CVA6_CONFIG` selects both the description to generate for, under `sw/arch-test/<config>/`, and
the model. The runner reads the model's configuration from `verilator/cva6tb.flist` and runs that
configuration's ELFs, so the two cannot disagree. `THREADS=1` suits running many simulations at
once, and `ZERO_SIM_MEM=1` keeps runs reproducible. Per-test logs go to
`verilator/logs/arch-test/`, with `results.txt` filling in during the run and `summary.txt`
written when it ends.

After editing a description, remove `test/sw/deps/riscv-arch-test/work/<config>/`: the framework
tracks its build against the generated test sources, not the description, and would otherwise
reuse ELFs whose expected results came from the old one.

## Tools

`make -C test/sw arch-test` fetches what it needs into `test/sw/deps/`, like the other external
suites:

- **riscv-arch-test** is cloned into `test/sw/deps/riscv-arch-test` and pinned to
  `RISCV_ARCH_TEST_REV`: the framework and its tests move, and a corpus that changes underneath a
  result makes the result meaningless.
- **Sail** comes from the upstream prebuilt release into `test/sw/deps/sail`, which avoids an OCaml
  toolchain. `SAIL_DIR` points at an existing installation instead.

At IIS, generation runs inside the oseda container, as [util/iis-env.sh](../../util/iis-env.sh)
shows. The framework itself also needs the following. `make arch-test` checks the compiler and Ruby before generating, because the
framework only fails much later, from inside a traceback.

| Need | Where it comes from |
| --- | --- |
| RISC-V GCC **15 or later** | `ACT_RV_BINROOT`, defaulting to the GCC on `PATH`. |
| **Ruby ≥ 3.2 with headers** | `PATH`. The UDB gems build native extensions, hence the headers. `rbenv`, `mise` or conda-forge `ruby>=3.2,<4` all work — the Gemfile rejects 4.x |
| **Python** | Not a constraint: the framework runs through `uv`, which provides its own and installs from the framework's lockfile as is, even when older than the framework expects; an inherited `PYTHONPATH` or activated `test/.venv` is dropped for it |

## How the DUT is described

| File | What it says |
| --- | --- |
| `<config>/config.yaml` | The UDB architecture configuration: extensions, XLEN, trap, PMP and counter parameters |
| `<config>/sail.json` | The same core for Sail, plus the memory map from `hw/cva6tb_pkg.sv` |
| `<config>/test_config.yaml` | Which toolchain, which reference model, and where the other files are |
| [link.ld](link.ld) | Where a test is placed: DRAM at `0x8000_0000` (shared by all configurations) |
| [rvmodel_macros.h](rvmodel_macros.h) | How a test prints, how it ends, and how it raises interrupts (shared by all configurations) |

`rvmodel_macros.h` is where this testbench differs most from the upstream examples. There is no
front-end server: a test ends by writing the **EOC register** at `0x1000_0004`, where bit 0 ends
the simulation and bits 31:1 carry the return code — 1 is a pass, 3 a failure. Printing goes to
the simulation console at `0x1000_1000`, a byte at a time, flushed on a newline.

**`config.yaml` and `sail.json` must describe the same machine.** Every expected result is
computed on Sail, so a capability declared in one and missing from the other produces failures
that point somewhere unrelated. When adding a configuration, check every capability in one file
is mirrored in the other.

**Measure WARL behaviour on the DUT.**
[csrprobe.S](../tests/csrprobe.S) writes patterns to every CSR the description depends on and
prints what reads back, or `TRAP` for a CSR the core lacks. Diffing its output between an already
described configuration and a new one shows exactly where their descriptions must differ.
[cboprobe.S](../tests/cboprobe.S) measures the cache-block size and whether `cbo.inval` discards
dirty data, reading memory through the testbench's uncached DRAM alias, and
[lrscprobe.S](../tests/lrscprobe.S) the LR/SC reservation set and whether a store by the same hart
drops the reservation:

```sh
make -C test/sw all
make -C test verilator-run HEXFILE=sw/out/csrprobe.hex MAX_CYCLES=500000
```

## Interrupts

Every configuration declares all six standard interrupts, and the macros raise each in its own way:

| Interrupt | How a test raises it |
| --- | --- |
| Machine timer (MTI) | The CLINT's `mtimecmp` at `0x0204_4000`, against `mtime` at `0x0204_BFF8` |
| Machine software (MSI) | The CLINT's `msip` at `0x0204_0000` |
| Supervisor software and timer (SSI, STI) | Writes to `mip`, whose SSIP and STIP are writable |
| Machine and supervisor external (MEI, SEI) | Bits 0 and 1 of the testbench register at `0x1000_0008`, ORed into the core's external interrupt lines |

The external lines are levels the macros raise and lower directly, like the interrupt generator
ACT gives Sail, and the supervisor one is distinct from the software-writable `mip.SEIP`, as the
tests require. `mtime` counts the testbench's 1 MHz RTC, a tick every 1000 core cycles, so the
macros arm a timer interrupt "soon" 10 ticks ahead. The CLIC configurations run the tests in the
standard interrupt mode (`mtvec` modes 0 and 1), in which the core takes interrupts through `mip`
as without CLIC.

## Configurations

| Configuration | Data cache | Beyond RV64IMAFDC, S, U and Sv39 |
| --- | --- | --- |
| `cv64a6_imafdch_sv39_wb` | write-back | H, B |
| `cv64a6_imafdc_sv39_hpdcache_wb` | HPDcache | B, Zkn, Zicbom |
| `cv64a6_splus` | HPDcache | as above, with superscalar issue |
| `cv64a6_imafdchxhclic_sv39_wb` | write-back | H, CLIC, virtual CLIC |
| `cv64a6_imafdchxhclic_sv39_hpdcache_wb` | HPDcache | as above, with Zicbom |
| `cv64a6_imafdchsclic_sv39_wb` | write-back | H, CLIC |
| `cv64a6_imafdchsclic_sv39_hpdcache_wb` | HPDcache | H, CLIC, Zicbom |

Configurations no probe can tell apart share one description. `cv64a6_splus` differs from
`cv64a6_imafdc_sv39_hpdcache_wb` only in superscalar issue, so its `config.yaml` and `sail.json`
are links to that configuration's and the two get byte-identical tests: any difference in their
results points at the superscalar pipeline. Likewise `cv64a6_imafdchsclic_sv39_wb` links to
`cv64a6_imafdchxhclic_sv39_wb`, and `cv64a6_imafdchxhclic_sv39_hpdcache_wb` to
`cv64a6_imafdchsclic_sv39_hpdcache_wb`: each pair differs only in the virtual CLIC, which is not
visible in any standard CSR.

The CLIC configurations implement the CLIC `mtvec` mode, which UDB cannot express, so the two
tests that check `mtvec`'s reserved mode bit are waived for them.

## Waivers

Failures that come from the framework or the platform rather than the core are listed in
[waivers.txt](waivers.txt), with the configurations they apply to and why. The runner still runs a
waived test: a failure is reported as `WAIVED` and kept out of the verdict, and a pass fails the
run until the line is removed, so a waiver cannot outlive its cause.

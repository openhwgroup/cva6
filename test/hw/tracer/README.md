# CVA6 instruction tracer

Writes one line per retired instruction, driven from the standard **RVFI** interface and usable
under Verilator as well as under event driven simulators.

```
        915ns        905  M  00000000800001a4  e6d70123  sb        a3, -414(a4)                    mem[0x10001000] <- 0x48               a3=0x48 a4=0x1000119e
        915ns        905  M  00000000800001a8  fec799e3  bne       a5, a2, 0x8000019a <main+0xc>   taken                                 a5=0x800001b1 a2=0x800001b6
        918ns        908  M  000000008000019a  0007c683  lbu       a3, 0(a5)                       a3  = 0x65 <- mem[0x800001b1]         a5=0x800001b1
        └─ time      │    │  └─ pc             │         └─ disassembly                            └─ effects                            └─ sources
                     │    └─ mode              └─ encoding
                     └─ cycle
```

The default format, `trace`, is plain text in fixed columns, made to be read in an editor. Other
formats reproduce the legacy
[`common/local/util/instr_tracer.sv`](../../../common/local/util/instr_tracer.sv), write spike's
commit log, or write fixed size records for tools; see *Output formats*.

## How it is put together

| File | Role |
| --- | --- |
| [cva6tb_tracer.sv](cva6tb_tracer.sv) | Samples RVFI at commit and calls the DPI backend. No strings, classes or queues. |
| [cva6tb_tracer_dpi.h](cva6tb_tracer_dpi.h) | The DPI-C interface between the two halves. |
| [cva6tb_tracer.cc](cva6tb_tracer.cc) | Formats and writes the trace; owns the output file. |
| [rv_disasm.h](rv_disasm.h) / [rv_disasm.cc](rv_disasm.cc) | Self-contained RV32/RV64 decoder, with the legacy tracer's spelling. |
| [rv_disasm_spike.cc](rv_disasm_spike.cc) | The same instructions spelled as spike-dasm spells them. |
| [rv_format.h](rv_format.h) / [rv_format.cc](rv_format.cc) | The output formats and the factory that picks between them. |
| [rv_stats.h](rv_stats.h) / [rv_stats.cc](rv_stats.cc) | Optional end of run summary, written to its own file. |
| [rv_symbols.h](rv_symbols.h) / [rv_symbols.cc](rv_symbols.cc) | Symbol table and its ELF loader. |
| [rv_trigger.h](rv_trigger.h) / [rv_trigger.cc](rv_trigger.cc) | Start/stop conditions and the windows they delimit. |

All decoding, formatting and file I/O live on the C++ side, so the RTL half stays trivial and
the same backend works under Verilator, QuestaSim, VCS and Xcelium. Nothing links against
spike, fesvr or any other external library.

The tracer needs `cva6_rvfi`, which turns the core's `rvfi_probes_o` into RVFI proper. Both are
instantiated in [`cva6tb_soc.sv`](../cva6tb_soc.sv) behind `` `ifdef TARGET_TRACER ``, so a
default build elaborates neither and pays nothing.

## Using it

Tracing is a build-time option, because RVFI generation itself costs simulation time:

```sh
make verilator-build TRACER=1
make verilator-run   TRACER=1 HEXFILE=sw/out/hello.hex
```

The trace lands in `verilator/cva6tb_trace_hart_0.trace`. QuestaSim works the same way
(`make vsim-build TRACER=1`), with the DPI backend compiled by `vlog`.

RV32 configurations work too, with the test software rebuilt for the narrower width:

```sh
make verilator-build CVA6_CONFIG=cv32a6_imac_sv32 TRACER=1
make -C sw clean && make -C sw $PWD/sw/out/hello.hex \
  SW_FLAGS="-DOT_PLATFORM_RV32 -march=rv32imac_zicsr_zifencei -mabi=ilp32 -mstrict-align -O2 \
            -Wall -Wextra -static -ffunction-sections -ffreestanding -fdata-sections"
```

Runtime behaviour is controlled with plusargs. With make, the everyday ones are variables named
after them, and `SIM_ARGS` passes any plusarg; it comes first on the command line, so it takes
priority:

| Plusarg | Make variable | Default | Meaning |
| --- | --- | --- | --- |
| `+notrace` | | — | Disable tracing in a build that has it compiled in |
| `+trace_file=<path>` | `TRACE_FILE` | `cva6tb_trace_hart_0.trace` | Output file; `.bin` for `binary`, `.txt` for the other formats |
| `+trace_format=<name>` | `TRACE_FORMAT` | `trace` | `trace`, `legacy`, `spike`, `rvfi` or `binary`, see *Output formats* |
| `+trace_verbose=<n>` | `TRACE_VERBOSE` | `0` | Detail level, see below |
| `+trace_stats=<path>` | `TRACE_STATS` | off | Write an end of run summary here |
| `+trace_start=<trigger>` | `TRACE_START` | open from the start | Open the trace window |
| `+trace_stop=<trigger>` | `TRACE_STOP` | never closes | Close it |
| `+trace_symbols=<elf>[,…]` | `TRACE_SYMBOLS` | off; with make, the program's ELF outside `legacy` | Annotate with symbol names, see *Symbol annotation* |
| `+trace_symbol_mode=<mode>` | | `header` | `header`, `inline` or `both` |
| `+trace_symbol_start=<trigger>` | | open from the start | Open the annotation window |
| `+trace_symbol_stop=<trigger>` | | never closes | Close it |

```sh
make verilator-run TRACER=1 HEXFILE=sw/out/hello.hex TRACE_VERBOSE=1
```

The simulation runs in `verilator/`. The Makefile makes the files it passes absolute; a file
named in `SIM_ARGS` is given as an absolute path, `$PWD/...` from `test/`.

### In another testbench

The tracer does not depend on this testbench, so an SoC that embeds CVA6 can put it in its own
one. One Bender target is needed and it is not `cva6tb`:

```sh
bender script ... -t tracer        # core/cva6_rvfi.sv and test/hw/tracer/cva6tb_tracer.sv
```

`-t cva6tb` would additionally compile `test/hw/cva6tb_*.sv` and make this testbench's
dependencies — its CLINT, its CLIC — relevant to the integrator, for nothing.

Bender does not know about the DPI backend, so the simulator needs it listed by hand. It is the
C++ in [this directory](.), and it needs C++17:

```sh
vlog -ccflags "-std=c++17 -O2" <cva6>/test/hw/tracer/*.cc
verilator ... <cva6>/test/hw/tracer/*.cc
```

Two modules are instantiated per core, in this order, both parameterised with the same
`CVA6Cfg` and RVFI types the core was. [`cva6tb_soc.sv`](../cva6tb_soc.sv) is the worked example:

- **`cva6_rvfi`** turns the core's `rvfi_probes_o` into the retirement records, and is the one
  that costs simulation time. Its `rvfi_instr_o` and `rvfi_csr_o` go to the tracer; its
  `rvfi_to_iti_o` carries the trap `tval` and the branch outcome, which are not in RVFI itself.
- **`cva6tb_tracer`** takes those four, and `HartId`, which must be set per core: it is what
  names the default output file, so two cores sharing it would write over each other.

Nothing else is needed — no clock other than the core's, no reset sequencing beyond `rst_ni`,
and no file handling: `cva6tb_tracer` reads its plusargs and opens its output itself, at time
zero, and closes it at `$finish`.

### Triggers

Anything that can be switched on and off is delimited by a *window*, and every window takes the
same kind of trigger at each end:

| Trigger | Fires when |
| --- | --- |
| `1000` or `cycle:1000` | the cycle counter reaches 1000 |
| `pc:0x80000100` | the program counter is this address |
| `sym:main` | the program counter is this symbol's entry point |

The instruction meeting the start condition is inside the window; the one meeting the stop
condition is not. Both ends keep being evaluated, so a `pc:` or `sym:` trigger reopens the
window every time execution passes through it — which is what you want for tracing every call
to a function. A window with no start trigger is open from the first instruction, and one with
no stop trigger never closes.

```sh
# from the first instruction of main on
make verilator-run TRACER=1 HEXFILE=sw/out/hello.hex TRACE_START=sym:main
```

The closing summary reports how much was traced when a window was in play:
`41 instructions traced of 125 retired`.

### Symbol annotation

Off unless `+trace_symbols=` names at least one ELF file. With make it is on: `TRACE_SYMBOLS`
names the program's own ELF, beside `HEXFILE`, and the boot ROM's once that has been built,
except in the `legacy` format, which stays byte compatible with the old logs. It takes a space
separated list in their place, and `TRACE_SYMBOLS=` turns annotation off. Each
source may be written `<path>@<bias>`, and the bias is added to every address it contributes —
which is how an image assembled from several separately linked binaries is handled: name each
one with the address it was actually placed at.

```sh
TRACE_SYMBOLS="sw/out/hello.elf sw/out/loader.elf@0x80100000"
```

`header` mode, the default, prints an objdump style line whenever execution enters a different
symbol and leaves the instruction lines untouched:

```
000000008000018e <main>:
        873ns        863  M  000000008000018e  00000797  auipc     a5, 0x0                         a5  = 0x8000018e
```

`inline` mode appends `<name+0x..>` to every line instead, and `both` does the two together. In
the `trace` format, branch and jump targets are named as well while annotation is on.

Only code symbols are kept: `STT_FUNC` and untyped labels such as `_start`, and only from
sections that are both allocated and executable. That drops the many symbols living in debug
sections, and RISC-V `$xrv64i...` mapping symbols are skipped by name.

Annotation has its own window, so it can be narrowed independently of the trace itself with
`+trace_symbol_start=` and `+trace_symbol_stop=`.

A rejected option — an unreadable ELF, an unknown symbol in a trigger, a misspelled mode —
stops the simulation rather than quietly producing the wrong trace.

### Output formats

`+trace_format=` picks how a line looks. The tracer decides *what* to report — window, symbols,
decode — and a formatter decides how it is spelled, so a new format is one class in
[rv_format.cc](rv_format.cc) and a name in the factory, with nothing else touched.

| Format | Purpose |
| --- | --- |
| `trace` (default) | plain text in fixed columns, meant to be read |
| `legacy` | the format of `instr_tracer.sv`, for diffing against an older `trace_hart_*.log` |
| `spike` | byte for byte what `spike -l --log-commits` writes, for diffing against spike |
| `rvfi` | the same information in `rvfi_tracer.sv`'s spelling, for the `verif/sim/` converters |
| `binary` | fixed size records, for tools rather than for people |

### The trace format

One line per instruction, in these columns: simulation time, cycle, mode, pc, encoding (four
digits for a compressed instruction), disassembly, what the instruction changed, and the
registers it read. The mode is the privilege level and the virtualisation bit together — `M`, `S`,
`U` and `D` for debug mode, and `VS` and `VU` for code running with V set — because the privilege
level alone cannot tell HS from VS or U from VU. Every column before the sources has a fixed
width, with time and cycle right aligned, so the lines align in any editor.

Instruction lines are indented under the symbol headers, which start in column 0, so an editor
can collapse one function at a time. VS Code folds by indentation with no setting; in vim, a
fold expression that starts a fold at every header does it:

```vim
:set foldmethod=expr foldexpr=getline(v:lnum)=~'^[0-9a-f]'?'>1':'='
```

The disassembly is spike's (see *Instruction coverage*), with branch and jump targets written as
addresses, and named when symbols are loaded. The effects are spelled like this:

| Effect | Meaning |
| --- | --- |
| `a0  = 0x2a` | register written, and its new value |
| `a0  = 0x2a <- mem[0x80001000]` | loaded from that address |
| `mem[0x80001000] <- 0x2a` | stored there, at the width of the access |
| `mem[0xffffffc000001000 pa=0x80201000]` | an access whose physical address differs |
| `mtvec = 0x80000100` | CSR written, and its value after the write, see *CSR writes* |
| `taken`, `not taken, mispredicted` | outcome of a conditional branch |
| `mispredicted` | a jump whose target was mispredicted |
| `!! illegal instruction, tval 0x0` | an instruction that trapped instead of retiring, then the CSRs the trap wrote |
| `!! interrupt` | a line of its own, ahead of the first instruction of the handler, then the CSRs the interrupt wrote |
| `!! ecall from U` | an environment call, then the CSRs it wrote |
| `-- mtval = 0x0` | a line of its own: CSRs written in a cycle where nothing retired or trapped |

Values are hex with no leading zeros. The name of a register written is padded to the longest
name of its register file, so the `=` signs line up: `a0  = 0x2a` above `s10 = 0x2a`. Every trap
and interrupt contains `!!`, so a search for it lists them all.

The sources column follows the effects: the registers the instruction read, with their values,
as `a5=0x800001b1 a2=0x800001b6`.

### Commit logs

Both commit log dialects write two lines per instruction: the instruction, then its
architectural effect — privilege, PC, encoding, the register written and its value, and
` mem <addr>` / ` mem <addr> <data>` for loads and stores. The disassembly on the first line is
the one spike-dasm prints, pseudo-instructions and all, so neither needs a spike-dasm pass.

```sh
TRACE_FORMAT=spike
```

```
core   0: 0x0000000080000008 (0x6783031b) addiw   t1, t1, 1656
core   0: 3 0x0000000080000008 (0x6783031b) x6  0x0000000000005678
```

**Why there are two dialects.** They are not interchangeable, and neither is a superset. Real
spike prefixes *both* lines with `core   N: ` and left aligns the register as `x6  0x…`;
`rvfi_tracer.sv` omits the prefix on the effect line and right aligns as `x 6 0x…`. The
converters under `verif/sim/` were written against the second: `verilator_log_to_trace_csv.py`'s
`RD_RE` matches the `rvfi` effect lines and none of the `spike` ones. So use `spike` to diff
against spike, and `rvfi` to feed those scripts.

Traps follow the same split: `spike` writes `core   0: exception trap_illegal_instruction,
epc 0x…`, which is the wording the converters' `ILLE_RE` looks for, while `rvfi` writes
`ILLEGAL_INSTR exception @ 0x<pc> (0x<insn>)`.

In `spike` format the effect line follows spike's rules too: store data at the width of the
access, a `mem` read and a `mem` write for an AMO, a read only for `lr`, a write for `sc` only
when it succeeds, and CSR writes as `c768_mstatus 0x…` records, in spike's order. A trap, an
`ecall` among them, is the disassembly line followed by spike's `exception` line and, for the
causes that have one, its `tval` line.

### CSR writes

CVA6's `cva6_rvfi` keeps a copy of the CSR state alongside RVFI, `rvfi_csr`: for every register
its current value and whether it changed in this cycle. The tracer passes on each change, and
the backend attaches it to the instruction or trap of the same cycle that made it:

- A CSR instruction reports the CSR it names, with its value after the write, even when the
  write left it unchanged; the value is the one the CSR reads back as, WARL fields applied.
- A trap or an `ecall` reports what taking it wrote: `mcause`, `mepc`, `mtval`, `mstatus`.
- An `mret` or `sret` reports `mstatus`, and an FP instruction `fflags` when its flags change it.
- What the entry into an interrupt handler writes happens in a cycle where nothing retires; it
  goes on the `!! interrupt` line of the `trace` format, and with it the cause in `mcause`.

The counters, `mip` and `sip`, `dcsr`, and the views `sstatus`, `sie` and `fcsr` change on their
own or along with another register, so they are reported only when an instruction names them.
With V set, a supervisor CSR instruction writes the virtual supervisor CSR, which is the one
reported.

`rvfi_csr` covers the machine, supervisor, user, FP, debug and PMP registers, the counters, the
hypervisor and virtual supervisor registers, and the CLIC ones. A write to a CSR outside it,
such as `senvcfg`, shows in the instruction only.

Verbosity levels do not apply to either commit log dialect, whose shape is fixed, and symbol
header lines are suppressed for both because they would break a parser reading the stream. The
inline annotation form still works.

### The binary format

`+trace_format=binary` writes a 64 byte header and then one fixed size record per event, little
endian and naturally aligned. There is nothing to parse: a reader checks the header and indexes
into the rest.

```python
import numpy as np
rec = np.dtype([('cycle','<u8'), ('time_ns','<u8'), ('pc','<u8'), ...])
data = np.fromfile('trace.bin', dtype=rec, offset=64)
mispredicted = data[(data['flags'] & 0x09) == 0x09]     # resolved branch that missed
loads        = data[data['class'] & 0x01]               # no decoder needed
```

Each record carries a `class` byte saying what the instruction is — load, store, atomic, CSR,
branch, jump, compressed — written by this tracer's decoder. Without it a consumer would have to
reimplement RISC-V decoding just to count an instruction mix, which is the one thing a trace of
raw encodings cannot answer on its own. With it, a dozen lines of standard library Python
reproduce every number in the statistics report.

[`util/read_trace.py`](../../util/read_trace.py) is the reference reader and documents the
layout field by field; it also converts to CSV and dumps records in a readable form:

```sh
./util/read_trace.py trace.bin --info      # header and record count
./util/read_trace.py trace.bin --csv       # csv on stdout
./util/read_trace.py trace.bin --limit 20  # readable dump
```

Retirements and traps share one record shape, told apart by `kind`; a trap puts its cause and
`tval` in the `rd_wdata` and `rs1_rdata` slots. A CSR write is a record of its own after the
retirement or trap that made it, with the address in `csr` and the value in `rd_wdata`. New
fields keep the offsets of the existing ones and come out of `reserved`, so a reader that checks
`version` and `record_size` keeps working.

### Comparing against spike

[`util/cmp_spike_trace.py`](../../util/cmp_spike_trace.py) diffs a spike commit log against a
trace taken in `spike` format and reports the first place they disagree:

```sh
spike --isa=rv64imac_zicsr -l --log-commits prog.elf > spike.log 2>&1
make verilator-run TRACER=1 HEXFILE=prog.hex TRACE_FORMAT=spike TRACE_FILE=rtl.log
./util/cmp_spike_trace.py spike.log rtl.log
```

The two runs do not start in the same place — spike begins at its own reset vector while the
testbench goes through its boot ROM — so the logs are aligned on the first program counter they
have in common, or on `--start-pc`. Everything is compared: the disassembly, the registers and
memory, and the CSR records, with one allowance. Spike records `fflags` on every instruction
that raises a flag, RVFI only when the value changes, and the flags are sticky; a record that
repeats the value `fflags` already holds is left out on both sides. `--ignore-disasm` and
`--ignore-csr` leave the disassembly and the CSR records out. The script reports where it
aligned the two logs, then either `MATCH` with the number of instructions compared or the first
disagreement, with both sides of the offending instruction:

```
#3 diverges:
  spike 0x0000000080000008 (0x6783031b)  addiw t1, t1, 1656  [x6 0x0000000000005678]
  trace 0x0000000080000008 (0x6783031b)  addiw t1, t1, 1656  [x6 0x000000000000dead]
```

The exit status is 0 when they match, so it drops into a regression script.

One caveat on what this can check: spike and the testbench only agree if the program does not
depend on anything outside the core. The tests under `sw/tests/` write to the EOC register and
the simulation console, which bare spike has no model for, so they diverge as soon as they touch
one. Self contained programs compare cleanly end to end.

### Verbosity levels

`+trace_verbose` adds detail to the two formats meant to be read. In `trace`:

**1** and above — append the commit port and the retire counter as a comment, `# p0 #1161`.
Useful for dual-issue questions.

In `legacy`:

**0** — the legacy layout, nothing else. This is what you want when diffing against an older
`trace_hart_*.log`.

**1** — adds, per line: the data moved by loads and stores (`ST:`/`LD:`), the CSR touched by a
CSR instruction and the value written to it as RVFI reports it (`csr:mtvec <-…`), addresses for AMOs, the outcome
of a resolved branch (`br:taken`, `br:not-taken,mispredicted`), a `<- trap entry` /
`<- interrupt entry` marker on the first instruction of a handler, and a second line under each
trap carrying the short cause name and the raw cause register. A `#` header names the columns.

The branch annotation makes the trace answer branch questions on its own:

```sh
grep -o "br:[a-z,-]*" cva6tb_trace_hart_0.txt | sort | uniq -c   # with TRACE_FORMAT=legacy
   9607 br:not-taken
   1512 br:not-taken,mispredicted
  72853 br:taken
   2951 br:taken,mispredicted
```

**2** — additionally stamps each line with the commit port and the retire counter, `[p0 #1234]`,
between the encoding and the disassembly. Useful for dual-issue questions; not diff compatible.

## End of run statistics

`+trace_stats=<path>` writes a summary when the run ends. It is off unless a path is given, and
it goes to its own file, so the trace stays a trace.

```sh
TRACE_STATS=stats.txt
```

The collector in [rv_stats.cc](rv_stats.cc) *observes* the same retirements the formatter is
handed, rather than reading the formatted text. That keeps the numbers independent of which
output format is in use, and a second collector counting something else hangs off the same two
`record()` calls without touching the tracer or the formatters.

It reports instruction and cycle counts with IPC, the mode split, the instruction mix with
bytes moved, branch and mispredict rates, traps grouped by cause, and — when symbols are loaded
— which of them the instructions went to:

```
Branch prediction
  resolved control flow           86923   23.6%
  of those taken                  75804   87.2%
  of those mispredicted            4463    5.1%

Where the instructions went (38 symbols, top 15)
  vprintfmt.constprop.1           93937   25.5%
  _boot                           67670   18.3%
  hpt_init                        56085   15.2%
```

Statistics cover what was traced, so a window narrows them too. To get a summary without
keeping a trace, point the trace at `/dev/null` and only the summary survives.

## What RVFI cannot tell us

- **Mispredictions** are not part of RVFI. CVA6's branch unit resolves them into `bp_resolve_t`,
  and the branch mispredict probe carries `is_mispredict` on `rvfi_to_iti_t`, alongside
  `branch_valid` and `is_taken`. Leave `branch_valid_i` / `branch_taken_i` /
  `branch_mispredict_i` tied to `'0` and the column reads `0` everywhere.
- **Third source operands.** RVFI reports two source values. For the FMA instructions the third
  one prints as `----------------`. The same fallback covers the few CVA6 instructions whose
  scoreboard operand slots do not line up with the architectural `rs1`/`rs2` — mostly the FP
  ops, where the tracer matches decoded operands against the reported ones by register number
  and falls back to consuming them in order.
- **`tval`.** Not part of RVFI; taken from `cva6_rvfi`'s `rvfi_to_iti_o.tval`, which is
  registered in the same cycle as the RVFI outputs.
- **Floating point flags per instruction.** `rvfi_csr` shows `fflags` when it changes, so an
  instruction that raises a flag already set leaves no record, and when two FP instructions
  retire together the change goes with the first of them.

## Instruction coverage

| Group | Covered |
| --- | --- |
| RV32I / RV64I, M, A, F, D, C | yes |
| Zicsr, Zifencei | yes, with CSR names |
| H (`hlv*`, `hsv*`, `hfence.*`) | yes |
| Zba, Zbb, Zbs, Zbc | yes |
| Zicond (`czero.eqz`, `czero.nez`) | yes |
| Zicbom, Zicboz (`cbo.*`) | yes |
| Zfh (half precision) | yes, via the format field |
| Zcb (`c.lbu`, `c.mul`, `c.zext.*`, …) | yes |
| Zcmt (`cm.jt`, `cm.jalt`) | yes, see below |
| Zkn (`aes*`, `sha*`, `pack*`, `brev8`, `zip`, `xperm*`) | no |
| V (vector) | no |

Zkn is enabled in `cv32a6_imac_sv32` and the `cv64a6_imafdc_sv39*` configurations; until the
decoder learns it, its instructions print as `INVALID`, apart from `clmul` and `clmulh`, which
share Zbc's encodings. Vector needs `vtype`/`vl` tracking to render sensibly.

Unknown encodings print as `INVALID` with the raw word still in the encoding column, so nothing
is silently dropped.

**Two spellings.** Every instruction above can be spelled two ways. `legacy` uses the legacy
tracer's: its columns, its operand order (`csrw t0, mtvec`) and the decompressed operands of a
compressed instruction (`c.j x0, 310`). The `spike` and `rvfi` formats use spike-dasm's: its
pseudo-instructions (`seqz`, `snez`, `sext.w`, `ret`), `zero` for `x0`, operands in assembler
order and pc relative targets (`c.j pc + 310`), and `unknown` for an encoding it does not know.
[rv_disasm_spike.cc](rv_disasm_spike.cc) is a table of the instructions with spike's match,
mask and operands, searched in spike's own order, so a pseudo-instruction wins over its base
instruction exactly where it does in spike. On RV32 it names `rev8`, which spike recognizes by
its RV64 encoding only.

**Zcmt needs a hint.** `cm.jt` and `cm.jalt` occupy the same encoding as `c.fsdsp`, and the two
are mutually exclusive by construction — a configuration has one or the other. The decoder
cannot tell from the instruction word alone, so the SV side passes `CVA6Cfg.RVZCMT` down to the
backend as an extension mask. Zcb needs no such hint because it only uses otherwise reserved
encodings.

CSR names cover every CSR CVA6 implements, named as spike names them, plus the CLIC and CVA6
specific ones spike has no name for, and trap causes cover the hypervisor codes. In CLIC
mode the cause register packs the saved interrupt level and privilege above the exception code;
the tracer masks those off and prints the raw value at verbosity 1.

## Comparing against the legacy tracer

Under QuestaSim the legacy `instr_tracer` can be compiled in alongside this one with
`LEGACY_TRACE=1`, so both write a trace for the same run. With the time and cycle stamps
stripped, the two traces match line for line apart from the differences listed below; the cycle
stamps differ by a constant offset, since the legacy tracer counts from the core's internal reset
and this one from the SoC reset, plus the RVFI register stage.

```sh
make vsim-build TRACER=1 LEGACY_TRACE=1
make vsim-run   TRACER=1 LEGACY_TRACE=1 HEXFILE=sw/out/clic_smode.hex TRACE_FORMAT=legacy
cd vsim/build
grep -vE "^Exception|tval:" trace_hart_0.log | sed -E 's/^ *[0-9]+ns +[0-9]+ //' > legacy.txt
sed -E 's/^ *[0-9]+ns +[0-9]+ //' cva6tb_trace_hart_0.txt > new.txt
diff legacy.txt new.txt
```

## Deliberate differences from the legacy tracer

- `amomaxu.w` / `amomaxu.d` are named correctly; the legacy tracer printed them as `amomax`.
- The RV64M 32-bit forms print as `mulw`, `divw`, `divuw`, `remw`, `remuw`; the legacy tracer
  appended a `w` to every mnemonic in the group and produced names like `mulhw`.
- CSRs the legacy tracer printed as a number, the CLIC ones among them, are printed by name.
- `csrs` and `csrc` are printed for the `rd == x0` forms. The legacy tracer listed both
  mnemonics but its `casez` ordering made the patterns unreachable, so it always said `csrrs`
  and `csrrc`.
- An `ecall` appears as a retired instruction. The legacy tracer printed only the
  `Exception @ ... Environment Call ...` line for it, because CVA6's RVFI reports environment
  calls as retirements.
- Interrupts produce no line at verbosity 0, where the legacy tracer printed
  `Exception @ ... Cause: ... Interrupt`. RVFI reports an interrupt on the *handler's* first
  instruction rather than on the interrupted one, so the tracer marks it there instead, as
  `<- interrupt entry` at verbosity 1. Moving that marker down to verbosity 0 is a one line
  change if the parity matters more than a clean diff.
- Exception lines stamp a plain nanosecond count instead of `%t`-formatted simulation time.
- Mnemonics and operands are derived from the encoding rather than from CVA6 scoreboard state.
  The rendering rules are the legacy ones, oddities included: `c.j` still prints as
  `c.j x0, <offset>` and `c.mv` as `c.mv rd, x0, rs2`, because that is the decompressed form the
  old tracer showed.

<!--
Copyright 2026 Thales France

Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
You may obtain a copy of the License at https://solderpad.org/licenses/

Original Author: Yannick Casamatta (yannick.casamatta@thalesgroup.com)
-->

# CVA6 Command Runner - `cook.py`

A modular command runner to automate and simplify RTL flow execution for the CVA6 RISC-V processor.

## Table of Contents

- [Overview](#overview)
- [Prerequisites](#prerequisites)
- [Installation](#installation)
- [Configuration](#configuration)
- [Build Directory Organization](#build-directory-organization)
- [Project Architecture](#project-architecture)
- [Recipe Reference](#recipe-reference)
  - [Test Patterns](#test-patterns)
  - [Software Compilation](#software-compilation)
  - [RTL Simulation](#rtl-simulation)
  - [Random Test Generation](#random-test-generation)
  - [Synthesis](#synthesis)
  - [Static Analysis](#static-analysis)
  - [Reports](#reports)
  - [Macros](#macros)
  - [Utilities](#utilities)
- [Complete Flow Examples](#complete-flow-examples)
- [Troubleshooting](#troubleshooting)

## Overview

`cook.py` is the main entry point for launching various "recipes" (tasks) in the CVA6 RTL flow. Built on [Typer](https://typer.tiangolo.com/), this modular framework enables you to:

- Compile software programs for CVA6 targets
- Elaborate and simulate RTL
- Run synthesis
- Execute static analysis tools (Spyglass, Verible, Pylint)
- Generate performance and area reports
- Automate complete flows via macros

## Current Status

At the moment, the command runner only provides recipes for the Synopsys tools (VCS, DC_shell, and SpyGlass). Only the UVM testbench is currently supported, with an optional tandem comparison mode against the SPIKE reference model.

### Roadmap

Future developments are planned to include:

- Support for the Questa and Verilator ISSs (MustHave).
- Support for the TestHarness testbench (MustHave).
- FPGA builds
- Documentation generation
- Dependency installation

Ideally, all project operations should be accessible through this single entry point: cook.py.

### Design Philosophy

The philosophy behind cook.py is to provide a single entry point exposing a collection of recipes, where each recipe performs one simple, well-defined task.

Each recipe should execute with the fewest possible dependencies. In particular, it should avoid requiring environment variables, long chains of external tool invocations, or any unnecessary setup. Recipes should remain as self-contained, deterministic, and easy to use & maintains as possible.

## Prerequisites

### CAD Tools

The following Synopsys tools must be installed with binaries accessible in `$PATH`:

- **VCS** - RTL simulation
- **Verdi** - Waveform debugging and trace analysis
- **DC Shell** - Logic synthesis
- **Spyglass** - Static analysis and lint checking

### Generic Tools

- **Black** - Python formator
- **pyLint** - Python static analysis and lint checking

### Verification Tools and Test Suites

- **SPIKE** - RISC-V ISA simulator (reference model for tandem verification)
- **riscv-tests** - Basic ISA tests
- **riscv-arch-test** - Official RISC-V architecture tests
- **riscv-compliance** - Compliance test suite
- **riscv-dv** - Random instruction generator
- **Proxy kernel** - system calls (optional)

## Installation

### Step-by-Step Setup

1. **Clone the repository and initialize submodules**

```bash
git clone https://github.com/openhwgroup/cva6.git
cd cva6
git submodule update --init --recursive
```

2. **Install the RISC-V toolchain**

At least one RISC-V toolchain must be configured (GCC or LLVM/Clang).

It is **strongly recommended** to use the toolchain built with the provided scripts.

Install toolchain build prerequisites
See util/toolchain-builder/README.md for details

Build and install the toolchain
See util/toolchain-builder/README.md for instructions

3. **Install Spike**

To speed up compilation and elaboration, you can set the `NUM_JOBS`

```bash
#Prerequisites (Debian based example)
sudo apt-get install cmake help2man device-tree-compiler
export NUM_JOBS=8  # Use 8 parallel jobs (cmake)
# Install SPIKE (RISC-V ISA simulator)
./verif/regress/install-spike.sh
```

4. **Install external git dependencies(Optional)**

Some git dependencies are not in submodules and must be cloned by manually.

```bash
# Install external git dependencies (mostly test suites)
./cook.py git-dependencies
```

5. **RISC-V Proxy Kernel (Optional)**

For simulations requiring system calls (e.g., printf in C programs), you can install the RISC-V proxy kernel:

```bash
./verif/regress/install-pk.sh
```

The proxy kernel acts as a lightweight service layer to handle system calls in bare-metal simulations.

## cook.py configuration

### Python Environment

**Python 3.9 or later**
**Required Python packages:**
- `typer` (≥0.9.0) - CLI framework with type hints
- `rich` (≥13.0.0) - Rich text formatting and beautiful terminal output
- `pyyaml` (≥6.0) - YAML configuration file parsing
- `plotly` (≥5.0.0) - Interactive data visualizations and charts

Install dependencies via pip:

```bash
pip3 install -r flows/requirements.txt
```

### Configuration Files

Configuration files are located in `flows/config/`:

- **`compiler.yml`** - Toolchain configurations (required)
- **`techno.yml`** - Technology libraries for synthesis
- **`dependencies.yml`** - External git repositories


### Custom Configuration Directory

By default, `cook.py` uses files in `flows/config/`. You can specify a custom configuration directory:

```bash
export CONFIG_DIR=/path/to/your/config
```

### Compiler Configuration (`compiler.yml`)

**This file must be adapted to your environment.**

Example configuration:

```yaml
# LLVM 20 configuration
llvm-20-1-8:
    TOOLS_PATH: "/opt/riscv/llvm-20"
    CLANG: "riscv32-unknown-elf-clang"
    GCC: None
    OBJDUMP: "riscv32-unknown-elf-objdump"
    NM: "riscv32-unknown-elf-nm"
    TARGET_TOOLCHAIN: "riscv32-unknown-elf"

# GCC 14 configuration
gcc-14:
    TOOLS_PATH: "/opt/riscv/gcc-14"
    CLANG: None
    GCC: "riscv32-unknown-elf-gcc"
    OBJDUMP: "riscv32-unknown-elf-objdump"
    NM: "riscv32-unknown-elf-nm"
    TARGET_TOOLCHAIN: "riscv32-unknown-elf"
```

**Notes:**
- `TOOLS_PATH`: Directory containing the toolchain
- Set `None` for `GCC` if using Clang, and vice versa
- Configuration name (e.g., `llvm-20-1-8`) is used with `-c` option in commands

### Techno Configuration (`techno.yml`)

**This file must be adapted to your environment.**

Example configuration:

```yaml
# MyTechno configuration
MyTechno:
    NAND2_AREA: "100"
    FOUNDRY_PATH: "/tmp/PDK/TECH1/STDCELLS/TECHNAME"
    LIB_NAME: "libname"
    TECH_NAME: "techname"
    CORNER_SYNTH: "corner_synth"
    SCENARIO_SYNTH_NAME: "wc_timing"
    CORNER_POWER: "corner_power"
    SCENARIO_POWER_NAME: "wc_power"
    LIB_VERILOG: "/tmp/PDK/TECH1/verilog/beh.v"
    FOUNDRY_RAM_PATH: ""

```

## Build Directory Organization

The `build/` directory is structured as follows:

```
build/
├── <target>/                    # e.g., cv32a60x, cv32a65x
│   ├── compile/                 # Software compilation outputs
│   │   └── <test name>/          # e.g., hello-world, coremark
│   │       ├── compile.log
│   │       ├── <test>.elf       # Executable binary
│   │       ├── <test>.dump      # Disassembly
│   │       ├── <test>.size      # Size report
│   │       └── isa_string       # ISA configuration
│   ├── elab/                    # RTL elaboration
│   │   └── <compilation mode>/  # e.g., sim_rtl
│   │       ├── compilation.log
│   │       ├── simv             # Simulation executable
│   │       └── ...
│   ├── simulation/              # Simulation results
│   │   └── <compilation mode>/  # e.g., sim_rtl
│   │       └── <test name>/     # e.g., hello-world
│   │           ├── vcs.log
│   │           ├── trace_hart_0.log
│   │           └── ...
│   ├── synthesis/               # Synthesis results
│   │   ├── build_config.yaml
│   │   └── ...
│   └── verible/                 # RTL formatting
│       └── verible-cmd.log
```

**Structure:**
- Each **target** (CVA6 configuration) has its own directory
- Each **recipe** has a working directory inside the target
- Results are organized by task type (compile, simulation, synthesis, etc.)

## Cook.py Architecture

```
CVA6_ROOT_DIR/
├── cook.py                      # Main entry point
├── flows/
│   ├── recipes/                 # Main recipes
│   │   ├── sw_compile.py
│   │   ├── vcs_uvm_comp.py
│   │   ├── vcs_uvm_run.py
│   │   ├── dc_shell_synth.py
│   │   └── ...
│   ├── patterns/                # Pre-configured basic tests
│   │   ├── hello_world.py
│   │   ├── coremark.py
│   │   └── dhrystone.py
│   ├── report_scripts/          # Report generation scripts
│   ├── macros/                  # Multi-recipe automation
│   ├── utils/                   # Helper functions
│   │   ├── config_loader.py
│   │   ├── report_builder.py
│   │   └── utils.py
│   └── config/                  # Configuration (customize for your env)
│       ├── compiler.yml         # Toolchain configuration
│       └── techno.yml           # Technology configuration
└── build/                       # Build directory (generated)
```

### Adding New Recipes

1. Create a Python file in `flows/recipes/`, `flows/patterns/`, or `flows/macros/`
2. Define a Typer application named `app`
3. The module will be automatically loaded by `cook.py`

Example:

```python
import typer

app = typer.Typer()

@app.command()
def my_recipe(
    target: str = typer.Option(..., "--target", "-t", help="CVA6 configuration"),
):
    """Description of my recipe."""
    # Implementation
    pass
```

### Build Manifests and Prerequisite Checks

Recipes often depend on artifacts produced by other recipes (e.g. a simulation
needs the software compiled by `sw-compile` and the design elaborated by
`vcs-uvm-comp`). To make these dependencies explicit and user-friendly, the
framework provides `flows/utils/manifest.py`:

- **`write_manifest(out_dir, recipe, options)`** - called at the end of a
  producer recipe. Writes a `cook_manifest.yml` file in the recipe's output
  directory recording the recipe name, date, and all options used. Example:

  ```yaml
  # build/cv32a60x/elab/sim_rtl/cook_manifest.yml
  recipe: vcs-uvm-comp
  date: '2026-08-26T14:32:11'
  options:
    target: cv32a60x
    comp_mode: rtl
    trace_mode: notrace
    tandem_enabled: false
    stats: false
    sim_profile: false
  ```

- **`require_prerequisite(path, description, hint)`** - called at the
  beginning of a consumer recipe. If the artifact is missing, prints an
  actionable error telling the user which recipe to run first, then exits:

  ```
  Missing prerequisite: compiled software for test 'hello_world'
    Expected: build/cv32a60x/compile/hello_world/hello_world.elf
    Run first: ./cook.py sw-compile -t cv32a60x -c <toolchain> --out hello_world <sources>
  ```

- **`read_manifest(out_dir)` + `require_manifest_option(...)`** - used by
  consumer recipes to verify that the options requested now are compatible
  with the options used by the producer. For example, `vcs-uvm-run
  --trace-mode fast` fails early with an explanation if the design was
  elaborated with `--trace-mode notrace`:

  ```
  Incompatible option: trace mode 'fast' requires a design elaborated with trace support
    'vcs-uvm-comp' was run with trace_mode='notrace', expected one of ['gui', 'fast', 'compact']
    Fix: ./cook.py vcs-uvm-comp -t cv32a60x --comp-mode rtl --trace-mode fast
  ```

  If no manifest exists (artifacts generated by an older cook.py), the
  compatibility check is skipped with a warning instead of failing.

**Current option compatibility rules enforced:**

| Consumer recipe | Option | Requires producer elaborated with |
|---|---|---|
| `vcs-uvm-run` / `xcelium-uvm-run` / `questa-uvm-run` | `--trace-mode` (any except notrace) | `--trace-mode` gui/fast/compact |
| `vcs-uvm-run` | `--interactive-gui` | `--trace-mode gui` |
| `*-uvm-run` | `--tandem-enabled` | `--tandem-enabled` |
| `*-uvm-run` | `--stats` | `--stats` |
| `vcs-uvm-run` | `--sim-profile` | `--sim-profile` |
| `vcs-uvm-gui` | (always) | simulation run with `--trace-mode` gui/fast |
| `*-uvm-comp` gate modes | `--comp-mode gate_*` | `dc-shell-synth` outputs present |

When adding a new recipe, follow this pattern:

1. Call `require_prerequisite()` early (before cleaning output directories)
   for every artifact the recipe consumes.
2. Call `write_manifest()` at the end, once artifacts are generated, passing
   all options that could affect downstream recipes.
3. If some of your options only work when the producer used specific options,
   add a `require_manifest_option()` check.

**Rule of thumb: no dedicated build directory, no manifest.** Recipes that do
not write to a dedicated output directory under `build/` do not write a
manifest. This covers:

- code quality tools (`black-python-formating`, `pylint-run`,
  `verible-rtl-formating`, `self-check`)
- recipes writing into the source tree (`hwconfig-forge` - its generated
  config package already carries a traceability header comment)
- external installers (`git-dependencies` - consumers check the installed
  tools directly with `require_prerequisite()`)
- testlist wrappers (`sw-compile-testlist`, `vcs-generator-run-testlist`,
  `uvm-run-testlist`) - each underlying unit recipe already writes a
  per-test manifest in its own output directory.

## Recipe Reference

### General Usage

```bash
# Show all available commands
./cook.py --help

# Get help for a specific command
./cook.py <command> --help
```

---

### Test Patterns

Pre-configured benchmark and test patterns for quick CVA6 validation.

#### `hello-world`

Build a simple "Hello World" test program.

```bash
./cook.py hello-world [OPTIONS]
```

**Required Options:**
- `-t, --target TEXT` - CVA6 user configuration (e.g., cv32a60x, cv32a65x)
- `-c, --toolchain [llvm-20-1-8|...]` - Toolchain defined in `$CONFIG_DIR/compiler.yml`

**Optional:**
- `--march TEXT` - Custom RISC-V architecture string (overrides target default)
- `--mabi TEXT` - Custom RISC-V ABI (overrides target default)

**Example:**
```bash
./cook.py hello-world -t cv32a60x -c llvm-20-1-8
```

#### `coremark`

Build the CoreMark performance benchmark.

```bash
./cook.py coremark [OPTIONS]
```

**Required Options:**
- `-t, --target TEXT` - CVA6 user configuration
- `-c, --toolchain [llvm-20-1-8|...]` - Toolchain defined in `$CONFIG_DIR/compiler.yml`

**Optional:**
- `--march TEXT` - Custom march string
- `--mabi TEXT` - Custom mabi string

**Example:**
```bash
./cook.py coremark -t cv32a60x -c llvm-20-1-8 --march rv32imac
```

**Output:** Generates `build/<target>/compile/coremark/*.elf` and reports

#### `dhrystone`

Build the Dhrystone performance benchmark.

```bash
./cook.py dhrystone [OPTIONS]
```

**Required Options:**
- `-t, --target TEXT` - CVA6 user configuration
- `-c, --toolchain [llvm-20-1-8|...]` - Toolchain defined in `$CONFIG_DIR/compiler.yml`

**Optional:**
- `--march TEXT` - Custom march string
- `--mabi TEXT` - Custom mabi string

**Example:**
```bash
./cook.py dhrystone -t cv32a65x -c gcc-14
```

---

### Software Compilation

Compile C/Assembly programs for CVA6 targets.

#### `sw-compile`

Compile software from source files and generate ELF binary with reports.

```bash
./cook.py sw-compile [OPTIONS] SRC_FILES...
```

**Required Arguments:**
- `SRC_FILES...` - Source files (.c, .S, etc.)

**Required Options:**
- `-t, --target TEXT` - CVA6 user configuration
- `-c, --toolchain [llvm-20-1-8|...]` - Toolchain defined in `$CONFIG_DIR/compiler.yml`
- `--linker TEXT` - Linker script file path
- `--out TEXT` - Test name (used throughout the flow)

**Optional:**
- `--inc TEXT` - Include directories (can be repeated)
- `--options TEXT` - Additional compiler options
- `--march TEXT` - Custom march instead of target default
- `--mabi TEXT` - Custom mabi instead of target default
- `--define TEXT` - Preprocessor directives (can be repeated)

**Example:**
```bash
./cook.py sw-compile \
  -t cv32a60x \
  -c llvm-20-1-8 \
  --linker verif/tests/custom/hello_world/link.ld \
  --out my_test \
  --inc verif/tests/custom/common \
  --define DEBUG=1 \
  src/main.c src/util.c src/startup.S
```

**Output:**
- `build/<target>/compile/<test>/<test>.elf`
- `build/<target>/compile/<test>/<test>.dump`
- `build/<target>/compile/<test>/<test>.size`

#### `sw-compile-testlist`

Build tests from a YAML testlist file.

```bash
./cook.py sw-compile-testlist [OPTIONS]
```

**Required Options:**
- `-t, --target TEXT` - CVA6 user configuration
- `-c, --toolchain [llvm-20-1-8|...]` - Toolchain defined in `$CONFIG_DIR/compiler.yml`
- `-l, --testlist TEXT` - Testlist YAML file in `verif/tests`
- `-tl, --target-testlist TEXT` - Testlist YAML file in `config/target/<target>/verif`

**Optional:**
- `-n, --testname TEXT` - Single test in testlist or target-testlist
- `--march TEXT` - Custom march instead of target default
- `--mabi TEXT` - Custom mabi instead of target default

**Example:**
```bash
# Compile all tests in the list
./cook.py sw-compile-testlist -t cv32a60x -c llvm-20-1-8 -l custom/smoke.yml

# Compile only one test from the list
./cook.py sw-compile-testlist -t cv32a60x -c llvm-20-1-8 -l custom/smoke.yml -n test_add
```

---

### RTL Simulation

RTL simulation with UVM testbench. Supports multiple simulators: VCS (Synopsys), Xcelium (Cadence), and Questa (Siemens).

#### `vcs-uvm-comp`

Compile and elaborate the VCS UVM simulation.

```bash
./cook.py vcs-uvm-comp [OPTIONS]
```

**Required Options:**
- `-t, --target TEXT` - CVA6 user configuration

**Optional:**
- `--comp-mode [rtl|gate_wc_power|gate_wc_timing|coverage]` - Hardware compilation mode (default: `rtl`)
- `--trace-mode [gui|fast|compact|notrace]` - Waveform trace mode (default: `notrace`)
  - `gui`: Full traces for Verdi (FSDB format)
  - `fast`: Fast dump with reduced detail
  - `compact`: Minimal traces
  - `notrace`: No waveform generation
- `--tandem-enabled / --no-tandem-enabled` - Enable SPIKE tandem verification (default: disabled)
- `--stats / --no-stats` - Enable RTL performance tracer (default: disabled)
- `--sim-profile / --no-sim-profile` - Enable simulation profiling (default: disabled)

**Example:**
```bash
# Basic RTL compilation
./cook.py vcs-uvm-comp -t cv32a60x

# With full traces and tandem verification
./cook.py vcs-uvm-comp \
  -t cv32a60x \
  --trace-mode gui \
  --tandem-enabled \
  --stats
```

**Output:** `build/<target>/elab/sim_rtl/simv` (simulation executable)

#### `vcs-uvm-run`

Run a single test on the elaborated simulation.

```bash
./cook.py vcs-uvm-run [OPTIONS]
```

**Required Options:**
- `-t, --target TEXT` - CVA6 user configuration
- `-n, --testname TEXT` - Test name (must be compiled first)

**Optional:**
- `--comp-mode [rtl|gate_wc_power|gate_wc_timing|coverage]` - Hardware compilation mode (default: `rtl`)
- `--trace-mode [gui|fast|compact|notrace]` - Trace mode (default: `notrace`)
- `--uvm-verbosity [NONE|LOW|MEDIUM|HIGH|FULL|DEBUG]` - UVM verbosity level (default: `NONE`)
- `--tandem-enabled / --no-tandem-enabled` - Enable SPIKE tandem (default: disabled)
- `--tb-performance-mode / --no-tb-performance-mode` - Enable testbench performance mode (default: disabled)
- `--stats / --no-stats` - Enable RTL perf tracer (default: disabled)
- `--sim-profile / --no-sim-profile` - Enable simulation profiling (default: disabled)
- `--interactive-gui / --no-interactive-gui` - Launch Verdi for interactive simulation (default: disabled)
- `--run_opts TEXT` - Additional simulation run options
- `--uvm-seed TEXT` - UVM randomization seed (default: randomized)

**Example:**
```bash
# Run with GUI traces
./cook.py vcs-uvm-run \
  -t cv32a60x \
  -n hello-world \
  --trace-mode gui \
  --uvm-verbosity MEDIUM

# Run with interactive Verdi
./cook.py vcs-uvm-run \
  -t cv32a60x \
  -n coremark \
  --interactive-gui \
  --stats
```

**Output:** `build/<target>/simulation/sim_rtl/<test>/`

#### `xcelium-uvm-comp`

Compile and elaborate the Xcelium (Cadence) UVM simulation.

```bash
./cook.py xcelium-uvm-comp [OPTIONS]
```

**Options:** Same as `vcs-uvm-comp` (see above)

**Example:**
```bash
./cook.py xcelium-uvm-comp -t cv32a60x --trace-mode fast
```

**Output:** `build/<target>/elab/sim_rtl/xcelium.d/` (snapshot)

#### `xcelium-uvm-run`

Run a single test with Xcelium simulator.

```bash
./cook.py xcelium-uvm-run [OPTIONS]
```

**Options:** Same as `vcs-uvm-run` (see above)

**Example:**
```bash
./cook.py xcelium-uvm-run -t cv32a60x -n hello-world --trace-mode fast
```

**Output:** `build/<target>/simulation/sim_rtl/<test>/` (waveforms in `.shm` format)

#### `questa-uvm-comp`

Compile and elaborate the Questa/ModelSim (Siemens) UVM simulation.

```bash
./cook.py questa-uvm-comp [OPTIONS]
```

**Options:** Same as `vcs-uvm-comp` (see above, except `--sim-profile` not supported)

**Example:**
```bash
./cook.py questa-uvm-comp -t cv32a60x --trace-mode fast
```

**Output:** `build/<target>/elab/sim_rtl/work/` (library)

#### `questa-uvm-run`

Run a single test with Questa/ModelSim simulator.

```bash
./cook.py questa-uvm-run [OPTIONS]
```

**Options:** Same as `vcs-uvm-run` (see above, except `--sim-profile` not supported)

**Example:**
```bash
./cook.py questa-uvm-run -t cv32a60x -n hello-world --trace-mode fast
```

**Output:** `build/<target>/simulation/sim_rtl/<test>/` (waveforms in `.wlf` format)

#### `uvm-run-testlist`

Run all tests (or a single test) from a testlist with any simulator.

```bash
./cook.py uvm-run-testlist [OPTIONS]
```

**Required Options:**
- `-s, --simulator [vcs|xcelium|questa]` - Simulator to use
- `-t, --target TEXT` - CVA6 user configuration

**Optional:**
- `-l, --testlist TEXT` - Testlist YAML file in `verif/tests`
- `-n, --testname TEXT` - Test in the testlist or already compiled (multiple allowed)
- `--comp-mode [rtl|gate_wc_power|gate_wc_timing|coverage]` - Hardware compilation mode (default: `rtl`)
- `--trace-mode [gui|fast|compact|notrace]` - Trace mode (default: `notrace`)
- `--uvm-verbosity [NONE|LOW|MEDIUM|HIGH|FULL|DEBUG]` - UVM verbosity level (default: `NONE`)
- `--tandem-enabled / --no-tandem-enabled` - Enable SPIKE tandem (default: disabled)
- `--tb-performance-mode / --no-tb-performance-mode` - Enable TB perf mode (default: disabled)
- `--stats / --no-stats` - Enable RTL perf tracer (default: disabled)
- `--sim-profile / --no-sim-profile` - Enable simulation profiling (VCS only, default: disabled)
- `--interactive-gui / --no-interactive-gui` - Launch GUI interactively (default: disabled)
- `--run_opts TEXT` - Additional simulation run options
- `--uvm-seed TEXT` - UVM randomization seed

**Example:**
```bash
# Run entire testlist with VCS
./cook.py uvm-run-testlist \
  -s vcs \
  -t cv32a60x \
  -l custom/regression.yml \
  --trace-mode compact

# Run with Xcelium
./cook.py uvm-run-testlist \
  -s xcelium \
  -t cv32a60x \
  -l custom/regression.yml \
  --tandem-enabled

# Run with Questa
./cook.py uvm-run-testlist \
  -s questa \
  -t cv32a60x \
  -n test_mul \
  --stats
```


#### `vcs-uvm-gui`

Open Verdi to view simulation traces (FSDB only).

```bash
./cook.py vcs-uvm-gui [OPTIONS]
```

**Required Options:**
- `-t, --target TEXT` - CVA6 user configuration

**Optional:**
- `-n, --testname TEXT` - Test name (compiled and simulated)
- `--comp-mode [rtl|gate_wc_power|gate_wc_timing|coverage]` - Hardware compilation mode (default: `rtl`)
- `-s, --session TEXT` - Verdi session file (user-saved .ses file)

**Example:**
```bash
# Open Verdi for a specific test
./cook.py vcs-uvm-gui -t cv32a60x -n hello-world

# Open with saved session
./cook.py vcs-uvm-gui -t cv32a60x -n coremark -s my_debug_session.ses
```

#### `spike-run`

Run test using the SPIKE ISA simulator.

```bash
./cook.py spike-run [OPTIONS]
```

**Required Options:**
- `-t, --target TEXT` - CVA6 user configuration
- `-n, --testname TEXT` - Test name (must be compiled first)

**Example:**
```bash
./cook.py spike-run -t cv32a60x -n hello-world
```

---

### Random Test Generation

RISC-V DV random instruction generator integration.

#### `vcs-generator-comp`

Compile the RISC-V DV generator project.

```bash
./cook.py vcs-generator-comp
```

No options required. This elaborates the test generation environment.

**Example:**
```bash
./cook.py vcs-generator-comp
```

#### `vcs-generator-run`

Run RISC-V DV to generate random instruction tests.

```bash
./cook.py vcs-generator-run [OPTIONS]
```

**Required Options:**
- `-n, --testname TEXT` - Test name to generate

**Optional:**
- `--type-instr [load_store|branch_jump|fence|csr_instr|dret|ebreak|unaligned_load_store]` - Instruction types to enable (comma-separated)
- `--gen-test TEXT` - Generator test class to run (default: `cva6_instr_base_test_c`)
- `-i, --iterations INTEGER` - Number of iterations (default: 1)
- `--batch-size INTEGER` - Tests to generate per batch (default: 1)
- `--instr-cnt INTEGER` - Number of instructions to generate (default: 300)
- `-e, --extension [zba|zbb|zbc|zbs|zcb|zcmp|zcmt|x]` - RISC-V extensions to enable (repeat flag for multiple)
- `-d, --directed-instr TEXT` - Directed instruction streams (e.g., `cva6_load_store_rand_instr_stream_c,10`)
- `--illegal-instr-ratio INTEGER` - Illegal instruction ratio (default: 0)
- `--unsupported-instr-ratio INTEGER` - Unsupported instruction ratio (default: 0)
- `--num-of-sub-program INTEGER` - Number of sub-programs (default: 0)
- `--seed INTEGER` - Random seed (randomized if not provided)
- `--tvec-alignment INTEGER` - Trap vector alignment value (default: 8)
- `-v, --verbose` - Enable UVM_HIGH verbosity
- `--options TEXT` - Additional options

**Example:**
```bash
# Generate simple random test
./cook.py vcs-generator-run -n my_random_test

# Generate with extensions and iterations
./cook.py vcs-generator-run \
  -n stress_test \
  --gen-test cva6_instr_base_test_c \
  --instr-cnt 1000 \
  -i 10 \
  -e zba -e zbb -e zbs \
  --directed-instr "cva6_load_store_rand_instr_stream_c,20"

# Generate with specific seed
./cook.py vcs-generator-run \
  -n reproducible_test \
  --seed 12345 \
  --instr-cnt 500 \
  --type-instr load_store,branch_jump
```

#### `vcs-generator-run-testlist`

Generate and run tests from a testlist.

```bash
./cook.py vcs-generator-run-testlist [OPTIONS]
```

**Required Options:**
- `-t, --target TEXT` - CVA6 user configuration
- `-l, --testlist TEXT` - Testlist YAML file in `verif/tests`
- `-tl, --target-testlist TEXT` - Testlist YAML file in `config/target/<target>/verif`

**Optional:**
- `-n, --testname TEXT` - Single test in testlist or target-testlist
- `--seed INTEGER` - Random seed (randomized if not provided)
- `--batch-size INTEGER` - Tests to generate per batch (default: 1)

**Example:**
```bash
# Generate all tests in testlist
./cook.py vcs-generator-run-testlist -l riscv-dv/random_tests.yml

# Generate specific test with seed
./cook.py vcs-generator-run-testlist \
  -l riscv-dv/random_tests.yml \
  -n arithmetic_test \
  --seed 98765 \
  --batch-size 4
```

---

### Synthesis

DC Shell logic synthesis.

#### `dc-shell-synth`

Run DC Shell synthesis flow.

```bash
./cook.py dc-shell-synth [OPTIONS]
```

**Required Options:**
- `-t, --target TEXT` - CVA6 user configuration
- `--techno [MyTechno]` - Technology defined in `$CONFIG_DIR/techno.yml`
- `--period TEXT` - Synthesis target clock period (in ns)

**Optional:**
- `--script-file TEXT` - DC setup script (default: `dc.tcl`)
- `--define [HPDCACHE_ASSERT_OFF|RVFI_ENABLE]` - Preprocessor directives (default: `HPDCACHE_ASSERT_OFF`)
- `--clean / --no-clean` - Clean working directory before synthesis (default: clean)

**Example:**
```bash
# Basic synthesis
./cook.py dc-shell-synth \
  -t cv32a60x \
  --techno MyTechno \
  --period 10.0

# with custom script
./cook.py dc-shell-synth \
  -t cv32a65x \
  --techno MyTechno \
  --period 5.0 \
  --script-file custom_dc.tcl \
  --no-clean
```

**Output:** `build/<target>/synthesis/`

---

### Static Analysis

Code quality and lint checking tools.

#### `spyglass-design-read`

Load design into Spyglass for static analysis.

```bash
./cook.py spyglass-design-read [OPTIONS]
```

**Required Options:**
- `-t, --target TEXT` - CVA6 user configuration

**Example:**
```bash
./cook.py spyglass-design-read -t cv32a60x
```

#### `spyglass-run`

Run Spyglass static analysis checks.

```bash
./cook.py spyglass-run [OPTIONS]
```

**Required Options:**
- `-t, --target TEXT` - CVA6 user configuration

**Optional:**
- `--run-type [run_cli|gui|show_goals]` - Execution mode (default: `run_cli`)
  - `run_cli`: Command-line batch mode
  - `gui`: Interactive GUI mode
  - `show_goals`: Display analysis goals

**Example:**
```bash
# Run checks in CLI mode
./cook.py spyglass-run -t cv32a60x

# Open GUI for interactive analysis
./cook.py spyglass-run -t cv32a60x --run-type gui
```

#### `verible-rtl-formating`

Format CVA6 RTL files with Verible formatter.

```bash
./cook.py verible-rtl-formating [OPTIONS]
```

**Required Options:**
- `-t, --target TEXT` - CVA6 user configuration

**Example:**
```bash
./cook.py verible-rtl-formating -t cv32a60x
```

**Note:** Verible formatting is mandatory before submitting pull requests.

#### `black-python-formating`

Format Python files with Black formatter.

```bash
./cook.py black-python-formating
```

No options required.

**Example:**
```bash
./cook.py black-python-formating
```

**Note:** Black formatting is mandatory before submitting pull requests.

#### `pylint-run`

Run Pylint static code analysis on Python files.

```bash
./cook.py pylint-run
```

No options required.

**Example:**
```bash
./cook.py pylint-run
```

**Note:** pylint 10/10 is mandatory before submitting pull requests.

---

### Reports

Analysis and visualization of simulation and synthesis results.

#### `report-benchmark`

Analyze performance benchmark logs and validate cycle counts.

```bash
./cook.py report-benchmark [OPTIONS]
```

**Required Options:**
- `-t, --target TEXT` - CVA6 user configuration
- `-n, --testname TEXT` - Test name (must be simulated first)

**Optional:**
- `--comp-mode [rtl|gate_wc_power|gate_wc_timing|coverage]` - Hardware compilation mode (default: `rtl`)

**Example:**
```bash
./cook.py report-benchmark -t cv32a60x -n coremark
./cook.py report-benchmark -t cv32a65x -n dhrystone --comp-mode gate_wc_timing
```

**Output:** Performance metrics and cycle count validation

#### `report-dc-shell-synth-kpi`

Analyze synthesis area (gate count) and parse logs for errors/warnings.

```bash
./cook.py report-dc-shell-synth-kpi [OPTIONS]
```

**Required Options:**
- `-t, --target TEXT` - CVA6 user configuration

**Optional:**
- `--log PATH` - Path to area/summary log file
- `--synthesis-log PATH` - Path to full synthesis log
- `--config PATH` - Path to YAML config file

**Example:**
```bash
# Use default paths
./cook.py report-dc-shell-synth-kpi -t cv32a60x

# Use custom log files
./cook.py report-dc-shell-synth-kpi \
  -t cv32a60x \
  --log build/cv32a60x/synthesis/area.rpt \
  --synthesis-log build/cv32a60x/synthesis/synth.log
```

**Output:** Gate count summary and error/warning report

#### `report-dc-shell-synth-area`

Generate Sunburst charts from synthesis area reports.

```bash
./cook.py report-graph-area [OPTIONS]
```

**Required Options:**
- `-t, --target TEXT` - CVA6 user configuration

**Optional:**
- `--in-report PATH` - Input report file to analyze
- `--config PATH` - Path to YAML config file
- `--top TEXT` - Top module to analyze (default: `cva6_example_obi`)

**Example:**
```bash
# Use default report
./cook.py report-graph-area -t cv32a60x

# Specify custom report and top module
./cook.py report-graph-area \
  -t cv32a65x \
  --in-report build/cv32a65x/synthesis/hierarchy.rpt \
  --top cva6_example_axi
```

**Output:** Interactive Sunburst chart visualization

---

### Macros

Automated multi-step workflows.

#### `macro-vcs-generator-testlist`

Complete flow: VCS Generator → SW Compile → UVM Run from testlist.

```bash
./cook.py macro-vcs-generator-testlist [OPTIONS]
```

**Required Options:**
- `-t, --target TEXT` - CVA6 user configuration
- `-l, --testlist TEXT` - Testlist YAML file in `verif/tests`
- `-tl, --target-testlist TEXT` - Testlist YAML file in `config/target/<target>/verif`

**Optional:**
- `-n, --testname TEXT` - Single test in testlist or target-testlist
- `-c, --toolchain [llvm-20-1-8|...]` - Toolchain (default: llvm-20-1-8)
- `--march TEXT` - Custom march
- `--mabi TEXT` - Custom mabi
- `--comp-mode [rtl|gate_wc_power|gate_wc_timing|coverage]` - Hardware compilation mode (default: `rtl`)
- `--trace-mode [gui|fast|compact|notrace]` - Trace mode (default: `notrace`)
- `--uvm-verbosity [NONE|LOW|MEDIUM|HIGH|FULL|DEBUG]` - UVM verbosity (default: `NONE`)
- `--tandem-enabled / --no-tandem-enabled` - Enable SPIKE tandem (default: disabled)
- `--tb-performance-mode / --no-tb-performance-mode` - Enable TB perf mode (default: disabled)
- `--stats / --no-stats` - Enable RTL perf tracer (default: disabled)
- `--sim-profile / --no-sim-profile` - Enable simulation profiling (default: disabled)
- `--run_opts TEXT` - Simulation run options
- `--batch-size INTEGER` - Tests to generate per batch (default: 1)
- `--seed INTEGER` - Random seed (randomized if not provided)
- `--uvm-seed TEXT` - UVM randomization seed

**Example:**
```bash
# Run complete random test generation flow
./cook.py macro-vcs-generator-testlist \
  -t cv32a60x \
  -l riscv-dv/basic_tests.yml \
  -c llvm-20-1-8 \
  --trace-mode fast \
  --batch-size 4

# Single test with tandem verification
./cook.py macro-vcs-generator-testlist \
  -t cv32a65x \
  -l riscv-dv/stress_tests.yml \
  -n arithmetic_stress \
  -c gcc-14 \
  --tandem-enabled \
  --stats
```

---

### Utilities

System utilities and configuration helpers.

#### `hwconfig-forge`

Modify or override hardware configuration parameters.

```bash
./cook.py hwconfig-forge [OPTIONS]
```

**Required Options:**
- `-t, --target_ref TEXT` - Reference CVA6 user configuration
- `-f, --target_forged TEXT` - Name of new forged configuration
- `-p, --param TEXT` - Parameter to override with value (`parameter=newvalue`) - repeat for multiple

**Example:**
```bash
# Create modified configuration
./cook.py hwconfig-forge \
  -t cv32a60x \
  -f cv32a60x_custom \
  -p "NrLoadPipeRegs=2" \
  -p "FpgaEn=false" \
  -p "CvxifEn=true"
```

**Output:** New configuration file `config/cv32a60x_custom.yml`

#### `riscv-isa-modify`

Modify RISC-V ISA strings by adding or removing extensions with automatic dependency handling.

```bash
./cook.py riscv-isa-modify [OPTIONS]
```

**Required Options:**
- `-t, --target TEXT` - CVA6 user configuration (for output directory isolation)
- `-i, --isa TEXT` - Input RISC-V ISA string (e.g., `rv32imc_zicsr` or `rv64gc`)

**Optional Options:**
- `-a, --add TEXT` - Extensions to add if not present (can be specified multiple times)
- `-r, --remove TEXT` - Extensions to remove if present (can be specified multiple times)
- `-q, --quiet` - Suppress output (errors only)

**Features:**
- Automatic extension dependency handling (e.g., adding 'd' auto-adds 'f')
- G-macro expansion/compaction (G = IMAFD + Zicsr + Zifencei)
- Per-target output isolation (prevents contamination in parallel CI jobs)
- YAML output for easy shell parsing

**Examples:**
```bash
# Add floating-point extensions
./cook.py riscv-isa-modify -t cv32a60x --isa rv32imc --add f --add d

# Remove floating-point (also removes dependent extensions)
./cook.py riscv-isa-modify -t cv64a6_imafdc_sv39 --isa rv64gc --remove f

# Combined add and remove
./cook.py riscv-isa-modify -t cv32a60x --isa rv32imc_zicsr --add f --add d --remove c

# Use in shell script
./cook.py riscv-isa-modify -t cv32a60x --isa rv32imc --add f --quiet
MODIFIED_ISA=$(grep modified_isa build/cv32a60x/riscv_isa_modify/modified_isa.yml | awk '{print $2}')
echo "Result: $MODIFIED_ISA"  # rv32imfc
```

**Output:** `build/<target>/riscv_isa_modify/modified_isa.yml`

**Use Case:** Commonly used in CI to dynamically adjust ISA strings for specific test requirements (e.g., adding 'f' extension for virtual memory tests).

#### `self-check`

Verify framework integrity and configuration.

```bash
./cook.py self-check
```

No options required.

**Example:**
```bash
./cook.py self-check
```

---

## Complete Flow Examples with Synopsys VCS and UVM testbench

### Example 1: Quick Smoke Test

```bash
# 1. Compile a pattern
./cook.py hello-world -t cv32a60x -c llvm-20-1-8

# 2. Elaborate simulation
./cook.py vcs-uvm-comp -t cv32a60x

# 3. Run simulation with traces
./cook.py vcs-uvm-run -t cv32a60x -n hello-world --trace-mode gui

# 4. View waveforms
./cook.py vcs-uvm-gui -t cv32a60x -n hello-world
```

### Example 2: Testlist Regression

```bash
# 1. Compile all tests in testlist
./cook.py sw-compile-testlist -t cv32a60x -c llvm-20-1-8 -l custom/regression.yml

# 2. Elaborate once
./cook.py vcs-uvm-comp -t cv32a60x

# 3. Run all tests (no traces for speed)
./cook.py uvm-run-testlist --simulator vcs -t cv32a60x -l custom/regression.yml --trace-mode notrace
```

### Example 3: Performance Benchmark

```bash
# 1. Compile benchmarks
./cook.py coremark -t cv32a65x -c gcc-14
./cook.py dhrystone -t cv32a65x -c gcc-14

# 2. Elaborate with performance counters
./cook.py vcs-uvm-comp -t cv32a65x --stats

# 3. Run benchmarks
./cook.py vcs-uvm-run -t cv32a65x -n coremark --stats --tb-performance-mode
./cook.py vcs-uvm-run -t cv32a65x -n dhrystone --stats --tb-performance-mode

# 4. Analyze results
./cook.py report-benchmark -t cv32a65x -n coremark
./cook.py report-benchmark -t cv32a65x -n dhrystone
```

### Example 4: Synthesis and Area Analysis

```bash
# 1. Run synthesis
./cook.py dc-shell-synth \
  -t cv32a60x \
  --techno umc55 \
  --period 5.0

# 2. Check area and errors
./cook.py report-check-area -t cv32a60x

# 3. Generate visualization (html)
./cook.py report-graph-area -t cv32a60x
```

### Example 5: Random Test Generation

```bash
# 1. Elaborate generator
./cook.py vcs-generator-comp

# 2. Generate and run with macro
./cook.py macro-vcs-generator-testlist \
  -t cv32a60x \
  -l riscv-dv/random_suite.yml \
  -c llvm-20-1-8 \
  --batch-size 8 \
  --trace-mode compact \
  --tandem-enabled
```

### Example 6: Gate-Level Simulation

```bash
# 1. Synthesize design first
./cook.py dc-shell-synth \
  -t cv32a60x \
  --techno umc55 \
  --period 10.0

# 2. Compile test
./cook.py hello-world -t cv32a60x -c llvm-20-1-8

# 3. Elaborate gate-level simulation
./cook.py vcs-uvm-comp \
  -t cv32a60x \
  --comp-mode gate_wc_timing \
  --trace-mode gui

# 4. Run gate-level simulation
./cook.py vcs-uvm-run \
  -t cv32a60x \
  -n hello-world \
  --comp-mode gate_wc_timing \
  --trace-mode gui
```

## Simulation Outputs and Logs

### Build Directory Structure

All simulation outputs are organized in the `build/` directory:

```
build/<target>/
├── compile/<test>/           # Software compilation outputs
│   ├── <test>.elf           # Executable binary
│   ├── <test>.dump          # Disassembly
│   ├── <test>.size          # Size report
│   └── compile.log          # Compilation log
├── elab/<comp-mode>/        # RTL elaboration
│   ├── simv                 # Simulation executable
│   └── compilation.log      # Elaboration log
└── simulation/<comp-mode>/<test>/  # Simulation results
    ├── simulation.log              # VCS simulation log
    ├── rvfi.log               # Hart execution trace
    ├── trace_hart_0_commit.log  # Committed instruction trace
    ├── wave.fsdb           # Waveform file (if trace enabled)
```

### Simulation Log Files Description

- **simulation.log**: Simulator console output
- **trace_rvfi_hart_00.dasm**: RTL simulation trace (RVFI)
- **spike_dasm.log**: RTL simulation trace disassembled (from trace_rvfi_hart_00.dasm)
- **tandem.log**: Spike Reference model trace (if tandem_mode enabled)
- **tandem_report.yml**: Tandem mismatchs  if any (if tandem_mode enabled)
- **timing_GLOBAL_PATTERN_end**: Time when ELF symbol timing_GLOBAL_PATTERN is detected
- **timing_GLOBAL_PATTERN_start**: Time when ELF symbol timing_GLOBAL_PATTERN is detected
- **timing_GLOBAL_PATTERN_start_cycle**: Cycle when ELF symbol timing_GLOBAL_PATTERN is detected
- **timing_GLOBAL_PATTERN_end_cycle**: Cycle when ELF symbol timing_GLOBAL_PATTERN is detected

### Waveform Generation

Waveform generation is controlled by the `--trace-mode` option:

- **`notrace`** (default): No waveform generation (fastest simulation)
- **`compact`**: Generate compact waveforms (FSDB format, smaller file size)
- **`fast`**: Generate fast waveforms (VPD format, faster dump, larger files)
- **`gui`**: Generate full waveforms for GUI viewing (FSDB format)

**Examples:**

```bash
# No waveforms (fastest)
./cook.py vcs-uvm-run -t cv32a60x -n hello-world --trace-mode notrace

# Compact waveforms (good for debugging)
./cook.py vcs-uvm-run -t cv32a60x -n hello-world --trace-mode compact

# Full GUI waveforms
./cook.py vcs-uvm-run -t cv32a60x -n hello-world --trace-mode gui

# View waveforms with Verdi
./cook.py vcs-uvm-gui -t cv32a60x -n hello-world
```

**Waveform file locations:**
- FSDB files: `build/<target>/simulation/<comp-mode>/<test>/inter.fsdb`
- VPD files: `build/<target>/simulation/<comp-mode>/<test>/inter.vpd`

### Legacy Environment Variables

The old `cva6.py` flow used environment variables for trace control. These are **not used** by `cook.py`:

- `TRACE_FAST=1` (old) → use `--trace-mode fast` (new)
- `TRACE_COMPACT=1` (old) → use `--trace-mode compact` (new)
- `VERDI=1` (old) → use `--interactive-gui` flag (new)

## Troubleshooting

### Toolchain Issues

If you encounter compiler-related errors:

1. Verify `compiler.yml` is properly configured
2. Check that `TOOLS_PATH` is correct
3. Check logs: `build/<target>/compile/<test>/compilation.log`
4. Confirm toolchain name matches what's used in commands

### VCS Simulation Issues

If elaboration fails:

1. Verify VCS is in `$PATH`
2. Check logs: `build/<target>/elab/<comp-mode>/compilation.log`
3. Ensure VCS license is available
4. Check for missing SystemVerilog files

```bash
# Verify VCS installation
which vcs
vcs -ID
```

### Missing Build Outputs

If `build/` directory is missing or incomplete:

1. Run recipes in correct order (compile before simulate)
2. Check for errors in previous steps
3. Verify write permissions on `build/` directory

### Useful Environment Variables

```bash
# Use custom configuration directory
export CONFIG_DIR=/path/to/my/config

# Synopsys tool locations (if needed)
export VCS_HOME=/path/to/vcs
export VERDI_HOME=/path/to/verdi
export DC_SHELL=/path/to/dc_shell
export SPYGLASS_HOME=/path/to/spyglass

# Add tools to PATH
export PATH=$VCS_HOME/bin:$VERDI_HOME/bin:$PATH
```

### Debug Mode

For debugging recipe execution:

```bash
# Enable Python debug output
python -u cook.py <command> [OPTIONS]

# Check configuration loading
export CONFIG_DIR=/your/config
./cook.py self-check
```



./cook.py sw-compile-testlist -t cv32a60x -c dummy1 -l config/target/cv32a60x/verif/*.yaml
./cook.py questa-uvm-comp -t cv32a60x --tandem-enabled
./cook.py questa-uvm-run -t cv32a60x -n rv32ui-p-add_0 --tandem-enabled

[![build status](https://iis-git.ee.ethz.ch/floce/ariane/badges/master/build.svg)](https://iis-git.ee.ethz.ch/floce/ariane/commits/master)
[![coverage report](https://iis-git.ee.ethz.ch/floce/ariane/badges/master/coverage.svg)](https://iis-git.ee.ethz.ch/floce/ariane/commits/master)

# Ariane RISC-V CPU

![](docs/fig/ariane_overview.png)

For detailed documentation refer to the [online documentation](http://www.be4web.net/ariane/) (Login: `zarubaf` Password: `zaruba`).

## <a name="getting_started"></a>Getting Started
Go and get the [RISC-V tools](https://github.com/riscv/riscv-tools).

Checkout the repository and initialize all submodules
```
git checkout git@iis-git.ee.ethz.ch:floce/ariane.git
git submodule update --init --recursive
```

Build Ariane by using the Makefile:
```
make build
```

Start the simulation using Modelsim:
```
make sim
```
To specify the test to run use (e.g.: you want to run `rv64ui-p-sraw` inside the riscv-tests isa folder:
```
make sim riscv-test=rv64ui-p-sraw
```
If you call `simc` instead of `sim` it will run without the GUI.

Or start any of the unit tests by:
```
make dcache_arbiter
```
### Randomized Constrained Testing with Torture

Ariane's core testbench is fully compatible with the randomized constrained testing framework called Torture. To start testing Ariane all you need is to step into the `riscv-torture/` folder and issue:
```
make rgentest
```
Which will produce a single randomized program, runs it on Spike (see [Getting Started](#getting_started)) and on the RTL simulator (QuestaSim) by calling `ariane-run-torture`.

Torture's overnight tests work the same way, just call
```
make rnight
```

C (a.k.a. Verilator) tests are currently not supported.

# Contributing

Check out the [contribution guide](CONTRIBUTING.md)

# Test Overview

## User Mode Integer Tests

| **Test Name** |                **P/V**                | **Test Name** |                **P/V**                | **Test Name** |                **P/V**                |
|---------------|---------------------------------------|---------------|---------------------------------------|---------------|---------------------------------------|
| add           | :white_check_mark: :white_check_mark: | lb            | :white_check_mark: :white_check_mark: | sll           | :white_check_mark: :white_check_mark: |
| addi          | :white_check_mark: :white_check_mark: | lbu           | :white_check_mark: :white_check_mark: | slli          | :white_check_mark: :white_check_mark: |
| addiw         | :white_check_mark: :white_check_mark: | ld            | :white_check_mark: :white_check_mark: | slliw         | :white_check_mark: :white_check_mark: |
| addw          | :white_check_mark: :white_check_mark: | lh            | :white_check_mark: :white_check_mark: | sllw          | :white_check_mark: :white_check_mark: |
| and           | :white_check_mark: :white_check_mark: | lhu           | :white_check_mark: :white_check_mark: | slt           | :white_check_mark: :white_check_mark: |
| andi          | :white_check_mark: :white_check_mark: | lui           | :white_check_mark: :white_check_mark: | slti          | :white_check_mark: :white_check_mark: |
| auipc         | :white_check_mark: :white_check_mark: | lw            | :white_check_mark: :white_check_mark: | sltiu         | :white_check_mark: :white_check_mark: |
| beq           | :white_check_mark: :white_check_mark: | lwu           | :white_check_mark: :white_check_mark: | sltu          | :white_check_mark: :white_check_mark: |
| bge           | :white_check_mark: :white_check_mark: | or            | :white_check_mark: :white_check_mark: | sra           | :white_check_mark: :white_check_mark: |
| bgeu          | :white_check_mark: :white_check_mark: | ori           | :white_check_mark: :white_check_mark: | srai          | :white_check_mark: :white_check_mark: |
| blt           | :white_check_mark: :white_check_mark: | sb            | :white_check_mark: :white_check_mark: | sraiw         | :white_check_mark: :white_check_mark: |
| bltu          | :white_check_mark: :white_check_mark: | sd            | :white_check_mark: :white_check_mark: | sraw          | :white_check_mark: :white_check_mark: |
| bne           | :white_check_mark: :white_check_mark: | sh            | :white_check_mark: :white_check_mark: | srl           | :white_check_mark: :white_check_mark: |
| sub           | :white_check_mark: :white_check_mark: | simple        | :white_check_mark: :white_check_mark: | srli          | :white_check_mark: :white_check_mark: |
| subw          | :white_check_mark: :white_check_mark: | jal           | :white_check_mark: :white_check_mark: | srliw         | :white_check_mark: :white_check_mark: |
| sw            | :white_check_mark: :white_check_mark: | jalr          | :white_check_mark: :white_check_mark: | srlw          | :white_check_mark: :white_check_mark: |
| xor           | :white_check_mark: :white_check_mark: |               |                                       |               |                                       |
| xori          | :white_check_mark: :white_check_mark: |               |                                       |               |                                       |

## Compressed Instruction Tests

| **Test Name** |                 **P/V**                 | **Test Name** | **P/V** | **Test Name** | **P/V** |
|---------------|-----------------------------------------|---------------|---------|---------------|---------|
| rvc           | :white_check_mark: :white_large_square: |               |         |               |         |

## Machine Mode Tests

| **Test Name** |     **P/F/U**      | **Test Name** |     **P/F/U**      | **Test Name** |     **P/F/U**      |
|---------------|--------------------|---------------|--------------------|---------------|--------------------|
| csr           | :white_check_mark: | illegal       | :white_check_mark: | mcsr          | :white_check_mark: |
| breakpoint    | Not Impl.          | ma_addr       | :white_check_mark: | ma_fetch      | :white_check_mark: |
| sbreak        | :white_check_mark: | scall         | :white_check_mark: |               |                    |

## Supervisor Mode Tests

| **Test Name** |     **P/F/U**      | **Test Name** |     **P/F/U**      | **Test Name** |     **P/F/U**      |
|---------------|--------------------|---------------|--------------------|---------------|--------------------|
| csr           | :white_check_mark: | dirty         | :white_check_mark: | ma_fetch      | :white_check_mark: |
| sbreak        | :white_check_mark: | scall         | :white_check_mark: | wfi           | :white_check_mark: |




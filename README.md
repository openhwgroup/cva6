[![build status](https://iis-git.ee.ethz.ch/floce/ariane/badges/master/build.svg)](https://iis-git.ee.ethz.ch/floce/ariane/commits/master)
[![coverage report](https://iis-git.ee.ethz.ch/floce/ariane/badges/master/coverage.svg)](https://iis-git.ee.ethz.ch/floce/ariane/commits/master)

# Ariane RISC-V CPU

![](docs/fig/ariane_overview.png)

For detailed documentation refer to the [online documentation](http://www.be4web.net/ariane/) (Login: `zarubaf` Password: `zaruba`).

## Getting Started
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
# Contributing

Check out the [contribution guide](CONTRIBUTING.md)

# Test Overview

## User Mode Integer Tests

| **Test Name** |                 **P/V**                 | **Test Name** |                **P/V**                 | **Test Name** |                 **P/V**                 |
|---------------|-----------------------------------------|---------------|----------------------------------------|---------------|-----------------------------------------|
| add           | :white_check_mark: :white_large_square: | lb            | :white_check_mark::white_large_square: | sll           | :white_check_mark: :white_check_mark:   |
| addi          | :white_check_mark: :white_large_square: | lbu           | :white_check_mark::white_large_square: | slli          | :white_check_mark: :white_large_square: |
| addiw         | :white_check_mark: :white_large_square: | ld            | :white_check_mark::white_large_square: | slliw         | :white_check_mark: :white_large_square: |
| addw          | :white_check_mark: :white_large_square: | lh            | :white_check_mark::white_large_square: | sllw          | :white_check_mark: :white_large_square: |
| and           | :white_check_mark: :white_large_square: | lhu           | :white_check_mark::white_large_square: | slt           | :white_check_mark: :white_large_square: |
| andi          | :white_check_mark: :white_large_square: | lui           | :white_check_mark::white_large_square: | slti          | :white_check_mark: :white_large_square: |
| auipc         | :white_check_mark: :white_large_square: | lw            | :white_check_mark::white_large_square: | sltiu         | :white_check_mark: :white_large_square: |
| beq           | :white_check_mark: :white_large_square: | lwu           | :white_check_mark::white_large_square: | sltu          | :white_check_mark: :white_large_square: |
| bge           | :white_check_mark: :white_large_square: | or            | :white_check_mark::white_large_square: | sra           | :white_check_mark: :white_large_square: |
| bgeu          | :white_check_mark: :white_large_square: | ori           | :white_check_mark::white_large_square: | srai          | :white_check_mark: :white_large_square: |
| blt           | :white_check_mark: :white_large_square: | sb            | :white_check_mark::white_large_square: | sraiw         | :white_check_mark: :white_large_square: |
| bltu          | :white_check_mark: :white_large_square: | sd            | :white_check_mark::white_check_mark:   | sraw          | :white_check_mark: :white_large_square: |
| bne           | :white_check_mark: :white_large_square: | sh            | :white_check_mark::white_large_square: | srl           | :white_check_mark: :white_check_mark:   |
| sub           | :white_check_mark: :white_large_square: | simple        | :white_check_mark::white_large_square: | srli          | :white_check_mark: :white_large_square: |
| subw          | :white_check_mark: :white_large_square: | jal           | :white_check_mark::white_large_square: | srliw         | :white_check_mark: :white_large_square: |
| sw            | :white_check_mark: :white_large_square: | jalr          | :white_check_mark::white_large_square: | srlw          | :white_check_mark: :white_large_square: |
| xor           | :white_check_mark: :white_large_square: |               |                                        |               |                                         |
| xori          | :white_check_mark: :white_large_square: |               |                                        |               |                                         |

## Compressed Instruction Tests

| **Test Name** |                **P/V**                 | **Test Name** | **P/V** | **Test Name** | **P/V** |
|---------------|----------------------------------------|---------------|---------|---------------|---------|
| rvc           | :white_check_mark::white_large_square: |               |         |               |         |

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




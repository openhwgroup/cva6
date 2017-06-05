[![build status](https://iis-git.ee.ethz.ch/floce/ariane/badges/initial-dev/build.svg)](https://iis-git.ee.ethz.ch/floce/ariane/commits/initial-dev)
[![coverage report](https://iis-git.ee.ethz.ch/floce/ariane/badges/initial-dev/coverage.svg)](https://iis-git.ee.ethz.ch/floce/ariane/commits/initial-dev)

# Ariane RISC-V CPU

![](docs/fig/ariane_overview.png)

For detailed documentation refer to the [online documentation](http://www.be4web.net/ariane/) (Login: `zarubaf` Password: `zaruba`).

## Getting Started

Checkout the repository and initialize all submodules
```
git checkout git@iis-git.ee.ethz.ch:floce/ariane.git
git submodule update --init --recursive
```
Build the RISC-V front-end server (fesvr) which contains utility functions to read and load ELF files.
```
make build-fesvr
```

Build Ariane by using the Makefile:
```
make build
```

Start the simulation using Modelsim:
```
make sim
```

Or start any of the unit tests by:
```
make dcache_arbiter
```
# Contributing

Check out the [contribution guide](CONTRIBUTING.md)

# Test Overview

| **Test Name** |      **P/F/U**       | **Test Name** |      **P/F/U**       | **Test Name** |      **P/F/U**       |
|---------------|----------------------|---------------|----------------------|---------------|----------------------|
| add           | :white_check_mark:   | lb            | :white_large_square: | sll           | :white_check_mark:   |
| addi          | :white_check_mark:   | lbu           | :white_large_square: | slli          | :white_check_mark:   |
| addiw         | :white_check_mark:   | ld            | :white_large_square: | slliw         | :white_check_mark:   |
| addw          | :white_check_mark:   | lh            | :white_large_square: | sllw          | :white_check_mark:   |
| and           | :white_check_mark:   | lhu           | :white_large_square: | slt           | :white_large_square: |
| andi          | :white_check_mark:   | lui           | :white_large_square: | slti          | :white_large_square: |
| auipc         | :white_check_mark:   | lw            | :white_large_square: | sltiu         | :white_large_square: |
| beq           | :white_check_mark:   | lwu           | :white_large_square: | sltu          | :white_large_square: |
| bge           | :white_check_mark:   | or            | :white_check_mark:   | sra           | :white_check_mark:   |
| bgeu          | :white_check_mark:   | ori           | :white_check_mark:   | srai          | :white_check_mark:   |
| blt           | :white_check_mark:   | sb            | :white_large_square: | sraiw         | :white_check_mark:   |
| bltu          | :white_check_mark:   | sd            | :white_large_square: | sraw          | :white_check_mark:   |
| bne           | :white_check_mark:   | sh            | :white_large_square: | srl           | :white_check_mark:   |
| sub           | :white_check_mark:   | simple        | :white_check_mark:   | srli          | :white_check_mark:   |
| subw          | :white_check_mark:   | jal           | :white_check_mark:   | srliw         | :white_check_mark:   |
| sw            | :white_large_square: | jalr          | :white_check_mark:   | srlw          | :white_check_mark:   |
| xor           | :white_check_mark:   |               |                      |               |                      |
| xori          | :white_check_mark:   |               |                      |               |                      |

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

| **Test Name** |     **P/F/U**      | **Test Name** | **P/F/U** |
|---------------|--------------------|---------------|-----------|
| add           | :white_check_mark: |               |           |
| addi          | :white_check_mark: |               |           |
| addiw         | :white_check_mark: |               |           |
| addw          | :white_check_mark: |               |           |
| and           | :white_check_mark: |               |           |
| andi          | :white_check_mark: |               |           |
| auipc         | :white_check_mark: |               |           |
| beq           | :white_check_mark: |               |           |
| bge           | :white_check_mark: |               |           |
| bgeu          | :white_check_mark: |               |           |
| blt           | :white_check_mark: |               |           |
| bltu          | :white_check_mark: |               |           |
| bne           | :white_check_mark: |               |           |

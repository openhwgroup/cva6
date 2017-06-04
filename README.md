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
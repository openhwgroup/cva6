#!/bin/bash
echo "exporting RISCV"

export PATH=/scratch/lvalente/riscv_install/bin:$PATH

export RISCV=/scratch/lvalente/riscv_install

export SW_HOME=$(pwd)/software

echo "exporting QUESTASIM PATH"

export QUESTASIM_HOME=/usr/pack/modelsim-10.7b-kgf/questasim/

echo "cloning submodules"

git submodule update --init --recursive


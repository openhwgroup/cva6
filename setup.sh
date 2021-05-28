#!/bin/bash
echo "exporting RISCV"

export PATH=/scratch/lvalente/riscv_install/bin:$PATH

export RISCV=/scratch/lvalente/riscv_install

echo "exporting QUESTASIM PATH"

export QUESTASIM_HOME=/usr/pack/modelsim-10.7b-kgf/questasim/

echo "cloning submodules"

git submodule update --init --recursive


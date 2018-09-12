# Customise this to a fast local disk
export TOP=/usr/scratch2/toscana/michscha/
export CI_BUILD_DIR=$TOP/ariane-dev

#customize this to your setup
export QUESTASIM_HOME=/usr/pack/modelsim-10.6b-kgf/questasim/
export QUESTASIM_VERSION=-10.6b
export QUESTASIM_FLAGS=-noautoldlibpath
export CXX=g++-7.2.0 CC=gcc-7.2.0


# where to install the tools
export RISCV=$TOP/riscv_install
export VERILATOR_ROOT=$TOP/verilator-3.924/

export PATH=$RISCV/bin:$VERILATOR_ROOT/bin:$PATH
export LIBRARY_PATH=$RISCV/lib
export LD_LIBRARY_PATH=$RISCV/lib:/usr/pack/gcc-7.2.0-af/linux-x64/lib64/
export C_INCLUDE_PATH=$RISCV/include:$VERILATOR_ROOT/include:/usr/pack/gcc-7.2.0-af/linux-x64/include
export CPLUS_INCLUDE_PATH=$RISCV/include:$VERILATOR_ROOT/include:/usr/pack/gcc-7.2.0-af/linux-x64/include

# number of parallel jobs to use for make commands and simulation
export NUM_JOBS=8

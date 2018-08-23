# Customise this to a fast local disk
export TOP=/scratch/$USER/projects
export CI_BUILD_DIR=$TOP/ariane-repo

#customize this to your setup
export QUESTASIM_HOME=
export QUESTASIM_VERSION=
export CXX=g++-4.8 CC=gcc-4.8

# where to install the tools
export RISCV=$TOP/riscv_install
export VERILATOR_ROOT=$TOP/verilator-3.924/

export PATH=$RISCV/bin:$VERILATOR_ROOT/bin:$PATH
export LIBRARY_PATH=$CI_BUILD_DIR/tmp/lib
export LD_LIBRARY_PATH=$CI_BUILD_DIR/tmp/lib
export C_INCLUDE_PATH=$CI_BUILD_DIR/tmp/include:$VERILATOR_ROOT/include
export CPLUS_INCLUDE_PATH=$CI_BUILD_DIR/tmp/include:$VERILATOR_ROOT/include

# number of parallel jobs to use for make commands and simulation
export NUM_JOBS=8

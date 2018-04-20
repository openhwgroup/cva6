# This script emulates what travis check in test does on the public server
# comment out next command if you don't want to use sudo
sudo apt install \
      gcc-4.8 \
      g++-4.8 \
      gperf \
      autoconf \
      automake \
      autotools-dev \
      libmpc-dev \
      libmpfr-dev \
      libgmp-dev \
      gawk \
      build-essential \
      bison \
      flex \
      texinfo \
      python-pexpect \
      libusb-1.0-0-dev \
      device-tree-compiler
# Customise this to a fast local disk
export TOP=/local/scratch/$USER
export TRAVIS_BUILD_DIR=$TOP/ariane-isatest
export RISCV=$TOP/riscv_install
export PATH=$TOP/riscv_install/bin:$TRAVIS_BUILD_DIR/tmp/bin:$PATH
export CXX=g++-4.8 CC=gcc-4.8
ci/make-tmp.sh
export LIBRARY_PATH=$TRAVIS_BUILD_DIR/tmp/lib
export LD_LIBRARY_PATH=$TRAVIS_BUILD_DIR/tmp/lib
export C_INCLUDE_PATH=$TRAVIS_BUILD_DIR/tmp/include
export CPLUS_INCLUDE_PATH=$TRAVIS_BUILD_DIR/tmp/include
export VERILATOR_ROOT=$TRAVIS_BUILD_DIR/tmp/verilator-3.918/
ci/build-riscv-gcc.sh
ci/install-verilator.sh
ci/install-fesvr.sh
ci/build-riscv-tests.sh
make run-asm-tests-verilator

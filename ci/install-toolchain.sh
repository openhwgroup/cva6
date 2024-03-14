
export PATH=$RISCV/bin:/bin:$PATH
export LIBRARY_PATH=$RISCV/lib
export LD_LIBRARY_PATH=$RISCV/lib
export C_INCLUDE_PATH=$RISCV/include
export CPLUS_INCLUDE_PATH=$RISCV/include

EMBECOSM_BASE=https://buildbot.embecosm.com/job/riscv32-gcc-ubuntu2204-release/10/artifact

mkdir -p $RISCV && chmod 777 $RISCV

[ ! -d $RISCV ] && sudo mkdir -p $RISCV && sudo chmod 777 $RISCV

if [ ! -d $RISCV/bin ]; then
    RISCV64_UNKNOWN_ELF_GCC=riscv32-embecosm-ubuntu2204-gcc13.2.0.tar.gz
    if [ ! -f "$RISCV64_UNKNOWN_ELF_GCC" ]; then
        wget $EMBECOSM_BASE/$RISCV64_UNKNOWN_ELF_GCC --no-check-certificate
    fi
    tar -x -f $RISCV64_UNKNOWN_ELF_GCC --strip-components=1 -C $RISCV
fi

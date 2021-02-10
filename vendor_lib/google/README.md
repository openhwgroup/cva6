### Google
Verification components from Google and CORE-V specific extensions and updates to same.

**riscv-dv**: location where the Google RISC-V Instruction Stream Generator is cloned to.

In order to use riscv-dv the following shell ENV variables must be set (values are examples only):
```
export DSIM="/tools/Metrics/dsim/20190802.10.1/bin/dsim"
export DSIM_LIB_PATH="/tools/Metrics/dsim/20190802.10.1/uvm-1.2/src/dpi"
export RISCV_GCC="/opt/riscv/bin/riscv32-unknown-elf-gcc"
export RISCV_OBJCOPY="/opt/riscv/bin/riscv32-unknown-elf-objcopy"
export SPIKE_PATH="/opt/riscv-64/bin/spike"
export RISCV_DV_ROOT="/data/mike/GitHubRepos/openhwgroup/core-v-verif/isg_tests/vendor_lib/google/riscv-dv"
```

# CVA6 Development Guide

## Building & Testing
- Build all: `make`
- Run simulation: `source verif/sim/setup-env.sh` then:
- Single test: `cd verif/sim && python3 cva6.py --target cv64a6_imafdc_sv39 --iss=veri-testharness --c_tests=/path/to/test.c`
- Run regression: `export DV_SIMULATORS=veri-testharness,spike && bash verif/regress/dv-riscv-arch-test.sh`
- Generate waveforms: `export TRACE_FAST=1` or `export TRACE_COMPACT=1` before running tests
- Enable coverage: `export cov=1` before running tests
- Run hello_world example: 
  ```
  cd /home/cai/cache_project/sandbox/cva6 && 
  source verif/sim/setup-env.sh && 
  cd ./verif/sim && 
  python3 cva6.py --target cv32a60x --iss=veri-testharness --iss_yaml=cva6.yaml \
  --c_tests ../tests/custom/hello_world/hello_world.c \
  --linker=../../config/gen_from_riscv_config/linker/link.ld \
  --gcc_opts="-static -mcmodel=medany -fvisibility=hidden -nostdlib \
  -nostartfiles -g ../tests/custom/common/syscalls.c \
  ../tests/custom/common/crt.S -lgcc \
  -I../tests/custom/env -I../tests/custom/common"
  ```

## Code Style
- RTL formatting: `verible-verilog-format --inplace $(git ls-tree -r HEAD --name-only core |grep '\.sv$' |grep -v '^core/include/std_cache_pkg.sv$' |grep -v cvfpu)`
- Naming: Parameters/defines: `UPPER_CASE`, modules/variables: `lower_case_with_underscores`
- Indentation: Follow lowRISC style guide - 2 spaces, no tabs
- Commits: 50 char subject line, imperative mood, present tense, explain what/why

## Git Workflow
- Never push to master, use feature branches
- Branch naming: `<type>/<description>` (e.g., `feature/new-component`, `fix/issue-123`)
- New features must be optional and disabled by default
- PRs require passing CI and including regression tests for new functionality
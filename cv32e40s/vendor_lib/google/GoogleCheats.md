## RISCV-DV Cheat Sheet

### tests

```
riscv_arithmetic_basic_test
riscv_rand_instr_test
riscv_jump_stress_test
riscv_loop_test
riscv_rand_jump_test
riscv_mmu_stress_test
riscv_no_fence_test
riscv_illegal_instr_test
riscv_ebreak_test
riscv_ebreak_debug_mode_test
riscv_full_interrupt_test
riscv_csr_test
riscv_unaligned_load_store_test
```

### Useful (?) examples

```
$ rm -rf out_2020-07-03 metrics* dsim.env
$ python3 ./run.py -si dsim --target rv32imc --steps gen --test riscv_arithmetic_basic_test
$ python3 ./run.py -si dsim --target rv32imc --steps gen --test riscv_rand_instr_test
$ python3 ./run.py -si dsim --target rv32imc --steps gen -v --test riscv_rand_instr_test
$ python3 ./run.py -si dsim --target rv32imc --steps gen -v --test riscv_jump_stress_test
```

### CSR Testing

Unlike all the other tests, which are produced by a SystemVerilog/UVM program, the CSR test is generated
by a Python3 script using a YAML file to specify the CSRs.  To run it:
```
$ python3 ./riscv-dv/scripts/gen_csr_test.py --csr_file corev-dv/cv32e40s_csr_template.yaml --out ./corev-dv
```

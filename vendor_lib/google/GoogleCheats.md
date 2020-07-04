## RISCV-DV Cheat Sheet

### tests
riscv\_arithmetic\_basic\_test
riscv\_rand\_instr\_test
riscv\_jump\_stress\_test
riscv\_loop\_test
riscv\_rand\_jump\_test
riscv\_mmu\_stress\_test
riscv\_no\_fence\_test
riscv\_illegal\_instr\_test
riscv\_ebreak\_test
riscv\_ebreak\_debug\_mode\_test
riscv\_full\_interrupt\_test
riscv\_csr\_test
riscv\_unaligned\_load\_store\_test

### Useful (?) examples
$ python3 ./run.py -si dsim --target rv32imc --steps gen --test riscv\_arithmetic\_basic\_test
$ rm -rf out\_2020-07-03/ metrics\* dsim.env 
$ python3 ./run.py -si dsim --target rv32imc --steps gen --test riscv\_rand\_instr\_test
$ python3 ./run.py -si dsim --target rv32imc --steps gen --test riscv\_rand\_instr\_test -v
$ python3 ./run.py -si dsim --target rv32imc --steps gen -v --test riscv\_jump\_stress\_test
$ python3 ./run.py -si dsim --target rv32imc --steps gen -v --test riscv\_arithmetic\_basic\_test

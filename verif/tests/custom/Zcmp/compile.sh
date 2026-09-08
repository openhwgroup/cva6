#!/bin/bash
riscv64-unknown-elf-gcc -static -mcmodel=medany -fvisibility=hidden -nostdlib -g syscalls.c -lgcc -Tlink.ld -march=rv32imf_zcmp_zicsr -mabi=ilp32 -o cm_push_pop_test_rv32.elf cm_push_pop_test.S -I ../env
riscv64-unknown-elf-gcc -static -mcmodel=medany -fvisibility=hidden -nostdlib -g syscalls.c -lgcc -Tlink.ld -march=rv32imf_zcmp_zicsr -mabi=ilp32 -o cm_popret_test_rv32.elf   cm_popret_test.S   -I ../env
riscv64-unknown-elf-gcc -static -mcmodel=medany -fvisibility=hidden -nostdlib -g syscalls.c -lgcc -Tlink.ld -march=rv32imf_zcmp_zicsr -mabi=ilp32 -o cm_popretz_test_rv32.elf  cm_popretz_test.S  -I ../env
riscv64-unknown-elf-gcc -static -mcmodel=medany -fvisibility=hidden -nostdlib -g syscalls.c -lgcc -Tlink.ld -march=rv32imf_zcmp_zicsr -mabi=ilp32 -o cm_mva01s_test_rv32.elf   cm_mva01s_test.S   -I ../env
riscv64-unknown-elf-gcc -static -mcmodel=medany -fvisibility=hidden -nostdlib -g syscalls.c -lgcc -Tlink.ld -march=rv32imf_zcmp_zicsr -mabi=ilp32 -o cm_mvsa01_test_rv32.elf   cm_mvsa01_test.S   -I ../env

riscv64-unknown-elf-gcc -static -mcmodel=medany -fvisibility=hidden -nostdlib -g syscalls.c -lgcc -Tlink.ld -march=rv64imd_zcmp_zicsr -mabi=lp64d -o cm_push_pop_test_rv64.elf cm_push_pop_test.S -I ../env
riscv64-unknown-elf-gcc -static -mcmodel=medany -fvisibility=hidden -nostdlib -g syscalls.c -lgcc -Tlink.ld -march=rv64imd_zcmp_zicsr -mabi=lp64d -o cm_popret_test_rv64.elf   cm_popret_test.S   -I ../env
riscv64-unknown-elf-gcc -static -mcmodel=medany -fvisibility=hidden -nostdlib -g syscalls.c -lgcc -Tlink.ld -march=rv64imd_zcmp_zicsr -mabi=lp64d -o cm_popretz_test_rv64.elf  cm_popretz_test.S  -I ../env
riscv64-unknown-elf-gcc -static -mcmodel=medany -fvisibility=hidden -nostdlib -g syscalls.c -lgcc -Tlink.ld -march=rv64imd_zcmp_zicsr -mabi=lp64d -o cm_mva01s_test_rv64.elf   cm_mva01s_test.S   -I ../env
riscv64-unknown-elf-gcc -static -mcmodel=medany -fvisibility=hidden -nostdlib -g syscalls.c -lgcc -Tlink.ld -march=rv64imd_zcmp_zicsr -mabi=lp64d -o cm_mvsa01_test_rv64.elf   cm_mvsa01_test.S   -I ../env



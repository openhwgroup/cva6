Use the following command to build the test binaries (example for cm_push_pop_test.S):
		riscv32-corev-elf-gcc -static -mcmodel=medany -fvisibility=hidden -nostdlib -g syscalls.c -lgcc -Tlink.ld -march=rv32gc_zcmp -o cm_push_pop_test.elf cm_push_pop_test.S

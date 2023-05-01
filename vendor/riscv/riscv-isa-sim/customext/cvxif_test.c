// Copyright (C) 2022 Thales DIS Design Services SAS
//
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0.
//
// Original Author: Zbigniew CHAMSKI <zbigniew.chamski@thalesgroup.com>
//
// The following is a RISC-V program to test the functionality of the
// basic CVXIF accelerator interface on the Core-V side.
// Compile using "riscv-none-elf-gcc -O2 cvxif_test.elf cvxif_test.c"
// with -march=/-mabi= settings appropriate for your project.
// Run using "spike -l --extension=cvxif cvxif_test.elf", adding
// an --isa= setting appropriate for your project.
//
// Upon simulating the compiled program, the trace should contain five
// instances of custom3 instructions (the third one being decoded as
// 'unknown').
// The last occurrence of 'custom3' instruction in the trace, encoded as
// 0x8002007b, should be immediately followed by exception
// 'trap_load_address_misaligned' with a tval equal to 0x1 and the
// execution should terminate correctly with exit code 0.
//
// In 64-bit mode, the trace of the last occurrence of custom3
// instruction should be equivalent to
//
//      core   0: 0x0000000080002686 (0x8002007b) custom3 (args unknown)
//      core   0: exception trap_load_address_misaligned, epc 0x0000000080002686
//      core   0:           tval 0x0000000000000001
//
// The corresponding trace in 32-bit mode should be equivalent to
//
//       core   0: 0x8000205a (0x8002007b) custom3 (args unknown)
//       core   0: exception trap_load_address_misaligned, epc 0x8000205a
//       core   0:           tval 0x00000001

#include <assert.h>
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>

// Values of MCAUSE corresponding to exceptions coming from the coprocessor I/F
#define CAUSE_MISALIGNED_LOAD 0x4
#define CAUSE_LOAD_ACCESS 0x5
#define CAUSE_MISALIGNED_STORE 0x6
#define CAUSE_STORE_ACCESS 0x7
#define CAUSE_LOAD_PAGE_FAULT 0xd
#define CAUSE_STORE_PAGE_FAULT 0xf
#define CAUSE_COPROCESSOR_EXCEPTION 0x20

// Value of TVAL to pass around.
#define COPRO_TVAL_TEST 0x1a

// Macro to read a CSR (from spike's "encoding.h")
#define read_csr(reg) ({ unsigned long __tmp; \
  asm volatile ("csrr %0, " #reg : "=r"(__tmp)); \
  __tmp; })

int main() {
  // "unsigned long int" is always XLEN bits wide.
  unsigned long int x = 123, y = 456, z = 0, t = 0;
  static unsigned long int amem = 111, bmem = 0;
  unsigned long a;

  // Add x + y into z.  Funct7 == 0, funct3 == 0x0.
  asm volatile (".insn r CUSTOM_3, 0, 0, %0, %1, %2" : "=r"(z) : "r"(x), "r"(y));
  if (z != 123 + 456)
  {
    //  printf("FAILURE!!!\n");
    return 1;
  }

  // Add three operands in a single R4-type add.
  // Leverage current values of x, y and z (z == x + y).
  asm volatile (".insn r CUSTOM_3, 0, 0x1, %0, %1, %2, %3" : "=r"(t) : "r"(x), "r"(y), "r"(z));
  if (t != x + y + z)
  {
    // printf("FAILURE");
    return 2;
  }
  // Load 'a' from 'amem'. CUSTOM_LD: opcode == CUSTOM_3, insn_type == I, funct3 == 0x1.
  asm volatile (".insn i CUSTOM_3, 0x1, %0, %1" : "=r"(a) : "m"(amem), "I"(0));
  if (a != 111)
  {
    //  printf("FAILURE!!!\n");
    return 3;
  }

  // Store 'a' in 'bmem'. CUSTOM_SD: opcode == CUSTOM_3, insn_type == S, funct3 == 0x2.
  asm volatile (".insn s CUSTOM_3, 0x2, %0, %1" : : "r"(a), "m"(bmem));
  if (bmem != 111)
  {
    //  printf("FAILURE!!!\n");
    return 4;
  }

  // Generate a misaligned load exception (mcause == 0x4).
  asm volatile  (".insn r CUSTOM_3, 0x0, 0x40, x0, x4, x0" : : );

  // If we get here, then the exception test failed ==> exit with general failure code.
  exit(1337);
}

// Override default trap handler.
uintptr_t handle_trap(uintptr_t cause, uintptr_t epc, uintptr_t regs[32])
{
  if (cause == CAUSE_MISALIGNED_LOAD)
    // Successfully terminate.
    exit(0);
  else
    // Fail with explicit retcode.
    exit(5);
}

#include <stdio.h>
#include <stdlib.h>

#define CPUADDR_CPUCTRL     0xBF0
#define CPUADDR_SECURESEED0 0xBF9
#define CPUADDR_SECURESEED1 0xBFA
#define CPUADDR_SECURESEED2 0xBFC

// Macros for using defines in inline asm
#define S(x) #x
#define STR(s) S(s)

int main(void) {
  uint32_t rd;
  const uint32_t rs1 = 0xFFFFFFFF;

  printf("Test cpuctrl\n");
  __asm__ volatile("csrr  %0, " STR(CPUADDR_CPUCTRL)          : "=r"(rd));
  __asm__ volatile("csrwi     " STR(CPUADDR_CPUCTRL) ", 0xF");
  __asm__ volatile("csrrs %0, " STR(CPUADDR_CPUCTRL) ", %1"   : "=r"(rd) : "r"(rs1));
  __asm__ volatile("csrrc %0, " STR(CPUADDR_CPUCTRL) ", %1"   : "=r"(rd) : "r"(rs1));

  printf("Test secureseed0\n");
  __asm__ volatile("csrr  %0, " STR(CPUADDR_SECURESEED0)          : "=r"(rd));
  __asm__ volatile("csrwi     " STR(CPUADDR_SECURESEED0) ", 0xF");
  __asm__ volatile("csrrs %0, " STR(CPUADDR_SECURESEED0) ", %1"   : "=r"(rd) : "r"(rs1));
  __asm__ volatile("csrrc %0, " STR(CPUADDR_SECURESEED0) ", %1"   : "=r"(rd) : "r"(rs1));

  printf("Test secureseed1\n");
  __asm__ volatile("csrr  %0, " STR(CPUADDR_SECURESEED1)          : "=r"(rd));
  __asm__ volatile("csrwi     " STR(CPUADDR_SECURESEED1) ", 0xF");
  __asm__ volatile("csrrs %0, " STR(CPUADDR_SECURESEED1) ", %1"   : "=r"(rd) : "r"(rs1));
  __asm__ volatile("csrrc %0, " STR(CPUADDR_SECURESEED1) ", %1"   : "=r"(rd) : "r"(rs1));

  printf("Test secureseed2\n");
  __asm__ volatile("csrr  %0, " STR(CPUADDR_SECURESEED2)          : "=r"(rd));
  __asm__ volatile("csrwi     " STR(CPUADDR_SECURESEED2) ", 0xF");
  __asm__ volatile("csrrs %0, " STR(CPUADDR_SECURESEED2) ", %1"   : "=r"(rd) : "r"(rs1));
  __asm__ volatile("csrrc %0, " STR(CPUADDR_SECURESEED2) ", %1"   : "=r"(rd) : "r"(rs1));

  // Test the one particular line that first caught a problem
  __asm__ volatile("csrwi 0xBF0, 0x2");

  printf("Test xsecure_csrs done\n");
  return EXIT_SUCCESS;
}

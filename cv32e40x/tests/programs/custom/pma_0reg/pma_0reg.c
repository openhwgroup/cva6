// TODO license header

#include <stdio.h>
#include <stdlib.h>

#define  ADDR  0x1A110800  // Repurposing the dbg section because it is otherwise not occupied in this test

void u_sw_irq_handler(void) {  // overrides a "weak" symbol in the bsp
  printf("u_sw_irq_handler: exception occured\n");
  exit(EXIT_FAILURE);
}

int main(void) {
  uint32_t tmp;

  printf("\nhello pma_0reg\n\n");


  // Misaligned should pass

  // Misaligned load should pass
  __asm__ volatile("lh %0, 7(%1)" : "=r"(tmp) : "r"(ADDR));  // would except and not continue if anything went wrong

  // Misaligned store should pass
  __asm__ volatile("sw %0, 9(%1)" : "=r"(tmp) : "r"(ADDR));


  // Atomics should pass

  // Load-reserved should pass
  /* TODO enable when RTL is implemented
  __asm__ volatile("lr.w %0, (%1)" : "=r"(tmp) : "r"(ADDR + 8));
  */

  // Store-conditional should pass
  /* TODO enable when RTL is implemented
  __asm__ volatile("sc.w %0, %0, (%1)" : "=r"(tmp) : "r"(ADDR + 12));
  */


  printf("\ngoodbye pma_0reg\n\n");
  return EXIT_SUCCESS;
}

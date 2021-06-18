// TODO license header

#include <stdio.h>
#include <stdlib.h>

#define  DEBUG_REQ_CONTROL_REG  *(volatile int *)0x15000008

typedef union {
  struct {
    unsigned int start_delay      : 15; // 14: 0
    unsigned int rand_start_delay : 1;  //    15
    unsigned int pulse_width      : 13; // 28:16
    unsigned int rand_pulse_width : 1;  //    29
    unsigned int pulse_mode       : 1;  //    30    0 = level, 1 = pulse
    unsigned int value            : 1;  //    31
  } fields;
  unsigned int bits;
} debug_req_control_t;

volatile int g_debug_entered = 0;

/*
static void set_ebreakm(void) {
  uint32_t dcsr;

  __asm__ volatile("csrr %0, dcsr": "=r"(dcsr));
  printf("dcsr = 0x%lx\n", dcsr);
  //TODO set it
}
*/

__attribute__((naked))
void debugger_epilogue(void) {
  asm("la sp, __debugger_stack_start");
  asm("addi sp, sp, 0x80");  // get top of stack region

  asm("lw a0, -8(sp)");
  asm("lw a1, -12(sp)");
  asm("lw a2, -16(sp)");
  asm("lw a3, -20(sp)");
  asm("lw a4, -24(sp)");
  asm("lw a5, -28(sp)");
  asm("lw a6, -32(sp)");
  asm("lw a7, -36(sp)");

  asm("lw t0, -40(sp)");
  asm("lw t1, -44(sp)");
  asm("lw t2, -48(sp)");
  asm("lw t3, -52(sp)");
  asm("lw t4, -56(sp)");
  asm("lw t5, -60(sp)");
  asm("lw t6, -64(sp)");

  asm("lw ra, -4(sp)");
  asm("csrr sp, dscratch");

  __asm__ volatile("dret");
  while (1)
    ;
}

void debugger(void) {
  uint32_t dpc;
  uint32_t dcsr;

  g_debug_entered = 1;

  printf("hello from debugger()\n");

  __asm__ volatile("csrr %0, dpc": "=r"(dpc));
  printf("dpc = 0x%lx\n", dpc);

  __asm__ volatile("csrr %0, dcsr": "=r"(dcsr));
  printf("dcsr = 0x%lx\n", dcsr);
  printf("dcsr.cause = 0x%lx\n", ((dcsr >> 6) & 0x7));

  debugger_epilogue();
}

__attribute__((naked))
void debugger_prologue(void) {
  // assuming "sp" and "ra" are already saved and set

  asm("sw a0, -8(sp)");
  asm("sw a1, -12(sp)");
  asm("sw a2, -16(sp)");
  asm("sw a3, -20(sp)");
  asm("sw a4, -24(sp)");
  asm("sw a5, -28(sp)");
  asm("sw a6, -32(sp)");
  asm("sw a7, -36(sp)");

  asm("sw t0, -40(sp)");
  asm("sw t1, -44(sp)");
  asm("sw t2, -48(sp)");
  asm("sw t3, -52(sp)");
  asm("sw t4, -56(sp)");
  asm("sw t5, -60(sp)");
  asm("sw t6, -64(sp)");

  //asm("addi sp, sp, -64");
  asm("csrr sp, dscratch");  // use "normal" stack, not the tiny debug stack

  debugger();
  while (1)
    ;
}

__attribute__((section(".debugger"), naked))
void debugger_entry(void) {
  asm("csrw dscratch, sp");
  asm("la sp, __debugger_stack_start");
  asm("addi sp, sp, 0x80");  // get top of stack region
  asm("sw ra, -4(sp)");
  debugger_prologue();
}

int main(void) {
  debug_req_control_t debug_req_control;

  printf("\nhello pma_debug\n\n");

  debug_req_control = (debug_req_control_t) {
    .fields.start_delay      = 0,
    .fields.rand_start_delay = 0,
    .fields.pulse_width      = 5,  // FIXME: BUG: one clock pulse cause core to lock up
    .fields.rand_pulse_width = 0,
    .fields.pulse_mode       = 1,
    .fields.value            = 1,
  };
  DEBUG_REQ_CONTROL_REG = debug_req_control.bits;
  printf("requested debug mode\n");
  while (!g_debug_entered)
    ;

  printf("\ngoodbye pma_debug\n\n");
  return EXIT_SUCCESS;
}

/*
**
** Copyright 2020 OpenHW Group
**
** Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
** you may not use this file except in compliance with the License.
** You may obtain a copy of the License at
**
**     https://solderpad.org/licenses/
**
** Unless required by applicable law or agreed to in writing, software
** distributed under the License is distributed on an "AS IS" BASIS,
** WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
** See the License for the specific language governing permissions and
** limitations under the License.
**
*******************************************************************************
** Basic debugger test. Needs more work and bugs fixed
** It will launch a debug request and have debugger code execute (debugger.S)
*******************************************************************************
*/

#include <stdio.h>
#include <stdlib.h>
#include "corev_uvmt.h"

volatile int glb_hart_status  = 0; // Written by main code only, read by debug code
volatile int glb_debug_status = 0; // Written by debug code only, read by main code
volatile int glb_ebreak_status = 0; // Written by ebreak code only, read by main code
volatile int glb_illegal_insn_status = 0; // Written by illegal instruction code only, read by main code
volatile int glb_debug_exception_status = 0; // Written by debug code during exception only
volatile int glb_exception_ebreak_status = 0; // Written by main code, read by exception handler

// Expectation flags. Raise an error if handler or routine is enterred when not expected,
volatile int glb_expect_illegal_insn    = 0;
volatile int glb_expect_ebreak_handler  = 0;
volatile int glb_expect_debug_entry     = 0;
volatile int glb_expect_debug_exception = 0;
volatile int glb_expect_irq_entry = 0;
// Counter values
// Checked at start and end of debug code
// Only lower 32 bits checked, as simulation cannot overflow on 32 bits
volatile int glb_mcycle_start = 0;
volatile int glb_mcycle_end = 0;
volatile int glb_minstret_start = 0;
volatile int glb_minstret_end = 0;
#define TEST_FAILED  *(volatile int *)CV_VP_STATUS_FLAGS_BASE = 1
#define TEST_PASSED  *(volatile int *)CV_VP_STATUS_FLAGS_BASE = 123456789

extern int __stack_start;
extern int _trigger_code;
extern int _trigger_code_ebreak;
extern int _trigger_code_cebreak;
extern int _trigger_code_illegal_insn;
extern int _trigger_code_branch_insn;
extern int _trigger_code_multicycle_insn;
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
}  debug_req_control_t;

#define DEBUG_REQ_CONTROL_REG *(volatile int *) CV_VP_DEBUG_CONTROL_BASE
#define TIMER_REG_ADDR         ((volatile uint32_t *) (CV_VP_INTR_TIMER_BASE+0))
#define TIMER_VAL_ADDR         ((volatile uint32_t *) (CV_VP_INTR_TIMER_BASE+4))

typedef union {
  struct {
    unsigned int uie   : 1;  //     0 // Implemented if USER mode enabled
    unsigned int sie   : 1;  //     1
    unsigned int wpri  : 1;  //     2
    unsigned int mie   : 1;  //     3 // Implemented
    unsigned int upie  : 1;  //     4 // Implemented if USER mode enabled
    unsigned int spie  : 1;  //     5
    unsigned int wpri0 : 1;  //     6
    unsigned int mpie  : 1;  //     7 // Implemented
    unsigned int spp   : 1;  //     8
    unsigned int wpri1 : 2;  // 10: 9
    unsigned int mpp   : 2;  // 12:11 // Implemented
    unsigned int fs    : 2;  // 14:13
    unsigned int xs    : 2;  // 16:15
    unsigned int mprv  : 1;  //    17
    unsigned int sum   : 1;  //    18
    unsigned int mxr   : 1;  //    19
    unsigned int tvm   : 1;  //    20
    unsigned int tw    : 1;  //    21
    unsigned int tsr   : 1;  //    22
    unsigned int wpri3 : 8;  // 30:23
    unsigned int sd    : 1;  //    31
  } fields;
  unsigned int bits;
}  mstatus_t;

extern void _trigger_test(int d);
extern void _trigger_test_ebreak(int d);
extern void _trigger_test_combo();
extern void _single_step(int d);
// Tag is simply to help debug and determine where the failure came from
void check_debug_status(int tag, int value)
{
  if(glb_debug_status != value){
    printf("ERROR: check_debug_status(%d, %d): Tag=%d status=%d, exp=%d \n\n",
           tag, value, tag, glb_debug_status, value);
    TEST_FAILED;
  }
}
void check_debug_exception_status(int tag, int value)
{
  if(glb_debug_exception_status != value){
    printf("ERROR: check_debug_exception_status(%d, %d): Tag=%d status=%d, exp=%d \n\n",
           tag, value, tag, glb_debug_exception_status, value);
    TEST_FAILED;
  }
}
void check_hart_status(int tag, int value)
{
  if(glb_hart_status != value){
    printf("ERROR: check_hart_status(%d, %d): Tag=%d status=%d, exp=%d \n\n",
           tag, value, tag, glb_hart_status, value);
    TEST_FAILED;
  }
}
void check_ebreak_status(int tag, int value)
{
  if(glb_ebreak_status != value){
    printf("ERROR: check_ebreak_status(%d, %d): Tag=%d status=%d, exp=%d \n\n",
           tag, value, tag, glb_ebreak_status, value);
    TEST_FAILED;
  }
}
void check_illegal_insn_status(int tag, int value)
{
  if(glb_illegal_insn_status != value){
    printf("ERROR: check_illegal_insn_status(%d, %d): Tag=%d status=%d, exp=%d \n\n",
           tag, value, tag, glb_illegal_insn_status, value);
    TEST_FAILED;
  }
}
void delay(int count) {
    for (volatile int d = 0; d < count; d++);
}

void mstatus_mie_enable() {
    int mie_bit = 0x1 << 3;
    asm volatile("csrrs x0, mstatus, %0" : : "r" (mie_bit));
}

void mstatus_mie_disable() {
    int mie_bit = 0x1 << 3;
    asm volatile("csrrc x0, mstatus, %0" : : "r" (mie_bit));
}

void mie_enable_all() {
    uint32_t mie_mask = (uint32_t) -1;
    asm volatile("csrrs x0, mie, %0" : : "r" (mie_mask));
}

void mie_disable_all() {
    uint32_t mie_mask = (uint32_t) -1;
    asm volatile("csrrc x0, mie, %0" : : "r" (mie_mask));
}

void mie_enable(uint32_t irq) {
    // Enable the interrupt irq in MIE
    uint32_t mie_bit = 0x1 << irq;
    asm volatile("csrrs x0, mie, %0" : : "r" (mie_bit));
}

void mie_disable(uint32_t irq) {
    // Disable the interrupt irq in MIE
    uint32_t mie_bit = 0x1 << irq;
    asm volatile("csrrc x0, mie, %0" : : "r" (mie_bit));
}

void mm_ram_assert_irq(uint32_t mask, uint32_t cycle_delay) {
    *TIMER_REG_ADDR = mask;
    *TIMER_VAL_ADDR = 1 + cycle_delay;
}

void counters_enable() {
    // Enable counters mcycle (bit0) and minstret (bit2)
    uint32_t mask = 1<<2 | 1<<0;
    asm volatile("csrrc x0, 0x320, %0" : : "r" (mask));
}
#define MACHINE 3
int main(int argc, char *argv[])
{
    debug_req_control_t debug_req_control;
    counters_enable();

    // Enable interrupt
    mstatus_mie_enable();
    mie_enable(30);

    // Assembly code from here to get better control of timing
    _trigger_test_combo();

    printf("------------------------\n");
    printf("Finished \n");
    return EXIT_SUCCESS;
}

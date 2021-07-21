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

volatile int glb_hart_status  = 0; // Written by main code only, read by debug code
volatile int glb_debug_status = 0; // Written by debug code only, read by main code
volatile int glb_illegal_insn_status = 0; // Written by illegal instruction code only, read by main code

// Expectation flags. Raise an error if handler or routine is enterred when not expected,
volatile int glb_expect_illegal_insn    = 0;
volatile int glb_expect_debug_entry     = 0;
volatile int glb_expect_ebreak_handler = 0;
volatile int glb_expect_irq_entry = 0;
volatile int glb_exception_ebreak_status = 0;
volatile int glb_ebreak_status = 0;
#define TEST_FAILED  *(volatile int *)0x20000000 = 1
#define TEST_PASSED  *(volatile int *)0x20000000 = 123456789

extern int __stack_start; 
extern void _single_step(int d);
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

#define DEBUG_REQ_CONTROL_REG *(volatile int *)0x15000008


// Tag is simply to help debug and determine where the failure came from
void check_debug_status(int tag, int value)
{
  if(glb_debug_status != value){
    printf("ERROR: check_debug_status(%d, %d): Tag=%d status=%d, exp=%d \n\n",
           tag, value, tag, glb_debug_status, value);
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


int main(int argc, char *argv[])
{
    debug_req_control_t debug_req_control;
    

    printf("------------------------\n");
    printf("Test 1: debug_req while processing illegal insn\n");
    glb_hart_status = 1;
    glb_expect_debug_entry = 1;
    glb_expect_illegal_insn = 1;
    // Request debug
    debug_req_control = (debug_req_control_t) {
      .fields.value            = 1,
      .fields.pulse_mode       = 1, //PULSE Mode
      .fields.rand_pulse_width = 0,
      .fields.pulse_width      = 5,// FIXME: BUG: one clock pulse cause core to lock up
      .fields.rand_start_delay = 0,
      .fields.start_delay      = 0
    };
    DEBUG_REQ_CONTROL_REG = debug_req_control.bits;
    asm volatile("dret");

    while(glb_debug_status != glb_hart_status){
        printf("Wait for Debugger\n");
    } 

    check_debug_status(11, glb_hart_status);
    check_illegal_insn_status(1,1);



    printf("------------------------\n");
    printf("Finished \n");
    return EXIT_SUCCESS;
}

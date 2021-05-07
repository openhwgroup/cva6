// Copyright 2017-2020 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// Author: Nursultan Kabylkas, UCSC
// Date: Jun 15, 2020
// Description: DPI wrappers to interface with Dromajo RISC-V emulator

#include <svdpi.h>
#include <iostream>
#include "dromajo_cosim.h"
#include "stdlib.h"
#include <string>
#include <vector>

/**
 * pointer to the dromajo emulator this pointer gets
 * accessed from RTL
 */
dromajo_cosim_state_t* dromajo_pointer;

/**
 * set the counter variable to number of instructions
 * you want to commit after the cosim failure. This is 
 * sometimes useful when debugging to see waveform 
 * activity post failure
 */
bool kill_soon = false;
uint32_t counter = 0;

/**
 * Initialize dromajo emulator
 *
 * This function should usually be called from the initial
 * block in RTL.
 *
 * @param config (.cfg) file with the configurations
 */
extern "C" void init_dromajo(char* cfg_f_name) {
  char *argv[] = {(char*)"Variane", cfg_f_name};

  dromajo_pointer = dromajo_cosim_init(2, argv);
}

/**
 * Progress the emulator
 *
 * This function progresses the emulator by one instruction
 * and compares the results by the committed instruction
 * in RTL. The following parameters are passed from RTL to 
 * dromajo for comparison purposes.
 *
 * @param hart_id - id of the HART that is commiting instruction
 * @param pc      - pc of the instruction being committed
 * @param insn    - RISCV instruction being committed
 * @param wdata   - the value being committed (what's going to destination register)
 * @param cycle   - clock cycle number (optional, this is not compared)
 */
extern "C" void dromajo_step(int      hart_id,
                             uint64_t pc,
                             uint32_t insn,
                             uint64_t wdata,
                             uint64_t cycle) {
  int exit_code;
  do {
    exit_code = dromajo_cosim_step(dromajo_pointer, hart_id, pc, insn, wdata, 0, true);
  } while (exit_code == 0x3);

  if (exit_code > 3) {
    kill_soon = true;
  } else if (exit_code == 0x2){
    exit(0);
  }

  if (kill_soon) {
    if (counter == 0) {
      std::cout << "Cosim failed!" << std::endl;
      exit(1);
    } else {
      std::cout << "Let's let it run for a couple of instructions" << std::endl;
    }
    counter--;
  }
}

/**
 * Redirects dromajo's execution flow on exception/interrupt
 *
 * @param hart_id - id of the HART that is trapping
 * @param cause   - exception or interrupt cause
 */
extern "C" void dromajo_trap(int      hart_id,
                             uint64_t cause) {
  std::cout << "Dromajo trapping. Cause = " << cause << std::endl;
  dromajo_cosim_raise_trap(dromajo_pointer, hart_id, cause);
}

/*
 * Copyright 2018 Google LLC
 * Copyright 2020 OpenHW Group
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

//------------------------------------------------------------------------------
// CORE-V instruction generator configuration class:
//     - extension of the RISC-V instruction generator base test.
//
// The base test Uses the factory to replace riscv_instr_gen_config with corev_instr_gen_config
//------------------------------------------------------------------------------

class cv32e40x_instr_gen_config extends riscv_instr_gen_config;

  // External config control (plusarg) to enable/disable fast_interrupt handlers
  bit enable_fast_interrupt_handler;
  bit enable_pma;
  bit exit_on_debug_exception;
  cv32e40x_pma_cfg pma_cfg;

  // Knob to set zero fast interrupt handler
  // Knob is needed because FIXED MTVEC mode won't work with fast interrupt handlers
  rand bit knob_zero_fast_intr_handlers;

  // Mask for using a fast interrupt handler (mret only), relying on h/W interrupt ack mechanism
  rand bit [31:0] use_fast_intr_handler;

  // Random register for debug stack pointer
  rand riscv_reg_t     dp;

  mem_region_t mem_region_override[$];

  constraint dp_c {
    // Debug pointer may not be the return address, stack pointer, nor thread pointer
    if (!gen_debug_section) {
      dp == ZERO;
    } else {
      !(dp inside {sp, tp, ra, scratch_reg, GP, RA, ZERO});
      foreach (gpr[i]) {
        !(gpr[i] inside {dp});
      }
    }
  }

  // CV32E40X requires the MTVEC table to be aligned to 256KB boundaries
  constraint mtvec_c {
    tvec_alignment == 8;
  }

  // Constrain fast interrupt handler
  constraint knob_zero_fast_intr_dist_c {
    solve knob_zero_fast_intr_handlers before use_fast_intr_handler;
    knob_zero_fast_intr_handlers dist {
                                        0 :/ 8,
                                        1 :/ 2
                                      };
  }

  constraint fast_intr_handler_c {
    if (!enable_fast_interrupt_handler) {
      knob_zero_fast_intr_handlers == 1;
    }

    // Nver use fast handler for exceptions (interrupt 0)
    use_fast_intr_handler[0] == 0;

    knob_zero_fast_intr_handlers -> !use_fast_intr_handler;

    // VECTORED mode required for any fast interrupts
    if (use_fast_intr_handler) {
      mtvec_mode == VECTORED;
    }
  }

  `uvm_object_utils_begin(cv32e40x_instr_gen_config)
    `uvm_field_enum(mtvec_mode_t, mtvec_mode,     UVM_DEFAULT)
    `uvm_field_enum(riscv_reg_t, dp,              UVM_DEFAULT)
    `uvm_field_enum(riscv_reg_t, scratch_reg,     UVM_DEFAULT)
    `uvm_field_int(knob_zero_fast_intr_handlers,  UVM_DEFAULT)
    `uvm_field_int(enable_fast_interrupt_handler, UVM_DEFAULT)
    `uvm_field_int(use_fast_intr_handler,         UVM_DEFAULT)
    `uvm_field_int(enable_pma,                    UVM_DEFAULT)
    `uvm_field_int(exit_on_debug_exception,       UVM_DEFAULT)
  `uvm_object_utils_end

  function new(string name="");
    super.new(name);

    get_bool_arg_value("+enable_fast_interrupt_handler=", enable_fast_interrupt_handler);
    get_bool_arg_value("+enable_pma=", enable_pma);
    get_bool_arg_value("+exit_on_debug_exception=", exit_on_debug_exception);

    if (enable_pma) begin
      pma_cfg = cv32e40x_pma_cfg::type_id::create("pma_cfg");
      foreach (pma_cfg.regions[i]) begin
        if (pma_cfg.regions[i].main) begin
          int size;
          int min_size;

          size = (pma_cfg.regions[i].word_addr_high - pma_cfg.regions[i].word_addr_low) * 4;
          min_size = (size < 4096*16) ? size : (4096*16);
          mem_region_override.push_back('{name:$sformatf("region_%0d", i), size_in_bytes: min_size, xwr: 3'b111});
        end
      end
      super.mem_region = this.mem_region_override;
    end // if (enable_pma)

  endfunction : new

  function void post_randomize();
    super.post_randomize();

    // Add in the debug pointer to reserved registers if we are using it
    if (gen_debug_section) begin
      reserved_regs = {tp, sp, scratch_reg, dp};
    end

    // In the debug ROM some combinations are not valid because they use the same register (dscratch0)
    if (gen_debug_section) begin
      if ((enable_ebreak_in_debug_rom || set_dcsr_ebreak) &&
           enable_debug_single_step) begin
        `uvm_fatal("CVINSTGENCFG",
                   $sformatf("Illegal combination of debug plusargs: enable_ebreak_in_debug_rom = %0d, set_dcsr_ebreakl = %0d, enable_debug_single_step = %0d",
                             enable_ebreak_in_debug_rom, set_dcsr_ebreak, enable_debug_single_step))
      end
    end
  endfunction : post_randomize

endclass : cv32e40x_instr_gen_config

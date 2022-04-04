// Copyright 2020 OpenHW Group
// Copyright 2020 Datum Technology Corporation
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     https://solderpad.org/licenses/
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.


`ifndef __UVME_CV32E40X_FETCH_TOGGLE_SEQ_C__
`define __UVME_CV32E40X_FETCH_TOGGLE_SEQ_C__

/**
 * Virtual sequence responsible for controlling fetch_en during tests
 */
class uvme_cv32e40x_fetch_toggle_seq_c extends uvme_cv32e40x_core_cntrl_base_seq_c;

  rand fetch_toggle_t fetch_toggle_mode;

  rand int unsigned initial_delay;

  `uvm_object_utils_begin(uvme_cv32e40x_fetch_toggle_seq_c);
    `uvm_field_enum(fetch_toggle_t, fetch_toggle_mode, UVM_DEFAULT)
    `uvm_field_int(initial_delay, UVM_DEFAULT)
  `uvm_object_utils_end

  constraint default_mode_cons {
    soft fetch_toggle_mode inside { FETCH_CONSTANT, FETCH_INITIAL_DELAY_CONSTANT };
  }

  constraint default_initial_delay {
    // Wait a bit before starting
    initial_delay inside {[50:200]};
  }

  extern function new(string name = "");

  extern virtual task body();

  extern virtual task fetch_constant();

  extern virtual task fetch_initial_delay();

  extern virtual task fetch_random_toggle();

endclass : uvme_cv32e40x_fetch_toggle_seq_c

function uvme_cv32e40x_fetch_toggle_seq_c::new(string name = "");

  super.new(name);

  if ($test$plusargs("fetch_initial_delay")) begin
    fetch_toggle_mode = FETCH_INITIAL_DELAY_CONSTANT;
    fetch_toggle_mode.rand_mode(0);
  end
  else if ($test$plusargs("random_fetch_toggle")) begin
    fetch_toggle_mode = FETCH_RANDOM_TOGGLE;
    fetch_toggle_mode.rand_mode(0);
  end
  else if ($test$plusargs("fetch_constant")) begin
    fetch_toggle_mode = FETCH_CONSTANT;
    fetch_toggle_mode.rand_mode(0);
  end

endfunction : new

task uvme_cv32e40x_fetch_toggle_seq_c::body();

  `uvm_info("FETCHTOGGLE", $sformatf("Driving fetch_en with mode: %s", fetch_toggle_mode.name()), UVM_LOW)

  case (fetch_toggle_mode)
    FETCH_CONSTANT: fetch_constant();
    FETCH_INITIAL_DELAY_CONSTANT: fetch_initial_delay();
    FETCH_RANDOM_TOGGLE: begin
      fetch_initial_delay();
      fetch_random_toggle();
    end
  endcase

endtask : body

task uvme_cv32e40x_fetch_toggle_seq_c::fetch_constant();

  // Start fetching as fast as possible
  cntxt.core_cntrl_vif.drv_cb.fetch_en <= 1'b1;

endtask : fetch_constant

task uvme_cv32e40x_fetch_toggle_seq_c::fetch_initial_delay();

  repeat (initial_delay) @(cntxt.core_cntrl_vif.drv_cb);
  cntxt.core_cntrl_vif.drv_cb.fetch_en <= 1'b1;

endtask : fetch_initial_delay

task uvme_cv32e40x_fetch_toggle_seq_c::fetch_random_toggle();

  while (1) begin
    int unsigned fetch_assert_cycles;
    int unsigned fetch_deassert_cycles;

    // Randomly assert for a random number of cycles
    randcase
      9: fetch_assert_cycles = $urandom_range(100_000, 100);
      1: fetch_assert_cycles = $urandom_range(100, 1);
      1: fetch_assert_cycles = $urandom_range(3, 1);
    endcase
    repeat (fetch_assert_cycles) @(cntxt.core_cntrl_vif.drv_cb);
    cntxt.core_cntrl_vif.drv_cb.fetch_en <= 1'b0;

    // Randomly dessert for a random number of cycles
    randcase
      3: fetch_deassert_cycles = $urandom_range(100, 1);
      1: fetch_deassert_cycles = $urandom_range(3, 1);
    endcase
    repeat (fetch_deassert_cycles) @(cntxt.core_cntrl_vif.drv_cb);
    cntxt.core_cntrl_vif.drv_cb.fetch_en <= 1'b1;
  end

endtask : fetch_random_toggle

`endif // __UVME_CV32E40X_FETCH_TOGGLE_SEQ_C__

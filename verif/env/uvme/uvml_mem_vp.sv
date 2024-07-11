// Copyright 2024 CoreLab Tech
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
//
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0

`ifndef __UVML_MEM_VP_SV__
`define __UVML_MEM_VP_SV__

typedef class uvme_cva6_cntxt_c;

/**
 * Memory model
 */
class uvml_mem_vp_c#(int XLEN=`UVML_MEM_XLEN) extends uvml_mem_c#(XLEN);

  int vp_log;
  uvme_cva6_cntxt_c  cntxt;

  `uvm_object_param_utils_begin(uvml_mem_vp_c#(XLEN));
    `uvm_field_object(cntxt, UVM_DEFAULT)
  `uvm_object_utils_end

  /**
   * Default constructor
   */
  extern function new(string name="uvml_mem_vp_c");

  /**
   * Write to memory array
   */
  extern virtual function void write(bit[XLEN-1:0] addr, reg[7:0] data);

  extern virtual function void post_write(bit[XLEN-1:0] addr, reg[7:0] data);

   /**
    * Read from memory array in 32 bit.
    */
   extern virtual function reg[31:0] read_word(bit[XLEN-1:0] addr);

  /**
   * Start delayed debug thread
   */
  extern virtual task debug(bit dbg_req_value,
                            bit request_mode,
                            bit rand_pulse_duration,
                            bit rand_start_delay,
                            int unsigned dbg_pulse_duration,
                            int unsigned start_delay);

  /**
   * Wait for clocks
   */
  extern virtual task wait_n_clocks(int unsigned n);

  /**
   * Asserts the actual interrupt wires
   */
  extern virtual task set_debug_req(bit debug_req);

endclass : uvml_mem_vp_c


function uvml_mem_vp_c::new(string name="uvml_mem_vp_c");

  super.new(name);
  vp_log = $fopen("vp.log", "w");

endfunction : new

function void uvml_mem_vp_c::write(bit[XLEN-1:0] addr, reg[7:0] data);

  super.write(addr, data);

  post_write(addr, data);

endfunction : write

function reg[31:0] uvml_mem_vp_c::read_word(bit[XLEN-1:0] addr);
  return {read(addr+'h3), read(addr+'h2), read(addr+'h1), read(addr+'h0)};
endfunction : read_word

function void uvml_mem_vp_c::post_write(bit[XLEN-1:0] addr, reg[7:0] data);
  reg[31:0] wval;
  if ( addr==(CV_VP_DEBUG_CONTROL_BASE+32'h3) ) begin
    wval = read_word(CV_VP_DEBUG_CONTROL_BASE);
    `uvm_info("UVML_MEM_VP", $sformatf("Call to virtual peripheral 'vp_debug_control', wval=0x%0x", wval), UVM_HIGH)
    debug(.dbg_req_value       (wval[31]),
          .request_mode        (wval[30]),
          .rand_pulse_duration (wval[29]),
          .dbg_pulse_duration  (wval[28:16]),
          .rand_start_delay    (wval[15]),
          .start_delay         (wval[14:0]));
  end
  else if ( addr==CV_VP_VIRTUAL_PRINTER_BASE ) begin
    wval=0;
    wval=data;
    `uvm_info("VP_VSEQ", $sformatf("Call to virtual peripheral 'virtual_printer', wval=0x%0x", wval), UVM_HIGH)
    // Allow $write as this acts as a UART/serial printer
    // $write("%c", wval);
    $fwrite(vp_log, $sformatf("%c", wval));
  end
  else if ( addr==CV_VP_STATUS_FLAGS_BASE ) begin
    wval = read_word(CV_VP_STATUS_FLAGS_BASE);
    // TODO if (wval == 'd123456789) begin
    // TODO   `uvm_info("VP_VSEQ", "virtual peripheral: TEST PASSED", UVM_DEBUG)
    // TODO   cntxt.vp_status_vif.tests_passed = 1;
    // TODO   cntxt.vp_status_vif.exit_valid   = 1;
    // TODO   cntxt.vp_status_vif.exit_value   = 0;
    // TODO end
    // TODO else if (wval == 'd1) begin
    // TODO   cntxt.vp_status_vif.tests_failed = 1;
    // TODO   cntxt.vp_status_vif.exit_valid   = 1;
    // TODO   cntxt.vp_status_vif.exit_value   = 1;
    // TODO end
  end
  else if ( addr==(CV_VP_STATUS_FLAGS_BASE+'h4) ) begin
    wval = read_word(CV_VP_STATUS_FLAGS_BASE+'h4);
    `uvm_info("VP_VSEQ", "virtual peripheral: END OF SIM", UVM_DEBUG)
    // TODO cntxt.vp_status_vif.exit_valid = 1;
    // TODO cntxt.vp_status_vif.exit_value = wval;
  end

endfunction : post_write

task uvml_mem_vp_c::debug(bit dbg_req_value,
                          bit request_mode,
                          bit rand_pulse_duration,
                          bit rand_start_delay,
                          int unsigned dbg_pulse_duration,
                          int unsigned start_delay);
  fork
    begin
      if(!uvm_config_db#(uvme_cva6_cntxt_c)::get(uvm_root::get(), "uvm_test_top.env", "cntxt", this.cntxt)) begin
        `uvm_fatal("UVML_MEM_VP", "cva6 cntxt object handle not found")
      end
      cntxt.debug_vif.is_active = 1;
      if (rand_start_delay) begin
         wait_n_clocks($urandom_range(start_delay, 0));
      end
      else begin
         wait_n_clocks(start_delay);
      end

      if (request_mode) begin
        set_debug_req(dbg_req_value);

        if (rand_pulse_duration) begin
          if (dbg_pulse_duration == 0)
            wait_n_clocks($urandom_range(128,1));
          else
            wait_n_clocks($urandom_range(dbg_pulse_duration, 1));
        end
        else begin
          wait_n_clocks(dbg_pulse_duration);
        end
        set_debug_req(!dbg_req_value);
      end
      else begin
        set_debug_req(dbg_req_value);
      end
    end
  join_none

endtask : debug

task uvml_mem_vp_c::wait_n_clocks(int unsigned n);

  repeat (n) @(cntxt.debug_vif.mon_cb);

endtask : wait_n_clocks

task uvml_mem_vp_c::set_debug_req(bit debug_req);

  cntxt.debug_vif.drv_cb.debug_drv <= debug_req;

endtask : set_debug_req

`endif // __UVML_MEM_VP_SV__


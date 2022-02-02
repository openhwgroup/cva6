// Copyright 2020 OpenHW Group
// Copyright 2020 Datum Technology Corporation
// Copyright 2021 Thales DIS Design Services SAS
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


`ifndef __UVME_CVA6_RESET_VSEQ_SV__
`define __UVME_CVA6_RESET_VSEQ_SV__


/**
 * Virtual sequence responsible for starting the system clock and issuing
 * the initial reset pulse to the DUT.
 */
class uvme_cva6_reset_vseq_c extends uvme_cva6_base_vseq_c;

   rand int unsigned  num_clk_before_reset; ///< Number of clock cylces between start of clock and resert assert
   rand int unsigned  rst_deassert_period ; ///< Time delta between resert assert and de-assert, measured in picoseconds (ps)
   rand int unsigned  post_rst_wait       ; ///< Time delta between resert de-assert and end of virtual sequence, measured in picoseconds (ps)


   `uvm_object_utils_begin(uvme_cva6_reset_vseq_c)
      `uvm_field_int(num_clk_before_reset, UVM_DEFAULT + UVM_DEC)
      `uvm_field_int(rst_deassert_period , UVM_DEFAULT + UVM_DEC)
      `uvm_field_int(post_rst_wait       , UVM_DEFAULT + UVM_DEC)
   `uvm_object_utils_end


   constraint defaults_cons {
      soft num_clk_before_reset ==    50;
      soft rst_deassert_period  == 7_400; // 7.4 ns
      soft post_rst_wait        == 7_400; // 7.4 ns
   }


   /**
    * Default constructor.
    */
   extern function new(string name="uvme_cva6_reset_vseq");

   /**
    * Starts the clock, waits, then resets the DUT.
    */
   extern virtual task body();

endclass : uvme_cva6_reset_vseq_c


function uvme_cva6_reset_vseq_c::new(string name="uvme_cva6_reset_vseq");

   super.new(name);

endfunction : new


task uvme_cva6_reset_vseq_c::body();

   uvma_clknrst_seq_item_c  clk_start_req;
   uvma_clknrst_seq_item_c  reset_assrt_req;

   // Define the clock before applying reset
   #1;
   cntxt.clknrst_cntxt.vif.clk = 0;
   #1;

   `uvm_info("RST_VSEQ", $sformatf("Starting clock with period of %0t", (cfg.sys_clk_period * 1ps)), UVM_LOW)
   `uvm_do_on_with(clk_start_req, p_sequencer.clknrst_sequencer, {
      action        == UVMA_CLKNRST_SEQ_ITEM_ACTION_START_CLK;
      initial_value == UVMA_CLKNRST_SEQ_ITEM_INITIAL_VALUE_0;
      //clk_period    == local::cfg.sys_clk_period;
      clk_period    == cfg.sys_clk_period;
      //clk_period    == uvme_cva6_sys_default_clk_period;
   })

   `uvm_info("RST_VSEQ", $sformatf("Asserting reset for %0t", (rst_deassert_period * 1ps)), UVM_LOW)
   `uvm_do_on_with(reset_assrt_req, p_sequencer.clknrst_sequencer, {
      action              == UVMA_CLKNRST_SEQ_ITEM_ACTION_ASSERT_RESET;
      initial_value       == UVMA_CLKNRST_SEQ_ITEM_INITIAL_VALUE_1    ;
      rst_deassert_period == local::rst_deassert_period;
   })

//   `uvm_info("RST_VSEQ", $sformatf("Done reset, waiting %0t for DUT to stabilize", (post_rst_wait * 1ps)), UVM_LOW)
//   #(post_rst_wait * 1ps);


endtask : body


`endif // __UVME_CVA6_RESET_VSEQ_SV__

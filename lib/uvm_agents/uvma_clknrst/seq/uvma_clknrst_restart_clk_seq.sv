//
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
//


`ifndef __UVMA_CLKNRST_RESTART_CLK_SEQ_SV__
`define __UVMA_CLKNRST_RESTART_CLK_SEQ_SV__


/**
 * Object holding sequence library for Clock & Reset agent.
 */
class uvma_clknrst_restart_clk_seq_c extends uvma_clknrst_base_seq_c;

   `uvm_object_utils          (uvma_clknrst_restart_clk_seq_c);
   `uvm_declare_p_sequencer(uvma_clknrst_sqr_c)

   extern function new(string name="uvma_clknrst_restart_clk_seq");

   extern task body();
endclass : uvma_clknrst_restart_clk_seq_c

function uvma_clknrst_restart_clk_seq_c::new(string name="uvma_clknrst_restart_clk_seq");

   super.new(name);

endfunction : new

task uvma_clknrst_restart_clk_seq_c::body();
   uvma_clknrst_seq_item_c clknrst_seq_item;

   clknrst_seq_item = uvma_clknrst_seq_item_c::type_id::create("clknrst_seq_item", , get_full_name());
   start_item(clknrst_seq_item);
   clknrst_seq_item.action = UVMA_CLKNRST_SEQ_ITEM_ACTION_RESTART_CLK;
   finish_item(clknrst_seq_item);

endtask : body

`endif // __UVMA_CLKNRST_RESTART_CLK_SEQ_SV__

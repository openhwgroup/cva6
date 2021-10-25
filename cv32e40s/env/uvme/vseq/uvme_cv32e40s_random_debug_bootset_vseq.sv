//
// Copyright 2020 OpenHW Group
// Copyright 2020 Silicon Labs, Inc.
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

`ifndef __UVME_CV32E40S_RANDOM_DEBUG_BOOTSET__
`define __UVME_CV32E40S_RANDOM_DEBUG_BOOTSET__

class uvme_cv32e40s_random_debug_bootset_c extends uvme_cv32e40s_base_vseq_c;


    `uvm_object_utils_begin(uvme_cv32e40s_random_debug_bootset_c)
    `uvm_object_utils_end

    extern function new(string name="uvme_cv32e40s_random_debug_bootset");

    extern virtual task body();
endclass : uvme_cv32e40s_random_debug_bootset_c

function uvme_cv32e40s_random_debug_bootset_c::new(string name="uvme_cv32e40s_random_debug_bootset");
    super.new(name);
endfunction : new


task uvme_cv32e40s_random_debug_bootset_c::body();
    fork
        uvma_debug_seq_item_c debug_req;
        `uvm_do_on_with(debug_req, p_sequencer.debug_sequencer, {
                active_cycles == 1;
        });
    join
endtask : body
`endif // __UVME_CV32E40S_RANDOM_DEBUG_BOOTSET__

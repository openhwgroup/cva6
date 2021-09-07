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


`ifndef __UVMA_FENCEI_SEQ_ITEM_SV__
`define __UVMA_FENCEI_SEQ_ITEM_SV__


/**
 * Object created by Fenci agent sequences
 */
class uvma_fencei_seq_item_c extends uvml_trn_seq_item_c;

   // Latency used by active masters to delay driving request
   int unsigned            req_latency;

   // Latency used by active slaves to delay driving acknowledge
   // A monitor will also use this to log latency of an acknowledge
   int unsigned            ack_latency;

   static protected string _log_format_string = "0x%08x %s 0x%01x 0x%08x";

   `uvm_object_param_utils_begin(uvma_fencei_seq_item_c)
      `uvm_field_int(req_latency, UVM_DEFAULT)
      `uvm_field_int(ack_latency, UVM_DEFAULT)
   `uvm_object_utils_end

   /**
    * Default constructor.
    */
   extern function new(string name="uvma_fencei_seq_item");

   /**
    * One-liner log message
    */
   extern function string convert2string();

endclass : uvma_fencei_seq_item_c

`pragma protect begin

function uvma_fencei_seq_item_c::new(string name="uvma_fencei_seq_item");

   super.new(name);

endfunction : new

function string uvma_fencei_seq_item_c::convert2string();

   convert2string = $sformatf("FENCEI: Ack latency: %0d", ack_latency);

endfunction : convert2string


`pragma protect end


`endif // __UVMA_FENCEI_SEQ_ITEM_SV__

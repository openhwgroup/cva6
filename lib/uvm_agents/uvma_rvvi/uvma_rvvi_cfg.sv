//
// Copyright 2020 OpenHW Group
// Copyright 2020 Datum Technology Corporation
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


`ifndef __UVMA_RVVI_CFG_SV__
`define __UVMA_RVVI_CFG_SV__


/**
 * Object encapsulating all parameters for creating, connecting and running all
 * Clock & Reset agent (uvma_rvvi_agent_c) components.
 */
class uvma_rvvi_cfg_c#(int ILEN=DEFAULT_ILEN,
                       int XLEN=DEFAULT_XLEN) extends uvm_object;

   typedef struct {
      bit [XLEN-1:0] addr_lo;
      bit [XLEN-1:0] addr_hi;
   } mem_range_t;

   // Core configuration
   uvma_core_cntrl_cfg_c         core_cfg;

   // Common options
   rand bit                      enabled;
   rand uvm_active_passive_enum  is_active;

   rand bit                      cov_model_enabled;
   rand bit                      trn_log_enabled;

   mem_range_t                   volatile_mem_range_q[$];

   `uvm_object_utils_begin(uvma_rvvi_cfg_c)
      `uvm_field_int (                         enabled                    , UVM_DEFAULT)
      `uvm_field_enum(uvm_active_passive_enum, is_active                  , UVM_DEFAULT)
      `uvm_field_int (                         cov_model_enabled          , UVM_DEFAULT)
      `uvm_field_int (                         trn_log_enabled            , UVM_DEFAULT)
   `uvm_object_utils_end

   constraint defaults_cons {
      soft enabled           == 1;
      soft is_active         == UVM_PASSIVE;
      soft cov_model_enabled == 0;
      soft trn_log_enabled   == 1;
   }

   /**
    * Default constructor.
    */
   extern function new(string name="uvma_rvvi_cfg");

   /**
    * Printer extension to support additional fields
    */
   extern function void do_print(uvm_printer printer);

   /**
    * Add a range of addresses to be considered volatile
    */
   extern function void add_volatile_mem_addr_range(bit [XLEN-1:0] addr_lo,
                                                    bit [XLEN-1:0] addr_hi);

   /**
    * Check if an address is volatile
    */
   extern function bit is_mem_addr_volatile(bit [XLEN-1:0] mem_addr);

endclass : uvma_rvvi_cfg_c

function uvma_rvvi_cfg_c::new(string name="uvma_rvvi_cfg");

   super.new(name);

endfunction : new

function void uvma_rvvi_cfg_c::do_print(uvm_printer printer);

   super.do_print(printer);

   foreach (volatile_mem_range_q[i]) begin
      printer.print_string($sformatf("volatile_mem_range_q[%0d]", i),
                           $sformatf($sformatf("0x%%0%0dx:0x%%0%0dx", XLEN/4, XLEN/4),
                                     volatile_mem_range_q[i].addr_lo, volatile_mem_range_q[i].addr_hi));
   end

endfunction : do_print

function void uvma_rvvi_cfg_c::add_volatile_mem_addr_range(bit [XLEN-1:0] addr_lo,
                                                           bit [XLEN-1:0] addr_hi);

   if (addr_lo > addr_hi)
      `uvm_fatal("RVVICFG", $sformatf("Illegal volatile address range 0x%0x:0x%0x", addr_lo, addr_hi));

   volatile_mem_range_q.push_back('{addr_lo, addr_hi});

endfunction : add_volatile_mem_addr_range

function bit uvma_rvvi_cfg_c::is_mem_addr_volatile(bit [XLEN-1:0] mem_addr);

   foreach (volatile_mem_range_q[i]) begin
      if (mem_addr >= volatile_mem_range_q[i].addr_lo && mem_addr <= volatile_mem_range_q[i].addr_hi)
         return 1;
   end

   return 0;

endfunction : is_mem_addr_volatile

`endif // __UVMA_RVVI_CFG_SV__

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

`ifndef __UVMA_CORE_CNTRL_PMA_REGION_SV__
`define __UVMA_CORE_CNTRL_PMA_REGION_SV__


/**
 * Object encapsulating all parameters for creating, connecting and running all
 * Clock & Reset agent (uvma_core_cntrl_agent_c) components.
 */

 class uvma_core_cntrl_pma_region_c extends uvm_object;

   // RISC-V ISA Configuration
   rand corev_mxl_t              xlen;

   // Word address for the start of PMA region (inclusive)
   rand bit [MAX_XLEN-1:0]       word_addr_low;

   // Word address for the end of PMA region (inclusive)
   rand bit [MAX_XLEN-1:0]       word_addr_high;

   // Is this main memory (i.e. supports exection, is idempotent and supported unaligned access)
   rand bit                      main;

   // Is this memory bufferable
   rand bit                      bufferable;

   // Is this memory cacheable
   rand bit                      cacheable;

   // Does this memory support atomics
   rand bit                      atomic;

   `uvm_object_utils_begin(uvma_core_cntrl_pma_region_c);
      `uvm_field_enum(corev_mxl_t,  xlen            , UVM_DEFAULT | UVM_NOPRINT)
      `uvm_field_int(               word_addr_low   , UVM_DEFAULT | UVM_NOPRINT)
      `uvm_field_int(               word_addr_high  , UVM_DEFAULT | UVM_NOPRINT)
      `uvm_field_int(               main            , UVM_DEFAULT | UVM_NOPRINT)
      `uvm_field_int(               bufferable      , UVM_DEFAULT | UVM_NOPRINT)
      `uvm_field_int(               cacheable       , UVM_DEFAULT | UVM_NOPRINT)
      `uvm_field_int(               atomic          , UVM_DEFAULT | UVM_NOPRINT)
   `uvm_field_utils_end

   constraint addr_range_cons {
      word_addr_low <= word_addr_high;
   }

   constraint addr_msb_cons {
      if (xlen == MXL_32) {
         word_addr_low[MAX_XLEN-1:32] == '0;
         word_addr_high[MAX_XLEN-1:32] == '0;
      } else if (xlen == MXL_64) {
         word_addr_low[MAX_XLEN-1:64] == '0;
         word_addr_high[MAX_XLEN-1:64] == '0;
      }
   }

   /**
    * Creates sub-configuration objects.
    */
   extern function new(string name="uvma_core_cntrl_pma_region_c");

   /**
    * Custom prints
    */
   extern function void do_print(uvm_printer printer);

   /**
    * Simple lookup if address is in region
    */
   extern function bit is_addr_in_region(bit [MAX_XLEN-1:0] byte_addr);

   /**
    * Convert word address to byte address
    */
   extern function bit [MAX_XLEN-1:0] get_byte_addr(bit [MAX_XLEN-1:0] word_addr);

 endclass : uvma_core_cntrl_pma_region_c

function uvma_core_cntrl_pma_region_c::new(string name="uvma_core_cntrl_pma_region_c");

   super.new(name);

endfunction : new

function void uvma_core_cntrl_pma_region_c::do_print(uvm_printer printer);

   super.do_print(printer);

   printer.print_string("xlen", xlen.name());
   printer.print_string("word_addr_low", $sformatf("0x%08x (0x%08x)", word_addr_low, get_byte_addr(word_addr_low)));
   printer.print_string("word_addr_high", $sformatf("0x%08x (0x%08x)", word_addr_high, get_byte_addr(word_addr_high)));
   printer.print_field("main", main, 1);
   printer.print_field("bufferable", bufferable, 1);
   printer.print_field("cacheable", cacheable, 1);
   printer.print_field("atomic", atomic, 1);

endfunction : do_print

function bit uvma_core_cntrl_pma_region_c::is_addr_in_region(bit [MAX_XLEN-1:0] byte_addr);

   // Per User manual, do not include the upper word address
   if (((byte_addr >> 2) >= word_addr_low) &&
       ((byte_addr >> 2) < word_addr_high))
      return 1;

   return 0;

endfunction : is_addr_in_region

function bit [MAX_XLEN-1:0] uvma_core_cntrl_pma_region_c::get_byte_addr(bit [MAX_XLEN-1:0] word_addr);
   bit [MAX_XLEN-1:0] byte_addr = word_addr << 2;

   case (xlen)
   MXL_32:  return byte_addr[31:0];
   MXL_64:  return byte_addr[63:0];
   MXL_128: return byte_addr[127:0];
   endcase

   `uvm_fatal("PMA", "Should not fall through to here");

endfunction : get_byte_addr

`endif // __UVMA_CORE_CNTRL_PMA_REGION_SV__

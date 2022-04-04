//
// Copyright 2021 Datum Technology Corporation
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
//
// Licensed under the Solderpad Hardware License v 2.1 (the "License"); you may
// not use this file except in compliance with the License, or, at your option,
// the Apache License version 2.0. You may obtain a copy of the License at
//
//     https://solderpad.org/licenses/SHL-2.1/
//
// Unless required by applicable law or agreed to in writing, any work
// distributed under the License is distributed on an "AS IS" BASIS, WITHOUT
// WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the
// License for the specific language governing permissions and limitations
// under the License.
//


`ifndef __UVML_MEM_SV__
`define __UVML_MEM_SV__


/**
 * Memory model
 */
class uvml_mem_c#(int XLEN=DEFAULT_XLEN) extends uvm_object;

   rand uvml_mem_default_enum mem_default;

   rand bit[7:0] mem_default_const_value;

   protected reg[7:0] _mem[bit[XLEN-1:0]];

   constraint defaults_cons {
      // By default avoid X's from this memory, can be overriden by core config constraints if X's are desired for some reason
      soft mem_default != MEM_DEFAULT_X;
   }

   `uvm_object_utils_begin(uvml_mem_c);
      `uvm_field_enum(uvml_mem_default_enum, mem_default, UVM_DEFAULT)
      `uvm_field_int (mem_default_const_value,            UVM_DEFAULT)
   `uvm_object_utils_end

   /**
    * Default constructor
    */
   extern function new(string name="uvml_mem");

   /**
    * Write to memory array
    */
   extern function void write(bit[XLEN-1:0] addr, reg[7:0] data);

   /**
    * Read from memory array, substituing a default value in case value is not in memory
    */
   extern function reg[7:0] read(bit[XLEN-1:0] addr);

   /**
    * Wrapper around readmemh for underlying memory
    */
   extern function void readmemh(const ref string mem_file_path);

endclass : uvml_mem_c


function uvml_mem_c::new(string name="uvml_mem");

   super.new(name);

endfunction : new

function void uvml_mem_c::write(bit[XLEN-1:0] addr, reg[7:0] data);

   _mem[addr] = data;

endfunction : write

function reg[7:0] uvml_mem_c::read(bit[XLEN-1:0] addr);
   if (!_mem.exists(addr)) begin
      case (mem_default)
         MEM_DEFAULT_X:      _mem[addr] = 'x;
         MEM_DEFAULT_0:      _mem[addr] = '0;
         MEM_DEFAULT_CONST:  _mem[addr] = mem_default_const_value;
         MEM_DEFAULT_INCR:   _mem[addr] = addr[7:0];
         MEM_DEFAULT_RANDOM: _mem[addr] = $urandom(); //@DVT_LINTER_WAIVER "MT20211214_11" disable SVTB.29.1.3.1
      endcase
   end

   return _mem[addr];

endfunction : read

function void uvml_mem_c::readmemh(const ref string mem_file_path);
   string error_desc;
   int file = $fopen(mem_file_path, "r");
   int errno = $ferror(file, error_desc);

   if (errno != 0) begin
      `uvm_fatal("MEMREADMEMH", $sformatf("Cannot open %s for reading (error description: %s)", mem_file_path, error_desc))
   end
   else begin
      $fclose(file);
      `uvm_info("MEMREADMEMH", $sformatf("Loading memory contents from %s", mem_file_path), UVM_LOW)
      $readmemh(mem_file_path, _mem);
   end

endfunction : readmemh

`endif // __UVML_MEM_SV__

//
// -------------------------------------------------------------
// Copyright 2010-2011 Mentor Graphics Corporation
// Copyright 2014 Semifore
// Copyright 2014 Intel Corporation
// Copyright 2004-2010 Synopsys, Inc.
// Copyright 2010-2018 Cadence Design Systems, Inc.
// Copyright 2010 AMD
// Copyright 2015-2018 NVIDIA Corporation
//    All Rights Reserved Worldwide
//
//    Licensed under the Apache License, Version 2.0 (the
//    "License"); you may not use this file except in
//    compliance with the License.  You may obtain a copy of
//    the License at
//
//        http://www.apache.org/licenses/LICENSE-2.0
//
//    Unless required by applicable law or agreed to in
//    writing, software distributed under the License is
//    distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
//    CONDITIONS OF ANY KIND, either express or implied.  See
//    the License for the specific language governing
//    permissions and limitations under the License.
// -------------------------------------------------------------
//

//------------------------------------------------------------------------------
// TITLE -- NODOCS -- Global Declarations for the Register Layer
//------------------------------------------------------------------------------
//
// This section defines globally available types, enums, and utility classes.
//
//------------------------------------------------------------------------------

`ifndef UVM_REG_MODEL__SV
`define UVM_REG_MODEL__SV


typedef class uvm_reg_field;
typedef class uvm_vreg_field;
typedef class uvm_reg;
typedef class uvm_reg_file;
typedef class uvm_vreg;
typedef class uvm_reg_block;
typedef class uvm_mem;
typedef class uvm_reg_item;
typedef class uvm_reg_map;
typedef class uvm_reg_map_info;
typedef class uvm_reg_sequence;
typedef class uvm_reg_adapter;
typedef class uvm_reg_indirect_data;


//-------------
// Group -- NODOCS -- Types
//-------------

// Type -- NODOCS -- uvm_reg_data_t
//
// 2-state data value with <`UVM_REG_DATA_WIDTH> bits
//
typedef  bit unsigned [`UVM_REG_DATA_WIDTH-1:0]  uvm_reg_data_t ;


// Type -- NODOCS -- uvm_reg_data_logic_t
//
// 4-state data value with <`UVM_REG_DATA_WIDTH> bits
//
typedef  logic unsigned [`UVM_REG_DATA_WIDTH-1:0]  uvm_reg_data_logic_t ;


// Type -- NODOCS -- uvm_reg_addr_t
//
// 2-state address value with <`UVM_REG_ADDR_WIDTH> bits
//
typedef  bit unsigned [`UVM_REG_ADDR_WIDTH-1:0]  uvm_reg_addr_t ;


// Type -- NODOCS -- uvm_reg_addr_logic_t
//
// 4-state address value with <`UVM_REG_ADDR_WIDTH> bits
//
typedef  logic unsigned [`UVM_REG_ADDR_WIDTH-1:0]  uvm_reg_addr_logic_t ;


// Type -- NODOCS -- uvm_reg_byte_en_t
//
// 2-state byte_enable value with <`UVM_REG_BYTENABLE_WIDTH> bits
//
typedef  bit unsigned [`UVM_REG_BYTENABLE_WIDTH-1:0]  uvm_reg_byte_en_t ;


// Type -- NODOCS -- uvm_reg_cvr_t
//
// Coverage model value set with <`UVM_REG_CVR_WIDTH> bits.
//
// Symbolic values for individual coverage models are defined
// by the <uvm_coverage_model_e> type.
//
// The following bits in the set are assigned as follows
//
// 0-7     - UVM pre-defined coverage models
// 8-15    - Coverage models defined by EDA vendors,
//           implemented in a register model generator.
// 16-23   - User-defined coverage models
// 24..    - Reserved
//
typedef  bit [`UVM_REG_CVR_WIDTH-1:0]  uvm_reg_cvr_t ;


// Type -- NODOCS -- uvm_hdl_path_slice
//
// Slice of an HDL path
//
// Struct that specifies the HDL variable that corresponds to all
// or a portion of a register.
//
// path    - Path to the HDL variable.
// offset  - Offset of the LSB in the register that this variable implements
// size    - Number of bits (toward the MSB) that this variable implements
//
// If the HDL variable implements all of the register, ~offset~ and ~size~
// are specified as -1. For example:
//|
//| r1.add_hdl_path('{ '{"r1", -1, -1} });
//|
//
typedef struct {
   string path;
   int offset;
   int size;
} uvm_hdl_path_slice;


typedef uvm_resource_db#(uvm_reg_cvr_t) uvm_reg_cvr_rsrc_db;


//--------------------
// Group -- NODOCS -- Enumerations
//--------------------

// Enum -- NODOCS -- uvm_status_e
//
// Return status for register operations
//
// UVM_IS_OK      - Operation completed successfully
// UVM_NOT_OK     - Operation completed with error
// UVM_HAS_X      - Operation completed successfully bit had unknown bits.
//

   typedef enum {
      UVM_IS_OK,
      UVM_NOT_OK,
      UVM_HAS_X
   } uvm_status_e;


// Enum -- NODOCS -- uvm_door_e
//
// Path used for register operation
//
// UVM_FRONTDOOR    - Use the front door
// UVM_BACKDOOR     - Use the back door
// UVM_PREDICT      - Operation derived from observations by a bus monitor via
//                    the <uvm_reg_predictor> class.
// UVM_DEFAULT_DOOR - Operation specified by the context
//

   typedef enum {
      UVM_FRONTDOOR,
      UVM_BACKDOOR,
      UVM_PREDICT,
      UVM_DEFAULT_DOOR
   } uvm_door_e;

`ifdef UVM_ENABLE_DEPRECATED_API
   typedef uvm_door_e uvm_path_e;
   parameter uvm_path_e UVM_DEFAULT_PATH = UVM_DEFAULT_DOOR;
`endif

// Enum -- NODOCS -- uvm_check_e
//
// Read-only or read-and-check
//
// UVM_NO_CHECK   - Read only
// UVM_CHECK      - Read and check
//   
   typedef enum {
      UVM_NO_CHECK,
      UVM_CHECK
   } uvm_check_e;


// Enum -- NODOCS -- uvm_endianness_e
//
// Specifies byte ordering
//
// UVM_NO_ENDIAN      - Byte ordering not applicable
// UVM_LITTLE_ENDIAN  - Least-significant bytes first in consecutive addresses
// UVM_BIG_ENDIAN     - Most-significant bytes first in consecutive addresses
// UVM_LITTLE_FIFO    - Least-significant bytes first at the same address
// UVM_BIG_FIFO       - Most-significant bytes first at the same address
//   
   typedef enum {
      UVM_NO_ENDIAN,
      UVM_LITTLE_ENDIAN,
      UVM_BIG_ENDIAN,
      UVM_LITTLE_FIFO,
      UVM_BIG_FIFO
   } uvm_endianness_e;


// Enum -- NODOCS -- uvm_elem_kind_e
//
// Type of element being read or written
//
// UVM_REG      - Register
// UVM_FIELD    - Field
// UVM_MEM      - Memory location
//
   typedef enum {
      UVM_REG,
      UVM_FIELD,
      UVM_MEM
   } uvm_elem_kind_e;


// Enum -- NODOCS -- uvm_access_e
//
// Type of operation begin performed
//
// UVM_READ     - Read operation
// UVM_WRITE    - Write operation
//
   typedef enum {
      UVM_READ,
      UVM_WRITE,
      UVM_BURST_READ,
      UVM_BURST_WRITE
   } uvm_access_e;


// Enum -- NODOCS -- uvm_hier_e
//
// Whether to provide the requested information from a hierarchical context.
//
// UVM_NO_HIER - Provide info from the local context
// UVM_HIER    - Provide info based on the hierarchical context

   typedef enum {
      UVM_NO_HIER,
      UVM_HIER
   } uvm_hier_e;


// Enum -- NODOCS -- uvm_predict_e
//
// How the mirror is to be updated
//
// UVM_PREDICT_DIRECT  - Predicted value is as-is
// UVM_PREDICT_READ    - Predict based on the specified value having been read
// UVM_PREDICT_WRITE   - Predict based on the specified value having been written
//
   typedef enum {
      UVM_PREDICT_DIRECT,
      UVM_PREDICT_READ,
      UVM_PREDICT_WRITE
   } uvm_predict_e;


// Enum -- NODOCS -- uvm_coverage_model_e
//
// Coverage models available or desired.
// Multiple models may be specified by bitwise OR'ing individual model identifiers.
//
// UVM_NO_COVERAGE      - None
// UVM_CVR_REG_BITS     - Individual register bits
// UVM_CVR_ADDR_MAP     - Individual register and memory addresses
// UVM_CVR_FIELD_VALS   - Field values
// UVM_CVR_ALL          - All coverage models
//
   typedef enum uvm_reg_cvr_t {
      UVM_NO_COVERAGE      = 'h0000,
      UVM_CVR_REG_BITS     = 'h0001,
      UVM_CVR_ADDR_MAP     = 'h0002,
      UVM_CVR_FIELD_VALS   = 'h0004,
      UVM_CVR_ALL          = -1
   } uvm_coverage_model_e;


// Enum -- NODOCS -- uvm_reg_mem_tests_e
//
// Select which pre-defined test sequence to execute.
//
// Multiple test sequences may be selected by bitwise OR'ing their
// respective symbolic values.
//
// UVM_DO_REG_HW_RESET      - Run <uvm_reg_hw_reset_seq>
// UVM_DO_REG_BIT_BASH      - Run <uvm_reg_bit_bash_seq>
// UVM_DO_REG_ACCESS        - Run <uvm_reg_access_seq>
// UVM_DO_MEM_ACCESS        - Run <uvm_mem_access_seq>
// UVM_DO_SHARED_ACCESS     - Run <uvm_reg_mem_shared_access_seq>
// UVM_DO_MEM_WALK          - Run <uvm_mem_walk_seq>
// UVM_DO_ALL_REG_MEM_TESTS - Run all of the above
//
// Test sequences, when selected, are executed in the
// order in which they are specified above.
//
typedef enum bit [63:0] {
  UVM_DO_REG_HW_RESET      = 64'h0000_0000_0000_0001,
  UVM_DO_REG_BIT_BASH      = 64'h0000_0000_0000_0002,
  UVM_DO_REG_ACCESS        = 64'h0000_0000_0000_0004,
  UVM_DO_MEM_ACCESS        = 64'h0000_0000_0000_0008,
  UVM_DO_SHARED_ACCESS     = 64'h0000_0000_0000_0010,
  UVM_DO_MEM_WALK          = 64'h0000_0000_0000_0020,
  UVM_DO_ALL_REG_MEM_TESTS = 64'hffff_ffff_ffff_ffff 
} uvm_reg_mem_tests_e;



//-----------------------
// Group -- NODOCS -- Utility Classes
//-----------------------

//------------------------------------------------------------------------------
// Class -- NODOCS -- uvm_hdl_path_concat
//
// Concatenation of HDL variables
//
// A dArray of <uvm_hdl_path_slice> specifying a concatenation
// of HDL variables that implement a register in the HDL.
//
// Slices must be specified in most-to-least significant order.
// Slices must not overlap. Gaps may exist in the concatenation
// if portions of the registers are not implemented.
//
// For example, the following register
//|
//|        1 1 1 1 1 1 0 0 0 0 0 0 0 0 0 0
//| Bits:  5 4 3 2 1 0 9 8 7 6 5 4 3 2 1 0
//|       +-+---+-------------+---+-------+
//|       |A|xxx|      B      |xxx|   C   |
//|       +-+---+-------------+---+-------+
//|
//
// If the register is implemented using a single HDL variable,
// The array should specify a single slice with its ~offset~ and ~size~
// specified as -1. For example:
//
//| concat.set('{ '{"r1", -1, -1} });
//
//------------------------------------------------------------------------------

class uvm_hdl_path_concat;

   // Variable -- NODOCS -- slices
   // Array of individual slices,
   // stored in most-to-least significant order
   uvm_hdl_path_slice slices[];

   // Function -- NODOCS -- set
   // Initialize the concatenation using an array literal
   function void set(uvm_hdl_path_slice t[]);
      slices = t;
   endfunction

   // Function -- NODOCS -- add_slice
   // Append the specified ~slice~ literal to the path concatenation
   function void add_slice(uvm_hdl_path_slice slice);
      slices = new [slices.size()+1] (slices);
      slices[slices.size()-1] = slice;
   endfunction

   // Function -- NODOCS -- add_path
   // Append the specified ~path~ to the path concatenation,
   // for the specified number of bits at the specified ~offset~.
   function void add_path(string path,
                          int unsigned offset = -1,
                          int unsigned size = -1);
      uvm_hdl_path_slice t;
      t.offset = offset;
      t.path   = path;
      t.size   = size;
      
      add_slice(t);
   endfunction
   
endclass




// concat2string

function automatic string uvm_hdl_concat2string(uvm_hdl_path_concat concat);
   string image = "{";
   
   if (concat.slices.size() == 1 &&
       concat.slices[0].offset == -1 &&
       concat.slices[0].size == -1)
      return concat.slices[0].path;

   foreach (concat.slices[i]) begin
      uvm_hdl_path_slice slice=concat.slices[i];

      image = { image, (i == 0) ? "" : ", ", slice.path };
      if (slice.offset >= 0)
         image = { image, "@", $sformatf("[%0d +: %0d]", slice.offset, slice.size) };
   end

   image = { image, "}" };

   return image;
endfunction

typedef struct packed {
  uvm_reg_addr_t min;
  uvm_reg_addr_t max;
  int unsigned stride;
  } uvm_reg_map_addr_range;


`include "reg/uvm_reg_item.svh"
`include "reg/uvm_reg_adapter.svh"
`include "reg/uvm_reg_predictor.svh"
`include "reg/uvm_reg_sequence.svh"
`include "reg/uvm_reg_cbs.svh"
`include "reg/uvm_reg_backdoor.svh"
`include "reg/uvm_reg_field.svh"
`include "reg/uvm_vreg_field.svh"
`include "reg/uvm_reg.svh"
`include "reg/uvm_reg_indirect.svh"
`include "reg/uvm_reg_fifo.svh"
`include "reg/uvm_reg_file.svh"
`include "reg/uvm_mem_mam.svh"
`include "reg/uvm_vreg.svh"
`include "reg/uvm_mem.svh"
`include "reg/uvm_reg_map.svh"
`include "reg/uvm_reg_block.svh"

`include "reg/sequences/uvm_reg_hw_reset_seq.svh"
`include "reg/sequences/uvm_reg_bit_bash_seq.svh"
`include "reg/sequences/uvm_mem_walk_seq.svh"
`include "reg/sequences/uvm_mem_access_seq.svh"
`include "reg/sequences/uvm_reg_access_seq.svh"
`include "reg/sequences/uvm_reg_mem_shared_access_seq.svh"
`include "reg/sequences/uvm_reg_mem_built_in_seq.svh"
`include "reg/sequences/uvm_reg_mem_hdl_paths_seq.svh"

`endif // UVM_REG_MODEL__SV

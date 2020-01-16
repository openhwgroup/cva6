//
// -------------------------------------------------------------
// Copyright 2010-2011 Mentor Graphics Corporation
// Copyright 2014 Semifore
// Copyright 2004-2018 Synopsys, Inc.
// Copyright 2010-2018 Cadence Design Systems, Inc.
// Copyright 2010 AMD
// Copyright 2014-2018 NVIDIA Corporation
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
// Title -- NODOCS -- Virtual Registers
//------------------------------------------------------------------------------
//
// A virtual register is a collection of fields,
// overlaid on top of a memory, usually in an array.
// The semantics and layout of virtual registers comes from
// an agreement between the software and the hardware,
// not any physical structures in the DUT.
//
//------------------------------------------------------------------------------

typedef class uvm_mem_region;
typedef class uvm_mem_mam;

typedef class uvm_vreg_cbs;


//------------------------------------------------------------------------------
// Class -- NODOCS -- uvm_vreg
//
// Virtual register abstraction base class
//
// A virtual register represents a set of fields that are
// logically implemented in consecutive memory locations.
//
// All virtual register accesses eventually turn into memory accesses.
//
// A virtual register array may be implemented on top of
// any memory abstraction class and possibly dynamically
// resized and/or relocated.
//
//------------------------------------------------------------------------------

// @uvm-ieee 1800.2-2017 auto 18.9.1
class uvm_vreg extends uvm_object;

   `uvm_register_cb(uvm_vreg, uvm_vreg_cbs)

   local bit locked;
   local uvm_reg_block parent;
   local int unsigned  n_bits;
   local int unsigned  n_used_bits;

   local uvm_vreg_field fields[$];   // Fields in LSB to MSB order

   local uvm_mem          mem;     // Where is it implemented?
   local uvm_reg_addr_t   offset;  // Start of vreg[0]
   local int unsigned     incr;    // From start to start of next
   local longint unsigned size;    //number of vregs
   local bit              is_static;

   local uvm_mem_region   region;    // Not NULL if implemented via MAM
  
   local semaphore atomic;   // Field RMW operations must be atomic
   local string fname;
   local int lineno;
   local bit read_in_progress;
   local bit write_in_progress;

   //
   // Group -- NODOCS -- Initialization
   //


   // @uvm-ieee 1800.2-2017 auto 18.9.1.1.1
   extern function new(string       name,
                       int unsigned n_bits);
                       


   // @uvm-ieee 1800.2-2017 auto 18.9.1.1.2
   extern function void configure(uvm_reg_block     parent,
                                  uvm_mem       mem    = null,
                                  longint unsigned  size   = 0,
                                  uvm_reg_addr_t    offset = 0,
                                  int unsigned      incr   = 0);


   // @uvm-ieee 1800.2-2017 auto 18.9.1.1.3
   extern virtual function bit implement(longint unsigned  n,
                                         uvm_mem       mem    = null,
                                         uvm_reg_addr_t    offset = 0,
                                         int unsigned      incr   = 0);

 
   // @uvm-ieee 1800.2-2017 auto 18.9.1.1.4
   extern virtual function uvm_mem_region allocate(longint unsigned   n,
                                                   uvm_mem_mam        mam,
                                                   uvm_mem_mam_policy alloc = null);

 
   // @uvm-ieee 1800.2-2017 auto 18.9.1.1.5
   extern virtual function uvm_mem_region get_region();


   // @uvm-ieee 1800.2-2017 auto 18.9.1.1.6
   extern virtual function void release_region();


   /*local*/ extern virtual function void set_parent(uvm_reg_block parent);
   /*local*/ extern function void Xlock_modelX();
   
   /*local*/ extern function void add_field(uvm_vreg_field field);
   /*local*/ extern task XatomicX(bit on);

   //
   // Group -- NODOCS -- Introspection
   //

   //
   // Function -- NODOCS -- get_name
   // Get the simple name
   //
   // Return the simple object name of this register.
   //

   //
   // Function -- NODOCS -- get_full_name
   // Get the hierarchical name
   //
   // Return the hierarchal name of this register.
   // The base of the hierarchical name is the root block.
   //
   extern virtual function string        get_full_name();


   // @uvm-ieee 1800.2-2017 auto 18.9.1.2.1
   extern virtual function uvm_reg_block get_parent();
   extern virtual function uvm_reg_block get_block();



   // @uvm-ieee 1800.2-2017 auto 18.9.1.2.2
   extern virtual function uvm_mem get_memory();


   // @uvm-ieee 1800.2-2017 auto 18.9.1.2.3
   extern virtual function int             get_n_maps      ();


   // @uvm-ieee 1800.2-2017 auto 18.9.1.2.4
   extern function         bit             is_in_map       (uvm_reg_map map);


   // @uvm-ieee 1800.2-2017 auto 18.9.1.2.5
   extern virtual function void            get_maps        (ref uvm_reg_map maps[$]);


   // @uvm-ieee 1800.2-2017 auto 18.9.1.2.6
   extern virtual function string get_rights(uvm_reg_map map = null);


   // @uvm-ieee 1800.2-2017 auto 18.9.1.2.7
   extern virtual function string get_access(uvm_reg_map map = null);

   //
   // FUNCTION -- NODOCS -- get_size
   // Returns the size of the virtual register array. 
   //
   extern virtual function int unsigned get_size();

   //
   // FUNCTION -- NODOCS -- get_n_bytes
   // Returns the width, in bytes, of a virtual register.
   //
   // The width of a virtual register is always a multiple of the width
   // of the memory locations used to implement it.
   // For example, a virtual register containing two 1-byte fields
   // implemented in a memory with 4-bytes memory locations is 4-byte wide. 
   //
   extern virtual function int unsigned get_n_bytes();

   //
   // FUNCTION -- NODOCS -- get_n_memlocs
   // Returns the number of memory locations used
   // by a single virtual register. 
   //
   extern virtual function int unsigned get_n_memlocs();

   //
   // FUNCTION -- NODOCS -- get_incr
   // Returns the number of memory locations
   // between two individual virtual registers in the same array. 
   //
   extern virtual function int unsigned get_incr();


   // @uvm-ieee 1800.2-2017 auto 18.9.1.2.12
   extern virtual function void get_fields(ref uvm_vreg_field fields[$]);


   // @uvm-ieee 1800.2-2017 auto 18.9.1.2.13
   extern virtual function uvm_vreg_field get_field_by_name(string name);


   // @uvm-ieee 1800.2-2017 auto 18.9.1.2.14
   extern virtual function uvm_reg_addr_t  get_offset_in_memory(longint unsigned idx);


   // @uvm-ieee 1800.2-2017 auto 18.9.1.2.15
   extern virtual function uvm_reg_addr_t  get_address(longint unsigned idx,
                                                       uvm_reg_map map = null);

   //
   // Group -- NODOCS -- HDL Access
   //


   // @uvm-ieee 1800.2-2017 auto 18.9.1.3.1
   extern virtual task write(input  longint unsigned   idx,
                             output uvm_status_e  status,
                             input  uvm_reg_data_t     value,
                             input  uvm_door_e    path = UVM_DEFAULT_DOOR,
                             input  uvm_reg_map     map = null,
                             input  uvm_sequence_base  parent = null,
                             input  uvm_object         extension = null,
                             input  string             fname = "",
                             input  int                lineno = 0);


   // @uvm-ieee 1800.2-2017 auto 18.9.1.3.2
   extern virtual task read(input  longint unsigned    idx,
                            output uvm_status_e   status,
                            output uvm_reg_data_t      value,
                            input  uvm_door_e     path = UVM_DEFAULT_DOOR,
                            input  uvm_reg_map      map = null,
                            input  uvm_sequence_base   parent = null,
                            input  uvm_object          extension = null,
                            input  string              fname = "",
                            input  int                 lineno = 0);


   // @uvm-ieee 1800.2-2017 auto 18.9.1.3.3
   extern virtual task poke(input  longint unsigned    idx,
                            output uvm_status_e   status,
                            input  uvm_reg_data_t      value,
                            input  uvm_sequence_base   parent = null,
                            input  uvm_object          extension = null,
                            input  string              fname = "",
                            input  int                 lineno = 0);


   // @uvm-ieee 1800.2-2017 auto 18.9.1.3.4
   extern virtual task peek(input  longint unsigned    idx,
                            output uvm_status_e   status,
                            output uvm_reg_data_t      value,
                            input  uvm_sequence_base   parent = null,
                            input  uvm_object          extension = null,
                            input  string              fname = "",
                            input  int                 lineno = 0);
  

   // @uvm-ieee 1800.2-2017 auto 18.9.1.3.5
   extern function void reset(string kind = "HARD");


   //
   // Group -- NODOCS -- Callbacks
   //


   // @uvm-ieee 1800.2-2017 auto 18.9.1.4.1
   virtual task pre_write(longint unsigned     idx,
                          ref uvm_reg_data_t   wdat,
                          ref uvm_door_e  path,
                          ref uvm_reg_map      map);
   endtask: pre_write


   // @uvm-ieee 1800.2-2017 auto 18.9.1.4.2
   virtual task post_write(longint unsigned       idx,
                           uvm_reg_data_t         wdat,
                           uvm_door_e        path,
                           uvm_reg_map            map,
                           ref uvm_status_e  status);
   endtask: post_write


   // @uvm-ieee 1800.2-2017 auto 18.9.1.4.3
   virtual task pre_read(longint unsigned     idx,
                         ref uvm_door_e  path,
                         ref uvm_reg_map      map);
   endtask: pre_read


   // @uvm-ieee 1800.2-2017 auto 18.9.1.4.4
   virtual task post_read(longint unsigned       idx,
                          ref uvm_reg_data_t     rdat,
                          input uvm_door_e  path,
                          input uvm_reg_map      map,
                          ref uvm_status_e  status);
   endtask: post_read

   extern virtual function void do_print (uvm_printer printer);
   extern virtual function string convert2string;
   extern virtual function uvm_object clone();
   extern virtual function void do_copy   (uvm_object rhs);
   extern virtual function bit do_compare (uvm_object  rhs,
                                          uvm_comparer comparer);
   extern virtual function void do_pack (uvm_packer packer);
   extern virtual function void do_unpack (uvm_packer packer);

endclass: uvm_vreg



//------------------------------------------------------------------------------
// Class -- NODOCS -- uvm_vreg_cbs
//
// Pre/post read/write callback facade class
//
//------------------------------------------------------------------------------

// @uvm-ieee 1800.2-2017 auto 18.9.2.1
virtual class uvm_vreg_cbs extends uvm_callback;

   `uvm_object_abstract_utils(uvm_vreg_cbs)

   string fname;
   int    lineno;

   function new(string name = "uvm_reg_cbs");
      super.new(name);
   endfunction
   


   // @uvm-ieee 1800.2-2017 auto 18.9.2.2.1
   virtual task pre_write(uvm_vreg         rg,
                          longint unsigned     idx,
                          ref uvm_reg_data_t   wdat,
                          ref uvm_door_e  path,
                          ref uvm_reg_map   map);
   endtask: pre_write



   // @uvm-ieee 1800.2-2017 auto 18.9.2.2.2
   virtual task post_write(uvm_vreg           rg,
                           longint unsigned       idx,
                           uvm_reg_data_t         wdat,
                           uvm_door_e        path,
                           uvm_reg_map         map,
                           ref uvm_status_e  status);
   endtask: post_write



   // @uvm-ieee 1800.2-2017 auto 18.9.2.2.3
   virtual task pre_read(uvm_vreg         rg,
                         longint unsigned     idx,
                         ref uvm_door_e  path,
                         ref uvm_reg_map   map);
   endtask: pre_read



   // @uvm-ieee 1800.2-2017 auto 18.9.2.2.4
   virtual task post_read(uvm_vreg           rg,
                          longint unsigned       idx,
                          ref uvm_reg_data_t     rdat,
                          input uvm_door_e  path,
                          input uvm_reg_map   map,
                          ref uvm_status_e  status);
   endtask: post_read
endclass: uvm_vreg_cbs


//
// Type -- NODOCS -- uvm_vreg_cb
// Convenience callback type declaration
//
// Use this declaration to register virtual register callbacks rather than
// the more verbose parameterized class
//
typedef uvm_callbacks#(uvm_vreg, uvm_vreg_cbs) uvm_vreg_cb /* @uvm-ieee 1800.2-2017 auto D.4.6.9*/   ;

//
// Type -- NODOCS -- uvm_vreg_cb_iter
// Convenience callback iterator type declaration
//
// Use this declaration to iterate over registered virtual register callbacks
// rather than the more verbose parameterized class
//
typedef uvm_callback_iter#(uvm_vreg, uvm_vreg_cbs) uvm_vreg_cb_iter /* @uvm-ieee 1800.2-2017 auto D.4.6.10*/   ;



//------------------------------------------------------------------------------
// IMPLEMENTATION
//------------------------------------------------------------------------------

function uvm_vreg::new(string       name,
                           int unsigned n_bits);
   super.new(name);

   if (n_bits == 0) begin
      `uvm_error("RegModel", $sformatf("Virtual register \"%s\" cannot have 0 bits", this.get_full_name()))
      n_bits = 1;
   end
   if (n_bits > `UVM_REG_DATA_WIDTH) begin
      `uvm_error("RegModel", $sformatf("Virtual register \"%s\" cannot have more than %0d bits (%0d)", this.get_full_name(), `UVM_REG_DATA_WIDTH, n_bits))
      n_bits = `UVM_REG_DATA_WIDTH;
   end
   this.n_bits = n_bits;

   this.locked    = 0;
endfunction: new

function void uvm_vreg::configure(uvm_reg_block      parent,
                                      uvm_mem        mem = null,
                                      longint unsigned   size = 0,
                                      uvm_reg_addr_t     offset = 0,
                                      int unsigned       incr = 0);
   this.parent = parent;

   this.n_used_bits = 0;

   if (mem != null) begin
      void'(this.implement(size, mem, offset, incr));
      this.is_static = 1;
   end
   else begin
      this.mem = null;
      this.is_static = 0;
   end
   this.parent.add_vreg(this);

   this.atomic = new(1);
endfunction: configure



function void uvm_vreg::Xlock_modelX();
   if (this.locked) return;

   this.locked = 1;
endfunction: Xlock_modelX


function void uvm_vreg::add_field(uvm_vreg_field field);
   int offset;
   int idx;
   
   if (this.locked) begin
      `uvm_error("RegModel", "Cannot add virtual field to locked virtual register model")
      return;
   end

   if (field == null) `uvm_fatal("RegModel", "Attempting to register NULL virtual field")

   // Store fields in LSB to MSB order
   offset = field.get_lsb_pos_in_register();

   idx = -1;
   foreach (this.fields[i]) begin
      if (offset < this.fields[i].get_lsb_pos_in_register()) begin
         int j = i;
         this.fields.insert(j, field);
         idx = i;
         break;
      end
   end
   if (idx < 0) begin
      this.fields.push_back(field);
      idx = this.fields.size()-1;
   end

   this.n_used_bits += field.get_n_bits();
   
   // Check if there are too many fields in the register
   if (this.n_used_bits > this.n_bits) begin
      `uvm_error("RegModel", $sformatf("Virtual fields use more bits (%0d) than available in virtual register \"%s\" (%0d)",
                                     this.n_used_bits, this.get_full_name(), this.n_bits))
   end

   // Check if there are overlapping fields
   if (idx > 0) begin
      if (this.fields[idx-1].get_lsb_pos_in_register() +
          this.fields[idx-1].get_n_bits() > offset) begin
         `uvm_error("RegModel", $sformatf("Field %s overlaps field %s in virtual register \"%s\"",
                                        this.fields[idx-1].get_name(),
                                        field.get_name(),
                                        this.get_full_name()))
      end
   end
   if (idx < this.fields.size()-1) begin
      if (offset + field.get_n_bits() >
          this.fields[idx+1].get_lsb_pos_in_register()) begin
         `uvm_error("RegModel", $sformatf("Field %s overlaps field %s in virtual register \"%s\"",
                                        field.get_name(),
                                        this.fields[idx+1].get_name(),
                                        this.get_full_name()))
      end
   end
endfunction: add_field


task uvm_vreg::XatomicX(bit on);
   if (on) this.atomic.get(1);
   else begin
      // Maybe a key was put back in by a spurious call to reset()
      void'(this.atomic.try_get(1));
      this.atomic.put(1);
   end
endtask: XatomicX


function void uvm_vreg::reset(string kind = "HARD");
   // Put back a key in the semaphore if it is checked out
   // in case a thread was killed during an operation
   void'(this.atomic.try_get(1));
   this.atomic.put(1);
endfunction: reset


function string uvm_vreg::get_full_name();
   uvm_reg_block blk;

   get_full_name = this.get_name();

   // Do not include top-level name in full name
   blk = this.get_block();
   if (blk == null) return get_full_name;
   if (blk.get_parent() == null) return get_full_name;

   get_full_name = {this.parent.get_full_name(), ".", get_full_name};
endfunction: get_full_name

function void uvm_vreg::set_parent(uvm_reg_block parent);
   this.parent = parent;
endfunction: set_parent

function uvm_reg_block uvm_vreg::get_parent();
   get_parent = this.parent;
endfunction: get_parent

function uvm_reg_block uvm_vreg::get_block();
   get_block = this.parent;
endfunction: get_block


function bit uvm_vreg::implement(longint unsigned n,
                                     uvm_mem      mem = null,
                                     uvm_reg_addr_t   offset = 0,
                                     int unsigned     incr = 0);

   uvm_mem_region region;

   if(n < 1)
   begin
     `uvm_error("RegModel", $sformatf("Attempting to implement virtual register \"%s\" with a subscript less than one doesn't make sense",this.get_full_name()))
      return 0;
   end

   if (mem == null) begin
      `uvm_error("RegModel", $sformatf("Attempting to implement virtual register \"%s\" using a NULL uvm_mem reference", this.get_full_name()))
      return 0;
   end

   if (this.is_static) begin
      `uvm_error("RegModel", $sformatf("Virtual register \"%s\" is static and cannot be dynamically implemented", this.get_full_name()))
      return 0;
   end

   if (mem.get_block() != this.parent) begin
      `uvm_error("RegModel", $sformatf("Attempting to implement virtual register \"%s\" on memory \"%s\" in a different block",
                                     this.get_full_name(),
                                     mem.get_full_name()))
      return 0;
   end

   begin
      int min_incr = (this.get_n_bytes()-1) / mem.get_n_bytes() + 1;
      if (incr == 0) incr = min_incr;
      if (min_incr > incr) begin
         `uvm_error("RegModel", $sformatf("Virtual register \"%s\" increment is too small (%0d): Each virtual register requires at least %0d locations in memory \"%s\".",
                                        this.get_full_name(), incr,
                                        min_incr, mem.get_full_name()))
         return 0;
      end
   end

   // Is the memory big enough for ya?
   if (offset + (n * incr) > mem.get_size()) begin
      `uvm_error("RegModel", $sformatf("Given Offset for Virtual register \"%s[%0d]\" is too big for memory %s@'h%0h", this.get_full_name(), n, mem.get_full_name(), offset))
      return 0;
   end

   region = mem.mam.reserve_region(offset,n*incr*mem.get_n_bytes());

   if (region == null) begin
      `uvm_error("RegModel", $sformatf("Could not allocate a memory region for virtual register \"%s\"", this.get_full_name()))
      return 0;
   end

   if (this.mem != null) begin
      `uvm_info("RegModel", $sformatf("Virtual register \"%s\" is being moved re-implemented from %s@'h%0h to %s@'h%0h",
                                 this.get_full_name(),
                                 this.mem.get_full_name(),
                                 this.offset,
                                 mem.get_full_name(), offset),UVM_MEDIUM)
      this.release_region();
   end

   this.region = region;
   this.mem    = mem;
   this.size   = n;
   this.offset = offset;
   this.incr   = incr;
   this.mem.Xadd_vregX(this);

   return 1;
endfunction: implement


function uvm_mem_region uvm_vreg::allocate(longint unsigned   n,
                                           uvm_mem_mam        mam,
                                           uvm_mem_mam_policy alloc=null);

   uvm_mem mem;

   if(n < 1)
   begin
     `uvm_error("RegModel", $sformatf("Attempting to implement virtual register \"%s\" with a subscript less than one doesn't make sense",this.get_full_name()))
      return null;
   end

   if (mam == null) begin
      `uvm_error("RegModel", $sformatf("Attempting to implement virtual register \"%s\" using a NULL uvm_mem_mam reference", this.get_full_name()))
      return null;
   end

   if (this.is_static) begin
      `uvm_error("RegModel", $sformatf("Virtual register \"%s\" is static and cannot be dynamically allocated", this.get_full_name()))
      return null;
   end

   mem = mam.get_memory();
   if (mem.get_block() != this.parent) begin
      `uvm_error("RegModel", $sformatf("Attempting to allocate virtual register \"%s\" on memory \"%s\" in a different block",
                                     this.get_full_name(),
                                     mem.get_full_name()))
      return null;
   end

   begin
      int min_incr = (this.get_n_bytes()-1) / mem.get_n_bytes() + 1;
      if (incr == 0) incr = min_incr;
      if (min_incr < incr) begin
         `uvm_error("RegModel", $sformatf("Virtual register \"%s\" increment is too small (%0d): Each virtual register requires at least %0d locations in memory \"%s\".",
                                        this.get_full_name(), incr,
                                        min_incr, mem.get_full_name()))
         return null;
      end
   end

   // Need memory at least of size num_vregs*sizeof(vreg) in bytes.
   allocate = mam.request_region(n*incr*mem.get_n_bytes(), alloc);
   if (allocate == null) begin
      `uvm_error("RegModel", $sformatf("Could not allocate a memory region for virtual register \"%s\"", this.get_full_name()))
      return null;
   end

   if (this.mem != null) begin
     `uvm_info("RegModel", $sformatf("Virtual register \"%s\" is being moved from %s@'h%0h to %s@'h%0h",
                                this.get_full_name(),
                                this.mem.get_full_name(),
                                this.offset,
                                mem.get_full_name(),
                                allocate.get_start_offset()),UVM_MEDIUM)

      this.release_region();
   end

   this.region = allocate;

   this.mem    = mam.get_memory();
   this.offset = allocate.get_start_offset();
   this.size   = n;
   this.incr   = incr;

   this.mem.Xadd_vregX(this);
endfunction: allocate


function uvm_mem_region uvm_vreg::get_region();
   return this.region;
endfunction: get_region


function void uvm_vreg::release_region();
   if (this.is_static) begin
      `uvm_error("RegModel", $sformatf("Virtual register \"%s\" is static and cannot be dynamically released", this.get_full_name()))
      return;
   end

   if (this.mem != null)
      this.mem.Xdelete_vregX(this);

   if (this.region != null) begin
      this.region.release_region();
   end

   this.region = null;
   this.mem    = null;
   this.size   = 0;
   this.offset = 0;

   this.reset();
endfunction: release_region


function uvm_mem uvm_vreg::get_memory();
   return this.mem;
endfunction: get_memory


function uvm_reg_addr_t  uvm_vreg::get_offset_in_memory(longint unsigned idx);
   if (this.mem == null) begin
      `uvm_error("RegModel", $sformatf("Cannot call uvm_vreg::get_offset_in_memory() on unimplemented virtual register \"%s\"",
                                     this.get_full_name()))
      return 0;
   end

   return this.offset + idx * this.incr;
endfunction


function uvm_reg_addr_t  uvm_vreg::get_address(longint unsigned idx,
                                                   uvm_reg_map map = null);
   if (this.mem == null) begin
      `uvm_error("RegModel", $sformatf("Cannot get address of of unimplemented virtual register \"%s\".", this.get_full_name()))
      return 0;
   end

   return this.mem.get_address(this.get_offset_in_memory(idx), map);
endfunction: get_address


function int unsigned uvm_vreg::get_size();
   if (this.size == 0) begin
      `uvm_error("RegModel", $sformatf("Cannot call uvm_vreg::get_size() on unimplemented virtual register \"%s\"",
                                     this.get_full_name()))
      return 0;
   end

   return this.size;
endfunction: get_size


function int unsigned uvm_vreg::get_n_bytes();
   return ((this.n_bits-1) / 8) + 1;
endfunction: get_n_bytes


function int unsigned uvm_vreg::get_n_memlocs();
   if (this.mem == null) begin
      `uvm_error("RegModel", $sformatf("Cannot call uvm_vreg::get_n_memlocs() on unimplemented virtual register \"%s\"",
                                     this.get_full_name()))
      return 0;
   end

   return (this.get_n_bytes()-1) / this.mem.get_n_bytes() + 1;
endfunction: get_n_memlocs


function int unsigned uvm_vreg::get_incr();
   if (this.incr == 0) begin
      `uvm_error("RegModel", $sformatf("Cannot call uvm_vreg::get_incr() on unimplemented virtual register \"%s\"",
                                     this.get_full_name()))
      return 0;
   end

   return this.incr;
endfunction: get_incr


function int uvm_vreg::get_n_maps();
   if (this.mem == null) begin
      `uvm_error("RegModel", $sformatf("Cannot call uvm_vreg::get_n_maps() on unimplemented virtual register \"%s\"",
                                     this.get_full_name()))
      return 0;
   end

   return this.mem.get_n_maps();
endfunction: get_n_maps


function void uvm_vreg::get_maps(ref uvm_reg_map maps[$]);
   if (this.mem == null) begin
      `uvm_error("RegModel", $sformatf("Cannot call uvm_vreg::get_maps() on unimplemented virtual register \"%s\"",
                                     this.get_full_name()))
      return;
   end

   this.mem.get_maps(maps);
endfunction: get_maps


function bit uvm_vreg::is_in_map(uvm_reg_map map);
   if (this.mem == null) begin
      `uvm_error("RegModel", $sformatf("Cannot call uvm_vreg::is_in_map() on unimplemented virtual register \"%s\"",
                                  this.get_full_name()))
      return 0;
   end

   return this.mem.is_in_map(map);
endfunction


function string uvm_vreg::get_access(uvm_reg_map map = null);
   if (this.mem == null) begin
      `uvm_error("RegModel", $sformatf("Cannot call uvm_vreg::get_rights() on unimplemented virtual register \"%s\"",
                                     this.get_full_name()))
      return "RW";
   end

   return this.mem.get_access(map);
endfunction: get_access


function string uvm_vreg::get_rights(uvm_reg_map map = null);
   if (this.mem == null) begin
      `uvm_error("RegModel", $sformatf("Cannot call uvm_vreg::get_rights() on unimplemented virtual register \"%s\"",
                                     this.get_full_name()))
      return "RW";
   end

   return this.mem.get_rights(map);
endfunction: get_rights


function void uvm_vreg::get_fields(ref uvm_vreg_field fields[$]);
   foreach(this.fields[i])
      fields.push_back(this.fields[i]);
endfunction: get_fields


function uvm_vreg_field uvm_vreg::get_field_by_name(string name);
   foreach (this.fields[i]) begin
      if (this.fields[i].get_name() == name) begin
         return this.fields[i];
      end
   end
   `uvm_warning("RegModel", $sformatf("Unable to locate field \"%s\" in virtual register \"%s\".",
                                    name, this.get_full_name()))
   get_field_by_name = null;
endfunction: get_field_by_name


task uvm_vreg::write(input  longint unsigned   idx,
                         output uvm_status_e  status,
                         input  uvm_reg_data_t     value,
                         input  uvm_door_e    path = UVM_DEFAULT_DOOR,
                         input  uvm_reg_map     map = null,
                         input  uvm_sequence_base  parent = null,
                         input  uvm_object         extension = null,
                         input  string             fname = "",
                         input  int                lineno = 0);
   uvm_vreg_cb_iter cbs = new(this);

   uvm_reg_addr_t  addr;
   uvm_reg_data_t  tmp;
   uvm_reg_data_t  msk;
   int lsb;

   this.write_in_progress = 1'b1;
   this.fname = fname;
   this.lineno = lineno;
   if (this.mem == null) begin
      `uvm_error("RegModel", $sformatf("Cannot write to unimplemented virtual register \"%s\".", this.get_full_name()))
      status = UVM_NOT_OK;
      return;
   end

   if (path == UVM_DEFAULT_DOOR)
     path = this.parent.get_default_door();

   foreach (fields[i]) begin
      uvm_vreg_field_cb_iter cbs = new(fields[i]);
      uvm_vreg_field f = fields[i];
      
      lsb = f.get_lsb_pos_in_register();
      msk = ((1<<f.get_n_bits())-1) << lsb;
      tmp = (value & msk) >> lsb;

      f.pre_write(idx, tmp, path, map);
      for (uvm_vreg_field_cbs cb = cbs.first(); cb != null;
           cb = cbs.next()) begin
         cb.fname = this.fname;
         cb.lineno = this.lineno;
         cb.pre_write(f, idx, tmp, path, map);
      end

      value = (value & ~msk) | (tmp << lsb);
   end
   this.pre_write(idx, value, path, map);
   for (uvm_vreg_cbs cb = cbs.first(); cb != null;
        cb = cbs.next()) begin
      cb.fname = this.fname;
      cb.lineno = this.lineno;
      cb.pre_write(this, idx, value, path, map);
   end

   addr = this.offset + (idx * this.incr);

   lsb = 0;
   status = UVM_IS_OK;
   for (int i = 0; i < this.get_n_memlocs(); i++) begin
      uvm_status_e s;

      msk = ((1<<(this.mem.get_n_bytes()*8))-1) << lsb;
      tmp = (value & msk) >> lsb;
      this.mem.write(s, addr + i, tmp, path, map , parent, , extension, fname, lineno);
      if (s != UVM_IS_OK && s != UVM_HAS_X) status = s;
      lsb += this.mem.get_n_bytes() * 8;
   end

   for (uvm_vreg_cbs cb = cbs.first(); cb != null;
        cb = cbs.next()) begin
      cb.fname = this.fname;
      cb.lineno = this.lineno;
      cb.post_write(this, idx, value, path, map, status);
   end
   this.post_write(idx, value, path, map, status);
   foreach (fields[i]) begin
      uvm_vreg_field_cb_iter cbs = new(fields[i]);
      uvm_vreg_field f = fields[i];
      
      lsb = f.get_lsb_pos_in_register();
      msk = ((1<<f.get_n_bits())-1) << lsb;
      tmp = (value & msk) >> lsb;

      for (uvm_vreg_field_cbs cb = cbs.first(); cb != null;
           cb = cbs.next()) begin
         cb.fname = this.fname;
         cb.lineno = this.lineno;
         cb.post_write(f, idx, tmp, path, map, status);
      end
      f.post_write(idx, tmp, path, map, status);

      value = (value & ~msk) | (tmp << lsb);
   end

   `uvm_info("RegModel", $sformatf("Wrote virtual register \"%s\"[%0d] via %s with: 'h%h",
                              this.get_full_name(), idx,
                              (path == UVM_FRONTDOOR) ? "frontdoor" : "backdoor",
                              value),UVM_MEDIUM)
   
   this.write_in_progress = 1'b0;
   this.fname = "";
   this.lineno = 0;

endtask: write


task uvm_vreg::read(input  longint unsigned   idx,
                        output uvm_status_e  status,
                        output uvm_reg_data_t     value,
                        input  uvm_door_e    path = UVM_DEFAULT_DOOR,
                        input  uvm_reg_map     map = null,
                        input  uvm_sequence_base  parent = null,
                        input  uvm_object         extension = null,
                        input  string             fname = "",
                        input  int                lineno = 0);
   uvm_vreg_cb_iter cbs = new(this);

   uvm_reg_addr_t  addr;
   uvm_reg_data_t  tmp;
   uvm_reg_data_t  msk;
   int lsb;
   this.read_in_progress = 1'b1;
   this.fname = fname;
   this.lineno = lineno;

   if (this.mem == null) begin
      `uvm_error("RegModel", $sformatf("Cannot read from unimplemented virtual register \"%s\".", this.get_full_name()))
      status = UVM_NOT_OK;
      return;
   end

   if (path == UVM_DEFAULT_DOOR)
     path = this.parent.get_default_door();

   foreach (fields[i]) begin
      uvm_vreg_field_cb_iter cbs = new(fields[i]);
      uvm_vreg_field f = fields[i];

      f.pre_read(idx, path, map);
      for (uvm_vreg_field_cbs cb = cbs.first(); cb != null;
           cb = cbs.next()) begin
         cb.fname = this.fname;
         cb.lineno = this.lineno;
         cb.pre_read(f, idx, path, map);
      end
   end
   this.pre_read(idx, path, map);
   for (uvm_vreg_cbs cb = cbs.first(); cb != null;
        cb = cbs.next()) begin
      cb.fname = this.fname;
      cb.lineno = this.lineno;
      cb.pre_read(this, idx, path, map);
   end

   addr = this.offset + (idx * this.incr);

   lsb = 0;
   value = 0;
   status = UVM_IS_OK;
   for (int i = 0; i < this.get_n_memlocs(); i++) begin
      uvm_status_e s;

      this.mem.read(s, addr + i, tmp, path, map, parent, , extension, fname, lineno);
      if (s != UVM_IS_OK && s != UVM_HAS_X) status = s;

      value |= tmp << lsb;
      lsb += this.mem.get_n_bytes() * 8;
   end

   for (uvm_vreg_cbs cb = cbs.first(); cb != null;
        cb = cbs.next()) begin
      cb.fname = this.fname;
      cb.lineno = this.lineno;
      cb.post_read(this, idx, value, path, map, status);
   end
   this.post_read(idx, value, path, map, status);
   foreach (fields[i]) begin
      uvm_vreg_field_cb_iter cbs = new(fields[i]);
      uvm_vreg_field f = fields[i];

      lsb = f.get_lsb_pos_in_register();

      msk = ((1<<f.get_n_bits())-1) << lsb;
      tmp = (value & msk) >> lsb;

      for (uvm_vreg_field_cbs cb = cbs.first(); cb != null;
           cb = cbs.next()) begin
         cb.fname = this.fname;
         cb.lineno = this.lineno;
         cb.post_read(f, idx, tmp, path, map, status);
      end
      f.post_read(idx, tmp, path, map, status);

      value = (value & ~msk) | (tmp << lsb);
   end

   `uvm_info("RegModel", $sformatf("Read virtual register \"%s\"[%0d] via %s: 'h%h",
                              this.get_full_name(), idx,
                              (path == UVM_FRONTDOOR) ? "frontdoor" : "backdoor",
                              value),UVM_MEDIUM)
   
   this.read_in_progress = 1'b0;
   this.fname = "";
   this.lineno = 0;
endtask: read


task uvm_vreg::poke(input longint unsigned   idx,
                        output uvm_status_e status,
                        input  uvm_reg_data_t    value,
                        input  uvm_sequence_base parent = null,
                        input  uvm_object        extension = null,
                        input  string            fname = "",
                        input  int               lineno = 0);
   uvm_reg_addr_t  addr;
   uvm_reg_data_t  tmp;
   uvm_reg_data_t  msk;
   int lsb;
   this.fname = fname;
   this.lineno = lineno;

   if (this.mem == null) begin
      `uvm_error("RegModel", $sformatf("Cannot poke in unimplemented virtual register \"%s\".", this.get_full_name()))
      status = UVM_NOT_OK;
      return;
   end

   addr = this.offset + (idx * this.incr);

   lsb = 0;
   status = UVM_IS_OK;
   for (int i = 0; i < this.get_n_memlocs(); i++) begin
      uvm_status_e s;

      msk = ((1<<(this.mem.get_n_bytes() * 8))-1) << lsb;
      tmp = (value & msk) >> lsb;

      this.mem.poke(status, addr + i, tmp, "", parent, extension, fname, lineno);
      if (s != UVM_IS_OK && s != UVM_HAS_X) status = s;

      lsb += this.mem.get_n_bytes() * 8;
   end

   `uvm_info("RegModel", $sformatf("Poked virtual register \"%s\"[%0d] with: 'h%h",
                              this.get_full_name(), idx, value),UVM_MEDIUM)
   this.fname = "";
   this.lineno = 0;

endtask: poke


task uvm_vreg::peek(input longint unsigned   idx,
                        output uvm_status_e status,
                        output uvm_reg_data_t    value,
                        input  uvm_sequence_base parent = null,
                        input  uvm_object        extension = null,
                        input  string            fname = "",
                        input  int               lineno = 0);
   uvm_reg_addr_t  addr;
   uvm_reg_data_t  tmp;
   uvm_reg_data_t  msk;
   int lsb;
   this.fname = fname;
   this.lineno = lineno;

   if (this.mem == null) begin
      `uvm_error("RegModel", $sformatf("Cannot peek in from unimplemented virtual register \"%s\".", this.get_full_name()))
      status = UVM_NOT_OK;
      return;
   end

   addr = this.offset + (idx * this.incr);

   lsb = 0;
   value = 0;
   status = UVM_IS_OK;
   for (int i = 0; i < this.get_n_memlocs(); i++) begin
      uvm_status_e s;

      this.mem.peek(status, addr + i, tmp, "", parent, extension, fname, lineno);
      if (s != UVM_IS_OK && s != UVM_HAS_X) status = s;

      value |= tmp << lsb;
      lsb += this.mem.get_n_bytes() * 8;
   end

   `uvm_info("RegModel", $sformatf("Peeked virtual register \"%s\"[%0d]: 'h%h",
                              this.get_full_name(), idx, value),UVM_MEDIUM)
   
   this.fname = "";
   this.lineno = 0;

endtask: peek


function void uvm_vreg::do_print (uvm_printer printer);
  super.do_print(printer);
  printer.print_generic("initiator", parent.get_type_name(), -1, convert2string());
endfunction

function string uvm_vreg::convert2string();
   string res_str;
   string t_str;
   bit with_debug_info;
   $sformat(convert2string, "Virtual register %s -- ", 
            this.get_full_name());

   if (this.size == 0)
     $sformat(convert2string, "%sunimplemented", convert2string);
   else begin
      uvm_reg_map maps[$];
      mem.get_maps(maps);

      $sformat(convert2string, "%s[%0d] in %0s['h%0h+'h%0h]\n", convert2string,
             this.size, this.mem.get_full_name(), this.offset, this.incr); 
      foreach (maps[i]) begin
        uvm_reg_addr_t  addr0 = this.get_address(0, maps[i]);

        $sformat(convert2string, "  Address in map '%s' -- @'h%0h+%0h",
        maps[i].get_full_name(), addr0, this.get_address(1, maps[i]) - addr0);
      end
   end
   foreach(this.fields[i]) begin
      $sformat(convert2string, "%s\n%s", convert2string,
               this.fields[i].convert2string());
   end

endfunction: convert2string



//TODO - add fatal messages
function uvm_object uvm_vreg::clone();
  return null;
endfunction

function void uvm_vreg::do_copy   (uvm_object rhs);
endfunction

function bit uvm_vreg::do_compare (uvm_object  rhs,
                                        uvm_comparer comparer);
  return 0;
endfunction

function void uvm_vreg::do_pack (uvm_packer packer);
endfunction

function void uvm_vreg::do_unpack (uvm_packer packer);
endfunction

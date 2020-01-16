//
// -------------------------------------------------------------
// Copyright 2010-2011 Mentor Graphics Corporation
// Copyright 2014 Semifore
// Copyright 2018 Intel Corporation
// Copyright 2004-2018 Synopsys, Inc.
// Copyright 2010-2018 Cadence Design Systems, Inc.
// Copyright 2010-2012 AMD
// Copyright 2013-2018 NVIDIA Corporation
// Copyright 2012 Accellera Systems Initiative
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


//------------------------------------------------------------------------------
// CLASS -- NODOCS -- uvm_mem
//------------------------------------------------------------------------------
// Memory abstraction base class
//
// A memory is a collection of contiguous locations.
// A memory may be accessible via more than one address map.
//
// Unlike registers, memories are not mirrored because of the potentially
// large data space: tests that walk the entire memory space would negate
// any benefit from sparse memory modelling techniques.
// Rather than relying on a mirror, it is recommended that
// backdoor access be used instead.
//
//------------------------------------------------------------------------------

// @uvm-ieee 1800.2-2017 auto 18.6.1
class uvm_mem extends uvm_object;
// See Mantis 6040. I did NOT make this class virtual because it 
// seems to break a lot of existing tests and code. 
// Sought LRM clarification

   typedef enum {UNKNOWNS, ZEROES, ONES, ADDRESS, VALUE, INCR, DECR} init_e;

   local bit               m_locked;
   local bit               m_read_in_progress;
   local bit               m_write_in_progress;
   local string            m_access;
   local longint unsigned  m_size;
   local uvm_reg_block     m_parent;
   local bit               m_maps[uvm_reg_map];
   local int unsigned      m_n_bits;
   local uvm_reg_backdoor  m_backdoor;
   local bit               m_is_powered_down;
   local int               m_has_cover;
   local int               m_cover_on;
   local string            m_fname;
   local int               m_lineno;
   local bit               m_vregs[uvm_vreg];
   local uvm_object_string_pool
               #(uvm_queue #(uvm_hdl_path_concat)) m_hdl_paths_pool;

   local static int unsigned  m_max_size;

   //----------------------
   // Group -- NODOCS -- Initialization
   //----------------------


   // @uvm-ieee 1800.2-2017 auto 18.6.3.1
   extern function new (string           name,
                        longint unsigned size,
                        int unsigned     n_bits,
                        string           access = "RW",
                        int              has_coverage = UVM_NO_COVERAGE);

   

   // @uvm-ieee 1800.2-2017 auto 18.6.3.2
   extern function void configure (uvm_reg_block parent,
                                   string        hdl_path = "");

   

   // @uvm-ieee 1800.2-2017 auto 18.6.3.3
   extern virtual function void set_offset (uvm_reg_map    map,
                                            uvm_reg_addr_t offset,
                                            bit            unmapped = 0);


   /*local*/ extern virtual function void set_parent(uvm_reg_block parent);
   /*local*/ extern function void add_map(uvm_reg_map map);
   /*local*/ extern function void Xlock_modelX();
   /*local*/ extern function void Xadd_vregX(uvm_vreg vreg);
   /*local*/ extern function void Xdelete_vregX(uvm_vreg vreg);


   // variable -- NODOCS -- mam
   //
   // Memory allocation manager
   //
   // Memory allocation manager for the memory corresponding to this
   // abstraction class instance.
   // Can be used to allocate regions of consecutive addresses of
   // specific sizes, such as DMA buffers,
   // or to locate virtual register array.
   //
   uvm_mem_mam mam;


   //---------------------
   // Group -- NODOCS -- Introspection
   //---------------------

   // Function -- NODOCS -- get_name
   //
   // Get the simple name
   //
   // Return the simple object name of this memory.
   //

   // Function -- NODOCS -- get_full_name
   //
   // Get the hierarchical name
   //
   // Return the hierarchal name of this memory.
   // The base of the hierarchical name is the root block.
   //
   extern virtual function string get_full_name();



   // @uvm-ieee 1800.2-2017 auto 18.6.4.1
   extern virtual function uvm_reg_block get_parent ();
   extern virtual function uvm_reg_block get_block  ();



   // @uvm-ieee 1800.2-2017 auto 18.6.4.2
   extern virtual function int get_n_maps ();



   // @uvm-ieee 1800.2-2017 auto 18.6.4.3
   extern function bit is_in_map (uvm_reg_map map);



   // @uvm-ieee 1800.2-2017 auto 18.6.4.4
   extern virtual function void get_maps (ref uvm_reg_map maps[$]);


   /*local*/ extern function uvm_reg_map get_local_map   (uvm_reg_map map);

   /*local*/ extern function uvm_reg_map get_default_map ();



   // @uvm-ieee 1800.2-2017 auto 18.6.4.5
   extern virtual function string get_rights (uvm_reg_map map = null);



   // @uvm-ieee 1800.2-2017 auto 18.6.4.6
   extern virtual function string get_access(uvm_reg_map map = null);


   // Function -- NODOCS -- get_size
   //
   // Returns the number of unique memory locations in this memory. 
   // this is in units of the memory declaration: full memory is get_size()*get_n_bits() (bits)
   extern function longint unsigned get_size();


   // Function -- NODOCS -- get_n_bytes
   //
   // Return the width, in number of bytes, of each memory location
   //
   extern function int unsigned get_n_bytes();


   // Function -- NODOCS -- get_n_bits
   //
   // Returns the width, in number of bits, of each memory location
   //
   extern function int unsigned get_n_bits();


   // Function -- NODOCS -- get_max_size
   //
   // Returns the maximum width, in number of bits, of all memories
   //
   extern static function int unsigned    get_max_size();



   // @uvm-ieee 1800.2-2017 auto 18.6.4.11
   extern virtual function void get_virtual_registers(ref uvm_vreg regs[$]);



   // @uvm-ieee 1800.2-2017 auto 18.6.4.12
   extern virtual function void get_virtual_fields(ref uvm_vreg_field fields[$]);



   // @uvm-ieee 1800.2-2017 auto 18.6.4.13
   extern virtual function uvm_vreg get_vreg_by_name(string name);



   // @uvm-ieee 1800.2-2017 auto 18.6.4.14
   extern virtual function uvm_vreg_field  get_vfield_by_name(string name);


   // Function -- NODOCS -- get_vreg_by_offset
   //
   // Find the virtual register implemented at the specified offset
   //
   // Finds the virtual register implemented in this memory
   // at the specified ~offset~ in the specified address ~map~
   // and returns its abstraction class instance.
   // If no virtual register at the offset is found, returns ~null~. 
   //
   extern virtual function uvm_vreg get_vreg_by_offset(uvm_reg_addr_t offset,
                                                       uvm_reg_map    map = null);

   

   // @uvm-ieee 1800.2-2017 auto 18.6.4.15
   extern virtual function uvm_reg_addr_t  get_offset (uvm_reg_addr_t offset = 0,
                                                       uvm_reg_map    map = null);



   // @uvm-ieee 1800.2-2017 auto 18.6.4.16
   extern virtual function uvm_reg_addr_t  get_address(uvm_reg_addr_t  offset = 0,
                                                       uvm_reg_map   map = null);



   // @uvm-ieee 1800.2-2017 auto 18.6.4.17
   extern virtual function int get_addresses(uvm_reg_addr_t     offset = 0,
                                             uvm_reg_map        map=null,
                                             ref uvm_reg_addr_t addr[]);


   //------------------
   // Group -- NODOCS -- HDL Access
   //------------------


   // @uvm-ieee 1800.2-2017 auto 18.6.5.1
   extern virtual task write(output uvm_status_e       status,
                             input  uvm_reg_addr_t     offset,
                             input  uvm_reg_data_t     value,
                             input  uvm_door_e         path   = UVM_DEFAULT_DOOR,
                             input  uvm_reg_map        map = null,
                             input  uvm_sequence_base  parent = null,
                             input  int                prior = -1,
                             input  uvm_object         extension = null,
                             input  string             fname = "",
                             input  int                lineno = 0);



   // @uvm-ieee 1800.2-2017 auto 18.6.5.2
   extern virtual task read(output uvm_status_e        status,
                            input  uvm_reg_addr_t      offset,
                            output uvm_reg_data_t      value,
                            input  uvm_door_e          path   = UVM_DEFAULT_DOOR,
                            input  uvm_reg_map         map = null,
                            input  uvm_sequence_base   parent = null,
                            input  int                 prior = -1,
                            input  uvm_object          extension = null,
                            input  string              fname = "",
                            input  int                 lineno = 0);



   // @uvm-ieee 1800.2-2017 auto 18.6.5.3
   extern virtual task burst_write(output uvm_status_e      status,
                                   input  uvm_reg_addr_t    offset,
                                   input  uvm_reg_data_t    value[],
                                   input  uvm_door_e        path = UVM_DEFAULT_DOOR,
                                   input  uvm_reg_map       map = null,
                                   input  uvm_sequence_base parent = null,
                                   input  int               prior = -1,
                                   input  uvm_object        extension = null,
                                   input  string            fname = "",
                                   input  int               lineno = 0);



   // @uvm-ieee 1800.2-2017 auto 18.6.5.4
   extern virtual task burst_read(output uvm_status_e      status,
                                  input  uvm_reg_addr_t    offset,
                                  ref    uvm_reg_data_t    value[],
                                  input  uvm_door_e        path = UVM_DEFAULT_DOOR,
                                  input  uvm_reg_map       map = null,
                                  input  uvm_sequence_base parent = null,
                                  input  int               prior = -1,
                                  input  uvm_object        extension = null,
                                  input  string            fname = "",
                                  input  int               lineno = 0);



   // @uvm-ieee 1800.2-2017 auto 18.6.5.5
   extern virtual task poke(output uvm_status_e       status,
                            input  uvm_reg_addr_t     offset,
                            input  uvm_reg_data_t     value,
                            input  string             kind = "",
                            input  uvm_sequence_base  parent = null,
                            input  uvm_object         extension = null,
                            input  string             fname = "",
                            input  int                lineno = 0);



   // @uvm-ieee 1800.2-2017 auto 18.6.5.6
   extern virtual task peek(output uvm_status_e       status,
                            input  uvm_reg_addr_t     offset,
                            output uvm_reg_data_t     value,
                            input  string             kind = "",
                            input  uvm_sequence_base  parent = null,
                            input  uvm_object         extension = null,
                            input  string             fname = "",
                            input  int                lineno = 0);



   extern protected function bit Xcheck_accessX (input uvm_reg_item rw,
                                                 output uvm_reg_map_info map_info);
   

   extern virtual task do_write (uvm_reg_item rw);
   extern virtual task do_read  (uvm_reg_item rw);


   //-----------------
   // Group -- NODOCS -- Frontdoor
   //-----------------


   // @uvm-ieee 1800.2-2017 auto 18.6.6.2
   extern function void set_frontdoor(uvm_reg_frontdoor ftdr,
                                      uvm_reg_map map = null,
                                      string fname = "",
                                      int lineno = 0);
   


   // @uvm-ieee 1800.2-2017 auto 18.6.6.1
   extern function uvm_reg_frontdoor get_frontdoor(uvm_reg_map map = null);


   //----------------
   // Group -- NODOCS -- Backdoor
   //----------------


   // @uvm-ieee 1800.2-2017 auto 18.6.7.2
   extern function void set_backdoor (uvm_reg_backdoor bkdr,
                                      string fname = "",
                                      int lineno = 0);



   // @uvm-ieee 1800.2-2017 auto 18.6.7.1
   extern function uvm_reg_backdoor get_backdoor(bit inherited = 1);



   // @uvm-ieee 1800.2-2017 auto 18.6.7.3
   extern function void clear_hdl_path (string kind = "RTL");

   

   // @uvm-ieee 1800.2-2017 auto 18.6.7.4
   extern function void add_hdl_path (uvm_hdl_path_slice slices[],
                                      string kind = "RTL");
   


   // @uvm-ieee 1800.2-2017 auto 18.6.7.5
   extern function void add_hdl_path_slice(string name,
                                           int offset,
                                           int size,
                                           bit first = 0,
                                           string kind = "RTL");



   // @uvm-ieee 1800.2-2017 auto 18.6.7.6
   extern function bit  has_hdl_path (string kind = "");



   // @uvm-ieee 1800.2-2017 auto 18.6.7.7
   extern function void get_hdl_path (ref uvm_hdl_path_concat paths[$],
                                      input string kind = "");



   // @uvm-ieee 1800.2-2017 auto 18.6.7.9
   extern function void get_full_hdl_path (ref uvm_hdl_path_concat paths[$],
                                           input string kind = "",
                                           input string separator = ".");


   // @uvm-ieee 1800.2-2017 auto 18.6.7.8
   extern function void get_hdl_path_kinds (ref string kinds[$]);


   // @uvm-ieee 1800.2-2017 auto 18.6.7.10
   extern virtual protected task backdoor_read(uvm_reg_item rw);



   // @uvm-ieee 1800.2-2017 auto 18.6.7.11
   extern virtual task backdoor_write(uvm_reg_item rw);

   

   extern virtual function uvm_status_e backdoor_read_func(uvm_reg_item rw);


   //-----------------
   // Group -- NODOCS -- Callbacks
   //-----------------
   `uvm_register_cb(uvm_mem, uvm_reg_cbs)



   // @uvm-ieee 1800.2-2017 auto 18.6.9.1
   virtual task pre_write(uvm_reg_item rw); endtask



   // @uvm-ieee 1800.2-2017 auto 18.6.9.2
   virtual task post_write(uvm_reg_item rw); endtask



   // @uvm-ieee 1800.2-2017 auto 18.6.9.3
   virtual task pre_read(uvm_reg_item rw); endtask



   // @uvm-ieee 1800.2-2017 auto 18.6.9.4
   virtual task post_read(uvm_reg_item rw); endtask


   //----------------
   // Group -- NODOCS -- Coverage
   //----------------


   // @uvm-ieee 1800.2-2017 auto 18.6.8.1
   extern protected function uvm_reg_cvr_t build_coverage(uvm_reg_cvr_t models);



   // @uvm-ieee 1800.2-2017 auto 18.6.8.2
   extern virtual protected function void add_coverage(uvm_reg_cvr_t models);



   // @uvm-ieee 1800.2-2017 auto 18.6.8.3
   extern virtual function bit has_coverage(uvm_reg_cvr_t models);



   // @uvm-ieee 1800.2-2017 auto 18.6.8.5
   extern virtual function uvm_reg_cvr_t set_coverage(uvm_reg_cvr_t is_on);



   // @uvm-ieee 1800.2-2017 auto 18.6.8.4
   extern virtual function bit get_coverage(uvm_reg_cvr_t is_on);



   // @uvm-ieee 1800.2-2017 auto 18.6.8.6
   protected virtual function void  sample(uvm_reg_addr_t offset,
                                           bit            is_read,
                                           uvm_reg_map    map);
   endfunction

   /*local*/ function void XsampleX(uvm_reg_addr_t addr,
                                    bit            is_read,
                                    uvm_reg_map    map);
      sample(addr, is_read, map);
   endfunction

   // Core ovm_object operations

   extern virtual function void do_print (uvm_printer printer);
   extern virtual function string convert2string();
   extern virtual function uvm_object clone();
   extern virtual function void do_copy   (uvm_object rhs);
   extern virtual function bit do_compare (uvm_object  rhs,
                                          uvm_comparer comparer);
   extern virtual function void do_pack (uvm_packer packer);
   extern virtual function void do_unpack (uvm_packer packer);


endclass: uvm_mem



//------------------------------------------------------------------------------
// IMPLEMENTATION
//------------------------------------------------------------------------------


// new

function uvm_mem::new (string           name,
                       longint unsigned size,
                       int unsigned     n_bits,
                       string           access = "RW",
                       int              has_coverage = UVM_NO_COVERAGE);

   super.new(name);
   m_locked = 0;
   if (n_bits == 0) begin
      `uvm_error("RegModel", {"Memory '",get_full_name(),"' cannot have 0 bits"})
      n_bits = 1;
   end
   m_size      = size;
   m_n_bits    = n_bits;
   m_backdoor  = null;
   m_access    = access.toupper();
   m_has_cover = has_coverage;
   m_hdl_paths_pool = new("hdl_paths");

   if (n_bits > m_max_size)
      m_max_size = n_bits;

endfunction: new


// configure

function void uvm_mem::configure(uvm_reg_block  parent,
                                 string         hdl_path="");

   if (parent == null)
     `uvm_fatal("REG/NULL_PARENT","configure: parent argument is null") 

   m_parent = parent;

   if (m_access != "RW" && m_access != "RO") begin
      `uvm_error("RegModel", {"Memory '",get_full_name(),"' can only be RW or RO"})
      m_access = "RW";
   end

   begin
      uvm_mem_mam_cfg cfg = new;

      cfg.n_bytes      = ((m_n_bits-1) / 8) + 1;
      cfg.start_offset = 0;
      cfg.end_offset   = m_size-1;

      cfg.mode     = uvm_mem_mam::GREEDY;
      cfg.locality = uvm_mem_mam::BROAD;

      mam = new(get_full_name(), cfg, this);
   end

   m_parent.add_mem(this);

   if (hdl_path != "") add_hdl_path_slice(hdl_path, -1, -1);
endfunction: configure


// set_offset

function void uvm_mem::set_offset (uvm_reg_map    map,
                                   uvm_reg_addr_t offset,
                                   bit unmapped = 0);

   uvm_reg_map orig_map = map;

   if (m_maps.num() > 1 && map == null) begin
      `uvm_error("RegModel",{"set_offset requires a non-null map when memory '",
                 get_full_name(),"' belongs to more than one map."})
      return;
   end

   map = get_local_map(map);

   if (map == null)
     return;
   
   map.m_set_mem_offset(this, offset, unmapped);
endfunction


// add_map

function void uvm_mem::add_map(uvm_reg_map map);
  m_maps[map] = 1;
endfunction


// Xlock_modelX

function void uvm_mem::Xlock_modelX();
   m_locked = 1;
endfunction: Xlock_modelX


// get_full_name

function string uvm_mem::get_full_name();
   if (m_parent == null)
      return get_name();
   
   return {m_parent.get_full_name(), ".", get_name()};

endfunction: get_full_name


// get_block

function uvm_reg_block uvm_mem::get_block();
   return m_parent;
endfunction: get_block


// get_n_maps

function int uvm_mem::get_n_maps();
   return m_maps.num();
endfunction: get_n_maps


// get_maps

function void uvm_mem::get_maps(ref uvm_reg_map maps[$]);
   foreach (m_maps[map])
     maps.push_back(map);
endfunction


// is_in_map

function bit uvm_mem::is_in_map(uvm_reg_map map);
   if (m_maps.exists(map))
     return 1;
   foreach (m_maps[l]) begin
    uvm_reg_map local_map=l;
     uvm_reg_map parent_map = local_map.get_parent_map();

     while (parent_map != null) begin
       if (parent_map == map)
         return 1;
       parent_map = parent_map.get_parent_map();
     end
   end
   return 0;
endfunction


// get_local_map

function uvm_reg_map uvm_mem::get_local_map(uvm_reg_map map);
   if (map == null)
     return get_default_map();
   if (m_maps.exists(map))
     return map; 
   foreach (m_maps[l]) begin
     uvm_reg_map local_map = l;
     uvm_reg_map parent_map = local_map.get_parent_map();

     while (parent_map != null) begin
       if (parent_map == map)
         return local_map;
       parent_map = parent_map.get_parent_map();
     end
   end
   `uvm_warning("RegModel", 
       {"Memory '",get_full_name(),"' is not contained within map '",map.get_full_name(),"'"})
   return null;
endfunction


// get_default_map

function uvm_reg_map uvm_mem::get_default_map();

   // if mem is not associated with any may, return ~null~
   if (m_maps.num() == 0) begin
      `uvm_warning("RegModel", 
        {"Memory '",get_full_name(),"' is not registered with any map"})
      return null;
   end

   // if only one map, choose that
   if (m_maps.num() == 1) begin
     void'(m_maps.first(get_default_map));
   end

   // try to choose one based on default_map in parent blocks.
   foreach (m_maps[l]) begin
     uvm_reg_map map = l;
     uvm_reg_block blk = map.get_parent();
     uvm_reg_map default_map = blk.get_default_map();
     if (default_map != null) begin
       uvm_reg_map local_map = get_local_map(default_map);
       if (local_map != null)
         return local_map;
     end
   end

   // if that fails, choose the first in this mem's maps

   void'(m_maps.first(get_default_map));

endfunction


// get_access

function string uvm_mem::get_access(uvm_reg_map map = null);
   get_access = m_access;
   if (get_n_maps() == 1) return get_access;

   map = get_local_map(map);
   if (map == null) return get_access;

   // Is the memory restricted in this map?
   case (get_rights(map))
     "RW":
       // No restrictions
       return get_access;

     "RO":
       case (get_access)
         "RW", "RO": get_access = "RO";

         "WO":    `uvm_error("RegModel", {"WO memory '",get_full_name(),
                       "' restricted to RO in map '",map.get_full_name(),"'"})

         default: `uvm_error("RegModel", {"Memory '",get_full_name(),
                       "' has invalid access mode, '",get_access,"'"})
       endcase

     "WO":
       case (get_access)
         "RW", "WO": get_access = "WO";

         "RO":    `uvm_error("RegModel", {"RO memory '",get_full_name(),
                       "' restricted to WO in map '",map.get_full_name(),"'"})

         default: `uvm_error("RegModel", {"Memory '",get_full_name(),
                       "' has invalid access mode, '",get_access,"'"})
       endcase

     default: `uvm_error("RegModel", {"Shared memory '",get_full_name(),
                  "' is not shared in map '",map.get_full_name(),"'"})
   endcase
endfunction: get_access


// get_rights

function string uvm_mem::get_rights(uvm_reg_map map = null);

   uvm_reg_map_info info;

   // No right restrictions if not shared
   if (m_maps.num() <= 1) begin
      return "RW";
   end

   map = get_local_map(map);

   if (map == null)
     return "RW";

   info = map.get_mem_map_info(this);
   return info.rights;

endfunction: get_rights


// get_offset

function uvm_reg_addr_t uvm_mem::get_offset(uvm_reg_addr_t offset = 0,
                                            uvm_reg_map map = null);

   uvm_reg_map_info map_info;
   uvm_reg_map orig_map = map;

   map = get_local_map(map);

   if (map == null)
     return -1;
   
   map_info = map.get_mem_map_info(this);
   
   if (map_info.unmapped) begin
      `uvm_warning("RegModel", {"Memory '",get_name(),
                   "' is unmapped in map '",
                   ((orig_map == null) ? map.get_full_name() : orig_map.get_full_name()),"'"})
      return -1;
   end
         
   return map_info.offset;

endfunction: get_offset



// get_virtual_registers

function void uvm_mem::get_virtual_registers(ref uvm_vreg regs[$]);
  foreach (m_vregs[vreg])
     regs.push_back(vreg);
endfunction


// get_virtual_fields

function void uvm_mem::get_virtual_fields(ref uvm_vreg_field fields[$]);

  foreach (m_vregs[l])
  begin
    uvm_vreg vreg = l;
    vreg.get_fields(fields);
  end
endfunction: get_virtual_fields


// get_vfield_by_name

function uvm_vreg_field uvm_mem::get_vfield_by_name(string name);
  // Return first occurrence of vfield matching name
  uvm_vreg_field vfields[$];

  get_virtual_fields(vfields);

  foreach (vfields[i])
    if (vfields[i].get_name() == name)
      return vfields[i];

  `uvm_warning("RegModel", {"Unable to find virtual field '",name,
                       "' in memory '",get_full_name(),"'"})
   return null;
endfunction: get_vfield_by_name


// get_vreg_by_name

function uvm_vreg uvm_mem::get_vreg_by_name(string name);

  foreach (m_vregs[l])
  begin
    uvm_vreg vreg = l;
    if (vreg.get_name() == name)
      return vreg;
  end

  `uvm_warning("RegModel", {"Unable to find virtual register '",name,
                       "' in memory '",get_full_name(),"'"})
  return null;

endfunction: get_vreg_by_name


// get_vreg_by_offset

function uvm_vreg uvm_mem::get_vreg_by_offset(uvm_reg_addr_t offset,
                                              uvm_reg_map map = null);
   `uvm_error("RegModel", "uvm_mem::get_vreg_by_offset() not yet implemented")
   return null;
endfunction: get_vreg_by_offset



// get_addresses

function int uvm_mem::get_addresses(uvm_reg_addr_t offset = 0,
                                    uvm_reg_map map=null,
                                    ref uvm_reg_addr_t addr[]);

   uvm_reg_map_info map_info;
   uvm_reg_map system_map;
   uvm_reg_map orig_map = map;

   map = get_local_map(map);

   if (map == null)
     return 0;

   map_info = map.get_mem_map_info(this);

   if (map_info.unmapped) begin
      `uvm_warning("RegModel", {"Memory '",get_name(),
                   "' is unmapped in map '",
                   ((orig_map == null) ? map.get_full_name() : orig_map.get_full_name()),"'"})
      return 0;
   end

   addr = map_info.addr;

   foreach (addr[i])
      addr[i] = addr[i] + map_info.mem_range.stride * offset;

   return map.get_n_bytes();

endfunction


// get_address

function uvm_reg_addr_t uvm_mem::get_address(uvm_reg_addr_t offset = 0,
                                             uvm_reg_map map = null);
   uvm_reg_addr_t  addr[];
   void'(get_addresses(offset, map, addr));
   return addr[0];
endfunction


// get_size

function longint unsigned uvm_mem::get_size();
   return m_size;
endfunction: get_size


// get_n_bits

function int unsigned uvm_mem::get_n_bits();
   return m_n_bits;
endfunction: get_n_bits


// get_max_size

function int unsigned uvm_mem::get_max_size();
   return m_max_size;
endfunction: get_max_size


// get_n_bytes

function int unsigned uvm_mem::get_n_bytes();
   return (m_n_bits - 1) / 8 + 1;
endfunction: get_n_bytes




//---------
// COVERAGE
//---------


function uvm_reg_cvr_t uvm_mem::build_coverage(uvm_reg_cvr_t models);
   build_coverage = UVM_NO_COVERAGE;
   void'(uvm_reg_cvr_rsrc_db::read_by_name({"uvm_reg::", get_full_name()},
                                           "include_coverage",
                                           build_coverage, this));
   return build_coverage & models;
endfunction: build_coverage


// add_coverage

function void uvm_mem::add_coverage(uvm_reg_cvr_t models);
   m_has_cover |= models;
endfunction: add_coverage


// has_coverage

function bit uvm_mem::has_coverage(uvm_reg_cvr_t models);
   return ((m_has_cover & models) == models);
endfunction: has_coverage


// set_coverage

function uvm_reg_cvr_t uvm_mem::set_coverage(uvm_reg_cvr_t is_on);
   if (is_on == uvm_reg_cvr_t'(UVM_NO_COVERAGE)) begin
      m_cover_on = is_on;
      return m_cover_on;
   end

   m_cover_on = m_has_cover & is_on;

   return m_cover_on;
endfunction: set_coverage


// get_coverage

function bit uvm_mem::get_coverage(uvm_reg_cvr_t is_on);
   if (has_coverage(is_on) == 0) return 0;
   return ((m_cover_on & is_on) == is_on);
endfunction: get_coverage




//-----------
// HDL ACCESS
//-----------

// write
//------

task uvm_mem::write(output uvm_status_e      status,
                    input  uvm_reg_addr_t    offset,
                    input  uvm_reg_data_t    value,
                    input  uvm_door_e        path = UVM_DEFAULT_DOOR,
                    input  uvm_reg_map       map = null,
                    input  uvm_sequence_base parent = null,
                    input  int               prior = -1,
                    input  uvm_object        extension = null,
                    input  string            fname = "",
                    input  int               lineno = 0);

   // create an abstract transaction for this operation
   uvm_reg_item rw = uvm_reg_item::type_id::create("mem_write",,get_full_name());
   rw.element      = this;
   rw.element_kind = UVM_MEM;
   rw.kind         = UVM_WRITE;
   rw.offset       = offset;
   rw.value[0]     = value;
   rw.path         = path;
   rw.map          = map;
   rw.parent       = parent;
   rw.prior        = prior;
   rw.extension    = extension;
   rw.fname        = fname;
   rw.lineno       = lineno;

   do_write(rw);

   status = rw.status;

endtask: write


// read

task uvm_mem::read(output uvm_status_e       status,
                   input  uvm_reg_addr_t     offset,
                   output uvm_reg_data_t     value,
                   input  uvm_door_e         path = UVM_DEFAULT_DOOR,
                   input  uvm_reg_map        map = null,
                   input  uvm_sequence_base  parent = null,
                   input  int                prior = -1,
                   input  uvm_object         extension = null,
                   input  string             fname = "",
                   input  int                lineno = 0);
   
   uvm_reg_item rw;
   rw = uvm_reg_item::type_id::create("mem_read",,get_full_name());
   rw.element      = this;
   rw.element_kind = UVM_MEM;
   rw.kind         = UVM_READ;
   rw.value[0]     = 0;
   rw.offset       = offset;
   rw.path         = path;
   rw.map          = map;
   rw.parent       = parent;
   rw.prior        = prior;
   rw.extension    = extension;
   rw.fname        = fname;
   rw.lineno       = lineno;

   do_read(rw);

   status = rw.status;
   value = rw.value[0];

endtask: read


// burst_write

task uvm_mem::burst_write(output uvm_status_e       status,
                          input  uvm_reg_addr_t     offset,
                          input  uvm_reg_data_t     value[],
                          input  uvm_door_e         path = UVM_DEFAULT_DOOR,
                          input  uvm_reg_map        map = null,
                          input  uvm_sequence_base  parent = null,
                          input  int                prior = -1,
                          input  uvm_object         extension = null,
                          input  string             fname = "",
                          input  int                lineno = 0);

   uvm_reg_item rw;
   rw = uvm_reg_item::type_id::create("mem_burst_write",,get_full_name());
   rw.element      = this;
   rw.element_kind = UVM_MEM;
   rw.kind         = UVM_BURST_WRITE;
   rw.offset       = offset;
   rw.value        = value;
   rw.path         = path;
   rw.map          = map;
   rw.parent       = parent;
   rw.prior        = prior;
   rw.extension    = extension;
   rw.fname        = fname;
   rw.lineno       = lineno;

   do_write(rw);

   status = rw.status;

endtask: burst_write


// burst_read

task uvm_mem::burst_read(output uvm_status_e       status,
                         input  uvm_reg_addr_t     offset,
                         ref    uvm_reg_data_t     value[],
                         input  uvm_door_e         path = UVM_DEFAULT_DOOR,
                         input  uvm_reg_map        map = null,
                         input  uvm_sequence_base  parent = null,
                         input  int                prior = -1,
                         input  uvm_object         extension = null,
                         input  string             fname = "",
                         input  int                lineno = 0);

   uvm_reg_item rw;
   rw = uvm_reg_item::type_id::create("mem_burst_read",,get_full_name());
   rw.element      = this;
   rw.element_kind = UVM_MEM;
   rw.kind         = UVM_BURST_READ;
   rw.offset       = offset;
   rw.value        = value;
   rw.path         = path;
   rw.map          = map;
   rw.parent       = parent;
   rw.prior        = prior;
   rw.extension    = extension;
   rw.fname        = fname;
   rw.lineno       = lineno;

   do_read(rw);

   status = rw.status;
   value  = rw.value;

endtask: burst_read


// do_write

task uvm_mem::do_write(uvm_reg_item rw);

   uvm_mem_cb_iter  cbs = new(this);
   uvm_reg_map_info map_info;
   
   m_fname  = rw.fname;
   m_lineno = rw.lineno;

   if (!Xcheck_accessX(rw, map_info))
     return;

   m_write_in_progress = 1'b1;

   rw.status = UVM_IS_OK;
   
   // PRE-WRITE CBS
   pre_write(rw);
   for (uvm_reg_cbs cb=cbs.first(); cb!=null; cb=cbs.next())
      cb.pre_write(rw);

   if (rw.status != UVM_IS_OK) begin
      m_write_in_progress = 1'b0;

      return;
   end

   rw.status = UVM_NOT_OK;

   // FRONTDOOR
   if (rw.path == UVM_FRONTDOOR) begin

      uvm_reg_map system_map = rw.local_map.get_root_map();
      
      if (map_info.frontdoor != null) begin
         uvm_reg_frontdoor fd = map_info.frontdoor;
         fd.rw_info = rw;
         if (fd.sequencer == null)
           fd.sequencer = system_map.get_sequencer();
         fd.start(fd.sequencer, rw.parent);
      end
      else begin
         rw.local_map.do_write(rw);
      end

      if (rw.status != UVM_NOT_OK)
         for (uvm_reg_addr_t idx = rw.offset;
              idx <= rw.offset + rw.value.size();
              idx++) begin
            XsampleX(map_info.mem_range.stride * idx, 0, rw.map);
            m_parent.XsampleX(map_info.offset +
                             (map_info.mem_range.stride * idx),
                              0, rw.map);
         end
   end
      
   // BACKDOOR     
   else begin
      // Mimick front door access, i.e. do not write read-only memories
      if (get_access(rw.map) inside {"RW", "WO"}) begin
         uvm_reg_backdoor bkdr = get_backdoor();
         if (bkdr != null)
            bkdr.write(rw);
         else
            backdoor_write(rw);
      end
      else
         rw.status = UVM_NOT_OK;
   end

   // POST-WRITE CBS
   post_write(rw);
   for (uvm_reg_cbs cb=cbs.first(); cb!=null; cb=cbs.next())
      cb.post_write(rw);

   // REPORT
   if (uvm_report_enabled(UVM_HIGH, UVM_INFO, "RegModel")) begin
     string path_s,value_s,pre_s,range_s;
     if (rw.path == UVM_FRONTDOOR)
       path_s = (map_info.frontdoor != null) ? "user frontdoor" :
                                               {"map ",rw.map.get_full_name()};
     else
       path_s = (get_backdoor() != null) ? "user backdoor" : "DPI backdoor";

     if (rw.value.size() > 1) begin
       value_s = "='{";
       pre_s = "Burst ";
       foreach (rw.value[i])
         value_s = {value_s,$sformatf("%0h,",rw.value[i])};
       value_s[value_s.len()-1]="}";
       range_s = $sformatf("[%0d:%0d]",rw.offset,rw.offset+rw.value.size());
     end
     else begin
       value_s = $sformatf("=%0h",rw.value[0]);
       range_s = $sformatf("[%0d]",rw.offset);
     end

     `uvm_info("RegModel", {pre_s,"Wrote memory via ",path_s,": ",
                                  get_full_name(),range_s,value_s}, UVM_HIGH)
   end

   m_write_in_progress = 1'b0;

endtask: do_write


// do_read

task uvm_mem::do_read(uvm_reg_item rw);

   uvm_mem_cb_iter cbs = new(this);
   uvm_reg_map_info map_info;
   
   m_fname = rw.fname;
   m_lineno = rw.lineno;

   if (!Xcheck_accessX(rw, map_info))
     return;

   m_read_in_progress = 1'b1;

   rw.status = UVM_IS_OK;
   
   // PRE-READ CBS
   pre_read(rw);
   for (uvm_reg_cbs cb=cbs.first(); cb!=null; cb=cbs.next())
      cb.pre_read(rw);

   if (rw.status != UVM_IS_OK) begin
      m_read_in_progress = 1'b0;

      return;
   end

   rw.status = UVM_NOT_OK;

   // FRONTDOOR
   if (rw.path == UVM_FRONTDOOR) begin
      
      uvm_reg_map system_map = rw.local_map.get_root_map();
         
      if (map_info.frontdoor != null) begin
         uvm_reg_frontdoor fd = map_info.frontdoor;
         fd.rw_info = rw;
         if (fd.sequencer == null)
           fd.sequencer = system_map.get_sequencer();
         fd.start(fd.sequencer, rw.parent);
      end
      else begin
         rw.local_map.do_read(rw);
      end

      if (rw.status != UVM_NOT_OK)
         for (uvm_reg_addr_t idx = rw.offset;
              idx <= rw.offset + rw.value.size();
              idx++) begin
            XsampleX(map_info.mem_range.stride * idx, 1, rw.map);
            m_parent.XsampleX(map_info.offset +
                             (map_info.mem_range.stride * idx),
                              1, rw.map);
         end
   end

   // BACKDOOR
   else begin
      // Mimick front door access, i.e. do not read write-only memories
      if (get_access(rw.map) inside {"RW", "RO"}) begin
         uvm_reg_backdoor bkdr = get_backdoor();
         if (bkdr != null)
            bkdr.read(rw);
         else
            backdoor_read(rw);
      end
      else
         rw.status = UVM_NOT_OK;
   end


   // POST-READ CBS
   post_read(rw);
   for (uvm_reg_cbs cb=cbs.first(); cb!=null; cb=cbs.next())
      cb.post_read(rw);

   // REPORT
   if (uvm_report_enabled(UVM_HIGH, UVM_INFO, "RegModel")) begin
     string path_s,value_s,pre_s,range_s;
     if (rw.path == UVM_FRONTDOOR)
       path_s = (map_info.frontdoor != null) ? "user frontdoor" :
                                               {"map ",rw.map.get_full_name()};
     else
       path_s = (get_backdoor() != null) ? "user backdoor" : "DPI backdoor";

     if (rw.value.size() > 1) begin
       value_s = "='{";
       pre_s = "Burst ";
       foreach (rw.value[i])
         value_s = {value_s,$sformatf("%0h,",rw.value[i])};
       value_s[value_s.len()-1]="}";
       range_s = $sformatf("[%0d:%0d]",rw.offset,(rw.offset+rw.value.size()));
     end
     else begin
       value_s = $sformatf("=%0h",rw.value[0]);
       range_s = $sformatf("[%0d]",rw.offset);
     end

      `uvm_info("RegModel", {pre_s,"Read memory via ",path_s,": ",
                                   get_full_name(),range_s,value_s}, UVM_HIGH)
   end

   m_read_in_progress = 1'b0;

endtask: do_read


// Xcheck_accessX

function bit uvm_mem::Xcheck_accessX(input uvm_reg_item rw,
                                     output uvm_reg_map_info map_info);

   if (rw.offset >= m_size) begin
      `uvm_error(get_type_name(), 
         $sformatf("Offset 'h%0h exceeds size of memory, 'h%0h",
           rw.offset, m_size))
      rw.status = UVM_NOT_OK;
      return 0;
   end

   if (rw.path == UVM_DEFAULT_DOOR)
     rw.path = m_parent.get_default_door();

   if (rw.path == UVM_BACKDOOR) begin
      if (get_backdoor() == null && !has_hdl_path()) begin
         `uvm_warning("RegModel",
            {"No backdoor access available for memory '",get_full_name(),
            "' . Using frontdoor instead."})
         rw.path = UVM_FRONTDOOR;
      end
      else if (rw.map == null) begin
         if (get_default_map() != null)
            rw.map = get_default_map();
         else
           rw.map = uvm_reg_map::backdoor();
      end
      //otherwise use the map specified in user's call to memory read/write
   end

   if (rw.path != UVM_BACKDOOR) begin

     rw.local_map = get_local_map(rw.map);

     if (rw.local_map == null) begin
        `uvm_error(get_type_name(), 
           {"No transactor available to physically access memory from map '",
            rw.map.get_full_name(),"'"})
        rw.status = UVM_NOT_OK;
        return 0;
     end

     map_info = rw.local_map.get_mem_map_info(this);

     if (map_info.frontdoor == null) begin

        if (map_info.unmapped) begin
           `uvm_error("RegModel", {"Memory '",get_full_name(),
                      "' unmapped in map '", rw.map.get_full_name(),
                      "' and does not have a user-defined frontdoor"})
           rw.status = UVM_NOT_OK;
           return 0;
        end

        if ((rw.value.size() > 1)) begin
           if (get_n_bits() > rw.local_map.get_n_bytes()*8) begin
              `uvm_error("RegModel",
                    $sformatf("Cannot burst a %0d-bit memory through a narrower data path (%0d bytes)",
                    get_n_bits(), rw.local_map.get_n_bytes()*8))
              rw.status = UVM_NOT_OK;
              return 0;
           end
           if (rw.offset + rw.value.size() > m_size) begin
              `uvm_error("RegModel",
                  $sformatf("Burst of size 'd%0d starting at offset 'd%0d exceeds size of memory, 'd%0d",
                      rw.value.size(), rw.offset, m_size))
              return 0;
           end
        end
     end

     if (rw.map == null)
       rw.map = rw.local_map;
   end

   return 1;
endfunction


//-------
// ACCESS
//-------

// poke

task uvm_mem::poke(output uvm_status_e      status,
                   input  uvm_reg_addr_t    offset,
                   input  uvm_reg_data_t    value,
                   input  string            kind = "",
                   input  uvm_sequence_base parent = null,
                   input  uvm_object        extension = null,
                   input  string            fname = "",
                   input  int               lineno = 0);
   uvm_reg_item rw;
   uvm_reg_backdoor bkdr = get_backdoor();

   m_fname = fname;
   m_lineno = lineno;

   if (bkdr == null && !has_hdl_path(kind)) begin
      `uvm_error("RegModel", {"No backdoor access available in memory '",
                             get_full_name(),"'"})
      status = UVM_NOT_OK;
      return;
   end

   // create an abstract transaction for this operation
   rw = uvm_reg_item::type_id::create("mem_poke_item",,get_full_name());
   rw.element      = this;
   rw.path         = UVM_BACKDOOR;
   rw.element_kind = UVM_MEM;
   rw.kind         = UVM_WRITE;
   rw.offset       = offset;
   rw.value[0]     = value & ((1 << m_n_bits)-1);
   rw.bd_kind      = kind;
   rw.parent       = parent;
   rw.extension    = extension;
   rw.fname        = fname;
   rw.lineno       = lineno;

   if (bkdr != null)
     bkdr.write(rw);
   else
     backdoor_write(rw);

   status = rw.status;

   `uvm_info("RegModel", $sformatf("Poked memory '%s[%0d]' with value 'h%h",
                              get_full_name(), offset, value),UVM_HIGH)

endtask: poke


// peek

task uvm_mem::peek(output uvm_status_e      status,
                   input  uvm_reg_addr_t    offset,
                   output uvm_reg_data_t    value,
                   input  string            kind = "",
                   input  uvm_sequence_base parent = null,
                   input  uvm_object        extension = null,
                   input  string            fname = "",
                   input  int               lineno = 0);
   uvm_reg_backdoor bkdr = get_backdoor();
   uvm_reg_item rw;

   m_fname = fname;
   m_lineno = lineno;

   if (bkdr == null && !has_hdl_path(kind)) begin
      `uvm_error("RegModel", {"No backdoor access available in memory '",
                 get_full_name(),"'"})
      status = UVM_NOT_OK;
      return;
   end

   // create an abstract transaction for this operation
   rw = uvm_reg_item::type_id::create("mem_peek_item",,get_full_name());
   rw.element      = this;
   rw.path         = UVM_BACKDOOR;
   rw.element_kind = UVM_MEM;
   rw.kind         = UVM_READ;
   rw.offset       = offset;
   rw.bd_kind      = kind;
   rw.parent       = parent;
   rw.extension    = extension;
   rw.fname        = fname;
   rw.lineno       = lineno;

   if (bkdr != null)
     bkdr.read(rw);
   else
     backdoor_read(rw);

   status = rw.status;
   value  = rw.value[0];

   `uvm_info("RegModel", $sformatf("Peeked memory '%s[%0d]' has value 'h%h",
                         get_full_name(), offset, value),UVM_HIGH)
endtask: peek


//-----------------
// Group- Frontdoor
//-----------------

// set_frontdoor

function void uvm_mem::set_frontdoor(uvm_reg_frontdoor ftdr,
                                     uvm_reg_map       map = null,
                                     string            fname = "",
                                     int               lineno = 0);
   uvm_reg_map_info map_info;
   m_fname = fname;
   m_lineno = lineno;

   map = get_local_map(map);

   if (map == null) begin
      `uvm_error("RegModel", {"Memory '",get_full_name(),
                 "' not found in map '", map.get_full_name(),"'"})
      return;
   end

   map_info = map.get_mem_map_info(this);
   map_info.frontdoor = ftdr;

endfunction: set_frontdoor


// get_frontdoor

function uvm_reg_frontdoor uvm_mem::get_frontdoor(uvm_reg_map map = null);
   uvm_reg_map_info map_info;

   map = get_local_map(map);

   if (map == null) begin
      `uvm_error("RegModel", {"Memory '",get_full_name(),
                 "' not found in map '", map.get_full_name(),"'"})
      return null;
   end

   map_info = map.get_mem_map_info(this);
   return map_info.frontdoor;

endfunction: get_frontdoor


//----------------
// Group- Backdoor
//----------------

// set_backdoor

function void uvm_mem::set_backdoor(uvm_reg_backdoor bkdr,
                                    string fname = "",
                                    int lineno = 0);
   m_fname = fname;
   m_lineno = lineno;
   m_backdoor = bkdr;
endfunction: set_backdoor


// get_backdoor

function uvm_reg_backdoor uvm_mem::get_backdoor(bit inherited = 1);
   
   if (m_backdoor == null && inherited) begin
     uvm_reg_block blk = get_parent();
     uvm_reg_backdoor bkdr;
     while (blk != null) begin
       bkdr = blk.get_backdoor();
       if (bkdr != null) begin
         m_backdoor = bkdr;
         break;
       end
       blk = blk.get_parent();
     end
   end

   return m_backdoor;
endfunction: get_backdoor


// backdoor_read_func

function uvm_status_e uvm_mem::backdoor_read_func(uvm_reg_item rw);

  uvm_hdl_path_concat paths[$];
  uvm_hdl_data_t val;
  bit ok=1;

  get_full_hdl_path(paths,rw.bd_kind);

  foreach (rw.value[mem_idx]) begin
     string idx;
     idx.itoa(rw.offset + mem_idx);
     foreach (paths[i]) begin
        uvm_hdl_path_concat hdl_concat = paths[i];
        val = 0;
        foreach (hdl_concat.slices[j]) begin
           string hdl_path = {hdl_concat.slices[j].path, "[", idx, "]"};

           `uvm_info("RegModel", {"backdoor_read from ",hdl_path},UVM_DEBUG)
 
           if (hdl_concat.slices[j].offset < 0) begin
              ok &= uvm_hdl_read(hdl_path, val);
              continue;
           end
           begin
              uvm_reg_data_t slice;
              int k = hdl_concat.slices[j].offset;
              ok &= uvm_hdl_read(hdl_path, slice);
              repeat (hdl_concat.slices[j].size) begin
                 val[k++] = slice[0];
                 slice >>= 1;
              end
           end
        end

        val &= (1 << m_n_bits)-1;

        if (i == 0)
           rw.value[mem_idx] = val;

        if (val != rw.value[mem_idx]) begin
           `uvm_error("RegModel", $sformatf("Backdoor read of register %s with multiple HDL copies: values are not the same: %0h at path '%s', and %0h at path '%s'. Returning first value.",
               get_full_name(), rw.value[mem_idx], uvm_hdl_concat2string(paths[0]),
               val, uvm_hdl_concat2string(paths[i])))
           return UVM_NOT_OK;
         end
      end
  end

  rw.status = (ok) ? UVM_IS_OK : UVM_NOT_OK;

  return rw.status;
endfunction


// backdoor_read

task uvm_mem::backdoor_read(uvm_reg_item rw);
  rw.status = backdoor_read_func(rw);
endtask


// backdoor_write

task uvm_mem::backdoor_write(uvm_reg_item rw);

  uvm_hdl_path_concat paths[$];
  bit ok=1;

   
  get_full_hdl_path(paths,rw.bd_kind);
   
  foreach (rw.value[mem_idx]) begin
     string idx;
     idx.itoa(rw.offset + mem_idx);
     foreach (paths[i]) begin
       uvm_hdl_path_concat hdl_concat = paths[i];
       foreach (hdl_concat.slices[j]) begin
          `uvm_info("RegModel", $sformatf("backdoor_write to %s ",hdl_concat.slices[j].path),UVM_DEBUG)
 
          if (hdl_concat.slices[j].offset < 0) begin
             ok &= uvm_hdl_deposit({hdl_concat.slices[j].path,"[", idx, "]"},rw.value[mem_idx]);
             continue;
          end
          begin
            uvm_reg_data_t slice;
            slice = rw.value[mem_idx] >> hdl_concat.slices[j].offset;
            slice &= (1 << hdl_concat.slices[j].size)-1;
            ok &= uvm_hdl_deposit({hdl_concat.slices[j].path, "[", idx, "]"}, slice);
          end
       end
     end
  end
  rw.status = (ok ? UVM_IS_OK : UVM_NOT_OK);
endtask




// clear_hdl_path

function void uvm_mem::clear_hdl_path(string kind = "RTL");
  if (kind == "ALL") begin
    m_hdl_paths_pool = new("hdl_paths");
    return;
  end

  if (kind == "")
    kind = m_parent.get_default_hdl_path();

  if (!m_hdl_paths_pool.exists(kind)) begin
    `uvm_warning("RegModel",{"Unknown HDL Abstraction '",kind,"'"})
    return;
  end

  m_hdl_paths_pool.delete(kind);
endfunction


// add_hdl_path

function void uvm_mem::add_hdl_path(uvm_hdl_path_slice slices[], string kind = "RTL");
    uvm_queue #(uvm_hdl_path_concat) paths = m_hdl_paths_pool.get(kind);
    uvm_hdl_path_concat concat = new();

    concat.set(slices);
    paths.push_back(concat);  
endfunction


// add_hdl_path_slice

function void uvm_mem::add_hdl_path_slice(string name,
                                          int offset,
                                          int size,
                                          bit first = 0,
                                          string kind = "RTL");
    uvm_queue #(uvm_hdl_path_concat) paths=m_hdl_paths_pool.get(kind);
    uvm_hdl_path_concat concat;

    if (first || paths.size() == 0) begin
       concat = new();
       paths.push_back(concat);
    end
    else
       concat = paths.get(paths.size()-1);
     
    concat.add_path(name, offset, size);
endfunction


// has_hdl_path

function bit  uvm_mem::has_hdl_path(string kind = "");
  if (kind == "")
    kind = m_parent.get_default_hdl_path();
  
  return m_hdl_paths_pool.exists(kind);
endfunction


// get_hdl_path

function void uvm_mem::get_hdl_path(ref uvm_hdl_path_concat paths[$],
                                    input string kind = "");

  uvm_queue #(uvm_hdl_path_concat) hdl_paths;

  if (kind == "")
     kind = m_parent.get_default_hdl_path();

  if (!has_hdl_path(kind)) begin
    `uvm_error("RegModel",
        {"Memory does not have hdl path defined for abstraction '",kind,"'"})
    return;
  end

  hdl_paths = m_hdl_paths_pool.get(kind);

  for (int i=0; i<hdl_paths.size();i++) begin
     uvm_hdl_path_concat t = hdl_paths.get(i);
     paths.push_back(t);
  end

endfunction


// get_hdl_path_kinds

function void uvm_mem::get_hdl_path_kinds (ref string kinds[$]);
  string kind;
  kinds.delete();
  if (!m_hdl_paths_pool.first(kind))
    return;
  do
    kinds.push_back(kind);
  while (m_hdl_paths_pool.next(kind));
endfunction

// get_full_hdl_path

function void uvm_mem::get_full_hdl_path(ref uvm_hdl_path_concat paths[$],
                                         input string kind = "",
                                         input string separator = ".");

   if (kind == "")
      kind = m_parent.get_default_hdl_path();
   
   if (!has_hdl_path(kind)) begin
      `uvm_error("RegModel",
          {"Memory does not have hdl path defined for abstraction '",kind,"'"})
      return;
   end

   begin
      uvm_queue #(uvm_hdl_path_concat) hdl_paths = m_hdl_paths_pool.get(kind);
      string parent_paths[$];

      m_parent.get_full_hdl_path(parent_paths, kind, separator);

      for (int i=0; i<hdl_paths.size();i++) begin
         uvm_hdl_path_concat hdl_concat = hdl_paths.get(i);

         foreach (parent_paths[j])  begin
            uvm_hdl_path_concat t = new;

            foreach (hdl_concat.slices[k]) begin
               if (hdl_concat.slices[k].path == "")
                  t.add_path(parent_paths[j]);
               else
                  t.add_path({ parent_paths[j], separator, hdl_concat.slices[k].path },
                             hdl_concat.slices[k].offset,
                             hdl_concat.slices[k].size);
            end
            paths.push_back(t);
         end
      end
   end
endfunction


// set_parent

function void uvm_mem::set_parent(uvm_reg_block parent);
  m_parent = parent;
endfunction


// get_parent

function uvm_reg_block uvm_mem::get_parent();
   return get_block();
endfunction


// convert2string

function string uvm_mem::convert2string();

   string res_str;
   string prefix;

   $sformat(convert2string, "%sMemory %s -- %0dx%0d bits", prefix,
            get_full_name(), get_size(), get_n_bits());

   if (m_maps.num()==0)
     convert2string = {convert2string, "  (unmapped)\n"};
   else
     convert2string = {convert2string, "\n"};
   foreach (m_maps[map]) begin
     uvm_reg_map parent_map = map;
     int unsigned offset;
     while (parent_map != null) begin
       uvm_reg_map this_map = parent_map;
       uvm_endianness_e endian_name;
       parent_map = this_map.get_parent_map();
       endian_name=this_map.get_endian();
       
       offset = parent_map == null ? this_map.get_base_addr(UVM_NO_HIER) :
                                     parent_map.get_submap_offset(this_map);
       prefix = {prefix, "  "};
       $sformat(convert2string, "%sMapped in '%s' -- buswidth %0d bytes, %s, offset 'h%0h, size 'h%0h, %s\n", prefix,
            this_map.get_full_name(), this_map.get_n_bytes(), endian_name.name(), offset,get_size(),get_access(this_map));
     end
   end
   prefix = "  ";
   if (m_read_in_progress == 1'b1) begin
      if (m_fname != "" && m_lineno != 0)
         $sformat(res_str, "%s:%0d ",m_fname, m_lineno);
      convert2string = {convert2string, "  ", res_str,
                       "currently executing read method"}; 
   end
   if ( m_write_in_progress == 1'b1) begin
      if (m_fname != "" && m_lineno != 0)
         $sformat(res_str, "%s:%0d ",m_fname, m_lineno);
      convert2string = {convert2string, "  ", res_str,
                       "currently executing write method"}; 
   end
endfunction


// do_print

function void uvm_mem::do_print (uvm_printer printer);
  super.do_print(printer);
  //printer.print_generic(" ", " ", -1, convert2string());
  printer.print_field_int("n_bits",get_n_bits(),32, UVM_UNSIGNED);
  printer.print_field_int("size",get_size(),32, UVM_UNSIGNED);
endfunction


// clone

function uvm_object uvm_mem::clone();
  `uvm_fatal("RegModel","RegModel memories cannot be cloned")
  return null;
endfunction

// do_copy

function void uvm_mem::do_copy(uvm_object rhs);
  `uvm_fatal("RegModel","RegModel memories cannot be copied")
endfunction


// do_compare

function bit uvm_mem::do_compare (uvm_object  rhs,
                                        uvm_comparer comparer);
  `uvm_warning("RegModel","RegModel memories cannot be compared")
  return 0;
endfunction


// do_pack

function void uvm_mem::do_pack (uvm_packer packer);
  `uvm_warning("RegModel","RegModel memories cannot be packed")
endfunction


// do_unpack

function void uvm_mem::do_unpack (uvm_packer packer);
  `uvm_warning("RegModel","RegModel memories cannot be unpacked")
endfunction


// Xadd_vregX

function void uvm_mem::Xadd_vregX(uvm_vreg vreg);
  m_vregs[vreg] = 1;
endfunction


// Xdelete_vregX

function void uvm_mem::Xdelete_vregX(uvm_vreg vreg);
   if (m_vregs.exists(vreg))
     m_vregs.delete(vreg);
endfunction

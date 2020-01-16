//
// -------------------------------------------------------------
// Copyright 2010-2012 Mentor Graphics Corporation
// Copyright 2011-2014 Semifore
// Copyright 2018 Intel Corporation
// Copyright 2004-2018 Synopsys, Inc.
// Copyright 2010-2018 Cadence Design Systems, Inc.
// Copyright 2010 AMD
// Copyright 2014-2018 NVIDIA Corporation
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
//

typedef class uvm_reg_cbs;
typedef class uvm_reg_frontdoor;


// @uvm-ieee 1800.2-2017 auto 18.4.1
class uvm_reg extends uvm_object;

   local bit               m_locked;
   local uvm_reg_block     m_parent;
   local uvm_reg_file      m_regfile_parent;
   local int unsigned      m_n_bits;
   local int unsigned      m_n_used_bits;
   protected bit           m_maps[uvm_reg_map];
   protected uvm_reg_field m_fields[$];   // Fields in LSB to MSB order
   local int               m_has_cover;
   local int               m_cover_on;
   local semaphore         m_atomic;
   local process           m_process;
   local string            m_fname;
   local int               m_lineno;
   local bit               m_read_in_progress;
   local bit               m_write_in_progress; 
   protected bit           m_update_in_progress;
   /*local*/ bit           m_is_busy;
   /*local*/ bit           m_is_locked_by_field;
   local uvm_reg_backdoor  m_backdoor;

   local static int unsigned m_max_size;

   local uvm_object_string_pool
       #(uvm_queue #(uvm_hdl_path_concat)) m_hdl_paths_pool;

   //----------------------
   // Group -- NODOCS -- Initialization
   //----------------------


   // @uvm-ieee 1800.2-2017 auto 18.4.2.1
   extern function new (string name="",
                        int unsigned n_bits,
                        int has_coverage);



   // @uvm-ieee 1800.2-2017 auto 18.4.2.2
   extern function void configure (uvm_reg_block blk_parent,
                                   uvm_reg_file regfile_parent = null,
                                   string hdl_path = "");



   // @uvm-ieee 1800.2-2017 auto 18.4.2.3
   extern virtual function void set_offset (uvm_reg_map    map,
                                            uvm_reg_addr_t offset,
                                            bit            unmapped = 0);

   /*local*/ extern virtual function void set_parent (uvm_reg_block blk_parent,
                                                      uvm_reg_file regfile_parent);
   /*local*/ extern virtual function void add_field  (uvm_reg_field field);
   /*local*/ extern virtual function void add_map    (uvm_reg_map map);

   /*local*/ extern function void   Xlock_modelX;

	// remove the knowledge that the register resides in the map from the register instance
	// @uvm-ieee 1800.2-2017 auto 18.4.2.5
	virtual function void unregister(uvm_reg_map map);
		m_maps.delete(map);
	endfunction
	

   //---------------------
   // Group -- NODOCS -- Introspection
   //---------------------

   // Function -- NODOCS -- get_name
   //
   // Get the simple name
   //
   // Return the simple object name of this register.
   //

   // Function -- NODOCS -- get_full_name
   //
   // Get the hierarchical name
   //
   // Return the hierarchal name of this register.
   // The base of the hierarchical name is the root block.
   //
   extern virtual function string get_full_name();



   // @uvm-ieee 1800.2-2017 auto 18.4.3.1
   extern virtual function uvm_reg_block get_parent ();
   extern virtual function uvm_reg_block get_block  ();



   // @uvm-ieee 1800.2-2017 auto 18.4.3.2
   extern virtual function uvm_reg_file get_regfile ();



   // @uvm-ieee 1800.2-2017 auto 18.4.3.3
   extern virtual function int get_n_maps ();



   // @uvm-ieee 1800.2-2017 auto 18.4.3.4
   extern function bit is_in_map (uvm_reg_map map);



   // @uvm-ieee 1800.2-2017 auto 18.4.3.5
   extern virtual function void get_maps (ref uvm_reg_map maps[$]);


   /*local*/ extern virtual function uvm_reg_map get_local_map   (uvm_reg_map map);
   /*local*/ extern virtual function uvm_reg_map get_default_map ();



   // @uvm-ieee 1800.2-2017 auto 18.4.3.6
   extern virtual function string get_rights (uvm_reg_map map = null);


   // Function -- NODOCS -- get_n_bits
   //
   // Returns the width, in bits, of this register.
   //
   extern virtual function int unsigned get_n_bits ();


   // Function -- NODOCS -- get_n_bytes
   //
   // Returns the width, in bytes, of this register. Rounds up to
   // next whole byte if register is not a multiple of 8.
   //
   extern virtual function int unsigned get_n_bytes();


   // Function -- NODOCS -- get_max_size
   //
   // Returns the maximum width, in bits, of all registers. 
   //
   extern static function int unsigned get_max_size();



   // @uvm-ieee 1800.2-2017 auto 18.4.3.10
   extern virtual function void get_fields (ref uvm_reg_field fields[$]);



   // @uvm-ieee 1800.2-2017 auto 18.4.3.11
   extern virtual function uvm_reg_field get_field_by_name(string name);


   /*local*/ extern function string Xget_fields_accessX(uvm_reg_map map);



   // @uvm-ieee 1800.2-2017 auto 18.4.3.12
   extern virtual function uvm_reg_addr_t get_offset (uvm_reg_map map = null);



   // @uvm-ieee 1800.2-2017 auto 18.4.3.13
   extern virtual function uvm_reg_addr_t get_address (uvm_reg_map map = null);



   // @uvm-ieee 1800.2-2017 auto 18.4.3.14
   extern virtual function int get_addresses (uvm_reg_map map = null,
                                              ref uvm_reg_addr_t addr[]);



   //--------------
   // Group -- NODOCS -- Access
   //--------------



   // @uvm-ieee 1800.2-2017 auto 18.4.4.2
   extern virtual function void set (uvm_reg_data_t  value,
                                     string          fname = "",
                                     int             lineno = 0);



   // @uvm-ieee 1800.2-2017 auto 18.4.4.1
   extern virtual function uvm_reg_data_t  get(string  fname = "",
                                               int     lineno = 0);


   // @uvm-ieee 1800.2-2017 auto 18.4.4.3
   extern virtual function uvm_reg_data_t  get_mirrored_value(string  fname = "",
                                               int     lineno = 0);



   // @uvm-ieee 1800.2-2017 auto 18.4.4.4
   extern virtual function bit needs_update(); 



   // @uvm-ieee 1800.2-2017 auto 18.4.4.5
   extern virtual function void reset(string kind = "HARD");


   // Function -- NODOCS -- get_reset
   //
   // Get the specified reset value for this register
   //
   // Return the reset value for this register
   // for the specified reset ~kind~.
   //
   extern virtual function uvm_reg_data_t
                             // @uvm-ieee 1800.2-2017 auto 18.4.4.6
                             get_reset(string kind = "HARD");



   // @uvm-ieee 1800.2-2017 auto 18.4.4.7
   extern virtual function bit has_reset(string kind = "HARD",
                                         bit    delete = 0);


   // Function -- NODOCS -- set_reset
   //
   // Specify or modify the reset value for this register
   //
   // Specify or modify the reset value for all the fields in the register
   // corresponding to the cause specified by ~kind~.
   //
   extern virtual function void
                       // @uvm-ieee 1800.2-2017 auto 18.4.4.8
                       set_reset(uvm_reg_data_t value,
                                 string         kind = "HARD");



   // @uvm-ieee 1800.2-2017 auto 18.4.4.9
   // @uvm-ieee 1800.2-2017 auto 18.8.5.3
   extern virtual task write(output uvm_status_e      status,
                             input  uvm_reg_data_t    value,
                             input  uvm_door_e        path = UVM_DEFAULT_DOOR,
                             input  uvm_reg_map       map = null,
                             input  uvm_sequence_base parent = null,
                             input  int               prior = -1,
                             input  uvm_object        extension = null,
                             input  string            fname = "",
                             input  int               lineno = 0);



   // @uvm-ieee 1800.2-2017 auto 18.4.4.10
   // @uvm-ieee 1800.2-2017 auto 18.8.5.4
   extern virtual task read(output uvm_status_e      status,
                            output uvm_reg_data_t    value,
                            input  uvm_door_e        path = UVM_DEFAULT_DOOR,
                            input  uvm_reg_map       map = null,
                            input  uvm_sequence_base parent = null,
                            input  int               prior = -1,
                            input  uvm_object        extension = null,
                            input  string            fname = "",
                            input  int               lineno = 0);



   // @uvm-ieee 1800.2-2017 auto 18.4.4.11
   // @uvm-ieee 1800.2-2017 auto 18.8.5.5
   // @uvm-ieee 1800.2-2017 auto 18.8.5.6
   extern virtual task poke(output uvm_status_e      status,
                            input  uvm_reg_data_t    value,
                            input  string            kind = "",
                            input  uvm_sequence_base parent = null,
                            input  uvm_object        extension = null,
                            input  string            fname = "",
                            input  int               lineno = 0);



   // @uvm-ieee 1800.2-2017 auto 18.4.4.12
   extern virtual task peek(output uvm_status_e      status,
                            output uvm_reg_data_t    value,
                            input  string            kind = "",
                            input  uvm_sequence_base parent = null,
                            input  uvm_object        extension = null,
                            input  string            fname = "",
                            input  int               lineno = 0);



   // @uvm-ieee 1800.2-2017 auto 18.4.4.13
   extern virtual task update(output uvm_status_e      status,
                              input  uvm_door_e        path = UVM_DEFAULT_DOOR,
                              input  uvm_reg_map       map = null,
                              input  uvm_sequence_base parent = null,
                              input  int               prior = -1,
                              input  uvm_object        extension = null,
                              input  string            fname = "",
                              input  int               lineno = 0);



   // @uvm-ieee 1800.2-2017 auto 18.4.4.14
   // @uvm-ieee 1800.2-2017 auto 18.8.5.8
   extern virtual task mirror(output uvm_status_e      status,
                              input uvm_check_e        check  = UVM_NO_CHECK,
                              input uvm_door_e         path = UVM_DEFAULT_DOOR,
                              input uvm_reg_map        map = null,
                              input uvm_sequence_base  parent = null,
                              input int                prior = -1,
                              input  uvm_object        extension = null,
                              input string             fname = "",
                              input int                lineno = 0);



   // @uvm-ieee 1800.2-2017 auto 18.4.4.15
   // @uvm-ieee 1800.2-2017 auto 18.8.5.9
   extern virtual function bit predict (uvm_reg_data_t    value,
                                        uvm_reg_byte_en_t be = -1,
                                        uvm_predict_e     kind = UVM_PREDICT_DIRECT,
                                        uvm_door_e        path = UVM_FRONTDOOR,
                                        uvm_reg_map       map = null,
                                        string            fname = "",
                                        int               lineno = 0);



   // @uvm-ieee 1800.2-2017 auto 18.4.4.16
   extern function bit is_busy();



   /*local*/ extern function void Xset_busyX(bit busy);

   /*local*/ extern task XreadX (output uvm_status_e      status,
                                 output uvm_reg_data_t    value,
                                 input  uvm_door_e        path,
                                 input  uvm_reg_map       map,
                                 input  uvm_sequence_base parent = null,
                                 input  int               prior = -1,
                                 input  uvm_object        extension = null,
                                 input  string            fname = "",
                                 input  int               lineno = 0);
   
   /*local*/ extern task XatomicX(bit on);

   /*local*/ extern virtual function bit Xcheck_accessX
                                (input uvm_reg_item rw,
                                 output uvm_reg_map_info map_info);

   /*local*/ extern function bit Xis_locked_by_fieldX();


   extern virtual function bit do_check(uvm_reg_data_t expected,
                                        uvm_reg_data_t actual,
                                        uvm_reg_map    map);

   extern virtual task do_write(uvm_reg_item rw);

   extern virtual task do_read(uvm_reg_item rw);

   extern virtual function void do_predict
                                (uvm_reg_item      rw,
                                 uvm_predict_e     kind = UVM_PREDICT_DIRECT,
                                 uvm_reg_byte_en_t be = -1);
   //-----------------
   // Group -- NODOCS -- Frontdoor
   //-----------------


   // @uvm-ieee 1800.2-2017 auto 18.4.5.2
   extern function void set_frontdoor(uvm_reg_frontdoor ftdr,
                                      uvm_reg_map       map = null,
                                      string            fname = "",
                                      int               lineno = 0);



   // @uvm-ieee 1800.2-2017 auto 18.4.5.1
   extern function uvm_reg_frontdoor get_frontdoor(uvm_reg_map map = null);


   //----------------
   // Group -- NODOCS -- Backdoor
   //----------------



   // @uvm-ieee 1800.2-2017 auto 18.4.6.2
   extern function void set_backdoor(uvm_reg_backdoor bkdr,
                                     string          fname = "",
                                     int             lineno = 0);
   
   

   // @uvm-ieee 1800.2-2017 auto 18.4.6.1
   extern function uvm_reg_backdoor get_backdoor(bit inherited = 1);



   // @uvm-ieee 1800.2-2017 auto 18.4.6.3
   extern function void clear_hdl_path (string kind = "RTL");



   // @uvm-ieee 1800.2-2017 auto 18.4.6.4
   extern function void add_hdl_path (uvm_hdl_path_slice slices[],
                                      string kind = "RTL");



   // @uvm-ieee 1800.2-2017 auto 18.4.6.5
   extern function void add_hdl_path_slice(string name,
                                           int offset,
                                           int size,
                                           bit first = 0,
                                           string kind = "RTL");



   // @uvm-ieee 1800.2-2017 auto 18.4.6.6
   extern function bit has_hdl_path (string kind = "");



   // @uvm-ieee 1800.2-2017 auto 18.4.6.7
   extern function void get_hdl_path (ref uvm_hdl_path_concat paths[$],
                                      input string kind = "");



   // @uvm-ieee 1800.2-2017 auto 18.4.6.8
   extern function void get_hdl_path_kinds (ref string kinds[$]);



   // @uvm-ieee 1800.2-2017 auto 18.4.6.9
   extern function void get_full_hdl_path (ref uvm_hdl_path_concat paths[$],
                                           input string kind = "",
                                           input string separator = ".");



   // @uvm-ieee 1800.2-2017 auto 18.4.6.10
   extern virtual task backdoor_read(uvm_reg_item rw);



   // @uvm-ieee 1800.2-2017 auto 18.4.6.11
   extern virtual task backdoor_write(uvm_reg_item rw);



   extern virtual function uvm_status_e backdoor_read_func(uvm_reg_item rw);



   // @uvm-ieee 1800.2-2017 auto 18.4.6.12
   virtual task  backdoor_watch(); endtask


   //----------------
   // Group -- NODOCS -- Coverage
   //----------------


   // @uvm-ieee 1800.2-2017 auto 18.4.7.1
   extern static function void include_coverage(string scope,
                                                uvm_reg_cvr_t models,
                                                uvm_object accessor = null);


   // @uvm-ieee 1800.2-2017 auto 18.4.7.2
   extern protected function uvm_reg_cvr_t build_coverage(uvm_reg_cvr_t models);



   // @uvm-ieee 1800.2-2017 auto 18.4.7.3
   extern virtual protected function void add_coverage(uvm_reg_cvr_t models);



   // @uvm-ieee 1800.2-2017 auto 18.4.7.4
   extern virtual function bit has_coverage(uvm_reg_cvr_t models);



   // @uvm-ieee 1800.2-2017 auto 18.4.7.6
   extern virtual function uvm_reg_cvr_t set_coverage(uvm_reg_cvr_t is_on);



   // @uvm-ieee 1800.2-2017 auto 18.4.7.5
   extern virtual function bit get_coverage(uvm_reg_cvr_t is_on);



   // @uvm-ieee 1800.2-2017 auto 18.4.7.7
   protected virtual function void sample(uvm_reg_data_t  data,
                                          uvm_reg_data_t  byte_en,
                                          bit             is_read,
                                          uvm_reg_map     map);
   endfunction


   // @uvm-ieee 1800.2-2017 auto 18.4.7.8
   virtual function void sample_values();
   endfunction

   /*local*/ function void XsampleX(uvm_reg_data_t  data,
                                    uvm_reg_data_t  byte_en,
                                    bit             is_read,
                                    uvm_reg_map     map);
      sample(data, byte_en, is_read, map);
   endfunction


   //-----------------
   // Group -- NODOCS -- Callbacks
   //-----------------
   `uvm_register_cb(uvm_reg, uvm_reg_cbs)
   


   // @uvm-ieee 1800.2-2017 auto 18.4.8.1
   virtual task pre_write(uvm_reg_item rw); endtask



   // @uvm-ieee 1800.2-2017 auto 18.4.8.2
   virtual task post_write(uvm_reg_item rw); endtask



   // @uvm-ieee 1800.2-2017 auto 18.4.8.3
   virtual task pre_read(uvm_reg_item rw); endtask



   // @uvm-ieee 1800.2-2017 auto 18.4.8.4
   virtual task post_read(uvm_reg_item rw); endtask


   extern virtual function void            do_print (uvm_printer printer);
   extern virtual function string          convert2string();
   extern virtual function uvm_object      clone      ();
   extern virtual function void            do_copy    (uvm_object rhs);
   extern virtual function bit             do_compare (uvm_object  rhs,
                                                       uvm_comparer comparer);
   extern virtual function void            do_pack    (uvm_packer packer);
   extern virtual function void            do_unpack  (uvm_packer packer);

endclass: uvm_reg


//------------------------------------------------------------------------------
// IMPLEMENTATION
//------------------------------------------------------------------------------

// new

function uvm_reg::new(string name="", int unsigned n_bits, int has_coverage);
   super.new(name);
   if (n_bits == 0) begin
      `uvm_error("RegModel", $sformatf("Register \"%s\" cannot have 0 bits", get_name()))
      n_bits = 1;
   end
   m_n_bits      = n_bits;
   m_has_cover   = has_coverage;
   m_atomic      = new(1);
   m_n_used_bits = 0;
   m_locked      = 0;
   m_is_busy     = 0;
   m_is_locked_by_field = 1'b0;
   m_hdl_paths_pool = new("hdl_paths");

   if (n_bits > m_max_size)
      m_max_size = n_bits;

endfunction: new


// configure

function void uvm_reg::configure (uvm_reg_block blk_parent,
                                  uvm_reg_file regfile_parent=null,
                                  string hdl_path = "");
   if (blk_parent == null) begin
     `uvm_error("UVM/REG/CFG/NOBLK", {"uvm_reg::configure() called without a parent block for instance \"", get_name(), "\" of register type \"", get_type_name(), "\"."})
     return;
   end

   m_parent = blk_parent;
   m_parent.add_reg(this);
   m_regfile_parent = regfile_parent;
   if (hdl_path != "")
     add_hdl_path_slice(hdl_path, -1, -1);
endfunction: configure


// add_field

function void uvm_reg::add_field(uvm_reg_field field);
   int offset;
   int idx;
   
   if (m_locked) begin
      `uvm_error("RegModel", "Cannot add field to locked register model")
      return;
   end

   if (field == null) `uvm_fatal("RegModel", "Attempting to register NULL field")

   // Store fields in LSB to MSB order
   offset = field.get_lsb_pos();

   idx = -1;
   foreach (m_fields[i]) begin
      if (offset < m_fields[i].get_lsb_pos()) begin
         int j = i;
         m_fields.insert(j, field);
         idx = i;
         break;
      end
   end
   if (idx < 0) begin
      m_fields.push_back(field);
      idx = m_fields.size()-1;
   end

   m_n_used_bits += field.get_n_bits();
   
   // Check if there are too many fields in the register
   if (m_n_used_bits > m_n_bits) begin
      `uvm_error("RegModel",
         $sformatf("Fields use more bits (%0d) than available in register \"%s\" (%0d)",
            m_n_used_bits, get_name(), m_n_bits))
   end

   // Check if there are overlapping fields
   if (idx > 0) begin
      if (m_fields[idx-1].get_lsb_pos() +
          m_fields[idx-1].get_n_bits() > offset) begin
         `uvm_error("RegModel", $sformatf("Field %s overlaps field %s in register \"%s\"",
                                        m_fields[idx-1].get_name(),
                                        field.get_name(), get_name()))
      end
   end
   if (idx < m_fields.size()-1) begin
      if (offset + field.get_n_bits() >
          m_fields[idx+1].get_lsb_pos()) begin
         `uvm_error("RegModel", $sformatf("Field %s overlaps field %s in register \"%s\"",
                                        field.get_name(),
                                        m_fields[idx+1].get_name(),
                                      get_name()))
      end
   end
endfunction: add_field


// Xlock_modelX

function void uvm_reg::Xlock_modelX();
   if (m_locked)
     return;
   m_locked = 1;
endfunction


//----------------------
// Group- User Frontdoor
//----------------------

// set_frontdoor

function void uvm_reg::set_frontdoor(uvm_reg_frontdoor ftdr,
                                     uvm_reg_map       map = null,
                                     string            fname = "",
                                     int               lineno = 0);
   uvm_reg_map_info map_info;
   ftdr.fname = m_fname;
   ftdr.lineno = m_lineno;
   map = get_local_map(map);
   if (map == null)
     return;
   map_info = map.get_reg_map_info(this);
   if (map_info == null)
      map.add_reg(this, -1, "RW", 1, ftdr);
   else begin
      map_info.frontdoor = ftdr;
   end
endfunction: set_frontdoor


// get_frontdoor

function uvm_reg_frontdoor uvm_reg::get_frontdoor(uvm_reg_map map = null);
   uvm_reg_map_info map_info;
   map = get_local_map(map);
   if (map == null)
     return null;
   map_info = map.get_reg_map_info(this);
   return map_info.frontdoor;
endfunction: get_frontdoor


// set_backdoor

function void uvm_reg::set_backdoor(uvm_reg_backdoor bkdr,
                                    string           fname = "",
                                    int              lineno = 0);
   bkdr.fname = fname;
   bkdr.lineno = lineno;
   if (m_backdoor != null &&
       m_backdoor.has_update_threads()) begin
      `uvm_warning("RegModel", "Previous register backdoor still has update threads running. Backdoors with active mirroring should only be set before simulation starts.")
   end
   m_backdoor = bkdr;
endfunction: set_backdoor


// get_backdoor

function uvm_reg_backdoor uvm_reg::get_backdoor(bit inherited = 1);

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



// clear_hdl_path

function void uvm_reg::clear_hdl_path(string kind = "RTL");
  if (kind == "ALL") begin
    m_hdl_paths_pool = new("hdl_paths");
    return;
  end

  if (kind == "") begin
     if (m_regfile_parent != null)
        kind = m_regfile_parent.get_default_hdl_path();
     else
        kind = m_parent.get_default_hdl_path();
  end

  if (!m_hdl_paths_pool.exists(kind)) begin
    `uvm_warning("RegModel",{"Unknown HDL Abstraction '",kind,"'"})
    return;
  end

  m_hdl_paths_pool.delete(kind);
endfunction


// add_hdl_path

function void uvm_reg::add_hdl_path(uvm_hdl_path_slice slices[],
                                    string kind = "RTL");
    uvm_queue #(uvm_hdl_path_concat) paths = m_hdl_paths_pool.get(kind);
    uvm_hdl_path_concat concat = new();

    concat.set(slices);
    paths.push_back(concat);
endfunction


// add_hdl_path_slice

function void uvm_reg::add_hdl_path_slice(string name,
                                          int offset,
                                          int size,
                                          bit first = 0,
                                          string kind = "RTL");
    uvm_queue #(uvm_hdl_path_concat) paths = m_hdl_paths_pool.get(kind);
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

function bit  uvm_reg::has_hdl_path(string kind = "");
  if (kind == "") begin
     if (m_regfile_parent != null)
        kind = m_regfile_parent.get_default_hdl_path();
     else
        kind = m_parent.get_default_hdl_path();
  end

  return m_hdl_paths_pool.exists(kind);
endfunction


// get_hdl_path_kinds

function void uvm_reg::get_hdl_path_kinds (ref string kinds[$]);
  string kind;
  kinds.delete();
  if (!m_hdl_paths_pool.first(kind))
    return;
  do
    kinds.push_back(kind);
  while (m_hdl_paths_pool.next(kind));
endfunction


// get_hdl_path

function void uvm_reg::get_hdl_path(ref uvm_hdl_path_concat paths[$],
                                        input string kind = "");

  uvm_queue #(uvm_hdl_path_concat) hdl_paths;

  if (kind == "") begin
     if (m_regfile_parent != null)
        kind = m_regfile_parent.get_default_hdl_path();
     else
        kind = m_parent.get_default_hdl_path();
  end

  if (!has_hdl_path(kind)) begin
    `uvm_error("RegModel",
       {"Register does not have hdl path defined for abstraction '",kind,"'"})
    return;
  end

  hdl_paths = m_hdl_paths_pool.get(kind);

  for (int i=0; i<hdl_paths.size();i++) begin
     paths.push_back(hdl_paths.get(i));
  end

endfunction


// get_full_hdl_path

function void uvm_reg::get_full_hdl_path(ref uvm_hdl_path_concat paths[$],
                                         input string kind = "",
                                         input string separator = ".");

   if (kind == "") begin
      if (m_regfile_parent != null)
         kind = m_regfile_parent.get_default_hdl_path();
      else
         kind = m_parent.get_default_hdl_path();
   end
   
   if (!has_hdl_path(kind)) begin
      `uvm_error("RegModel",
         {"Register ",get_full_name()," does not have hdl path defined for abstraction '",kind,"'"})
      return;
   end

   begin
      uvm_queue #(uvm_hdl_path_concat) hdl_paths = m_hdl_paths_pool.get(kind);
      string parent_paths[$];

      if (m_regfile_parent != null)
         m_regfile_parent.get_full_hdl_path(parent_paths, kind, separator);
      else
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


// set_offset

function void uvm_reg::set_offset (uvm_reg_map    map,
                                   uvm_reg_addr_t offset,
                                   bit unmapped = 0);

   uvm_reg_map orig_map = map;

   if (m_maps.num() > 1 && map == null) begin
      `uvm_error("RegModel",{"set_offset requires a non-null map when register '",
                 get_full_name(),"' belongs to more than one map."})
      return;
   end

   map = get_local_map(map);

   if (map == null)
     return;
   
   map.m_set_reg_offset(this, offset, unmapped);
endfunction


// set_parent

function void uvm_reg::set_parent(uvm_reg_block blk_parent,
                                      uvm_reg_file regfile_parent);
  if (m_parent != null) begin
     // ToDo: remove register from previous parent
  end
  m_parent = blk_parent;
  m_regfile_parent = regfile_parent;
endfunction


// get_parent

function uvm_reg_block uvm_reg::get_parent();
  return get_block();
endfunction


// get_regfile

function uvm_reg_file uvm_reg::get_regfile();
   return m_regfile_parent;
endfunction


// get_full_name

function string uvm_reg::get_full_name();

   if (m_regfile_parent != null)
      return {m_regfile_parent.get_full_name(), ".", get_name()};

   if (m_parent != null)
      return {m_parent.get_full_name(), ".", get_name()};
   
   return get_name();
endfunction: get_full_name


// add_map

function void uvm_reg::add_map(uvm_reg_map map);
  m_maps[map] = 1;
endfunction


// get_maps

function void uvm_reg::get_maps(ref uvm_reg_map maps[$]);
   foreach (m_maps[map])
     maps.push_back(map);
endfunction


// get_n_maps

function int uvm_reg::get_n_maps();
   return m_maps.num();
endfunction


// is_in_map

function bit uvm_reg::is_in_map(uvm_reg_map map);
   if (m_maps.exists(map))
     return 1;
   foreach (m_maps[l]) begin
     uvm_reg_map local_map = l;
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

function uvm_reg_map uvm_reg::get_local_map(uvm_reg_map map);
   if (map == null)
     return get_default_map();
   if (m_maps.exists(map))
     return map; 
   foreach (m_maps[l]) begin
     uvm_reg_map local_map=l;
     uvm_reg_map parent_map = local_map.get_parent_map();

     while (parent_map != null) begin
       if (parent_map == map)
         return local_map;
       parent_map = parent_map.get_parent_map();
     end
   end
   `uvm_warning("RegModel", 
       {"Register '",get_full_name(),"' is not contained within map '",map.get_full_name(),"'"})
   return null;
endfunction



// get_default_map

function uvm_reg_map uvm_reg::get_default_map();

   // if reg is not associated with any map, return ~null~
   if (m_maps.num() == 0) begin
      `uvm_warning("RegModel", 
        {"Register '",get_full_name(),"' is not registered with any map"})
      return null;
   end

   // if only one map, choose that
   if (m_maps.num() == 1) begin
     uvm_reg_map map;
     void'(m_maps.first(map));
     return map;
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

   // if that fails, choose the first in this reg's maps

   begin
     uvm_reg_map map;
     void'(m_maps.first(map));
     return map;
   end

endfunction


// get_rights

function string uvm_reg::get_rights(uvm_reg_map map = null);

   uvm_reg_map_info info;

   map = get_local_map(map);

   if (map == null)
     return "RW";

   info = map.get_reg_map_info(this);
   return info.rights;

endfunction



// get_block

function uvm_reg_block uvm_reg::get_block();
   get_block = m_parent;
endfunction


// get_offset

function uvm_reg_addr_t uvm_reg::get_offset(uvm_reg_map map = null);

   uvm_reg_map_info map_info;
   uvm_reg_map orig_map = map;

   map = get_local_map(map);

   if (map == null)
     return -1;
   
   map_info = map.get_reg_map_info(this);
   
   if (map_info.unmapped) begin
      `uvm_warning("RegModel", {"Register '",get_name(),
                   "' is unmapped in map '",
                   ((orig_map == null) ? map.get_full_name() : orig_map.get_full_name()),"'"})
      return -1;
   end
         
   return map_info.offset;

endfunction


// get_addresses

function int uvm_reg::get_addresses(uvm_reg_map map=null, ref uvm_reg_addr_t addr[]);

   uvm_reg_map_info map_info;
   uvm_reg_map orig_map = map;

   map = get_local_map(map);

   if (map == null)
     return -1;

   map_info = map.get_reg_map_info(this);

   if (map_info.unmapped) begin
      `uvm_warning("RegModel", {"Register '",get_name(),
                   "' is unmapped in map '",
                   ((orig_map == null) ? map.get_full_name() : orig_map.get_full_name()),"'"})
      return -1;
   end
 
   addr = map_info.addr;
   return map.get_n_bytes();

endfunction


// get_address

function uvm_reg_addr_t uvm_reg::get_address(uvm_reg_map map = null);
   uvm_reg_addr_t  addr[];
   void'(get_addresses(map,addr));
   return addr[0];
endfunction


// get_n_bits

function int unsigned uvm_reg::get_n_bits();
   return m_n_bits;
endfunction


// get_n_bytes

function int unsigned uvm_reg::get_n_bytes();
   return ((m_n_bits-1) / 8) + 1;
endfunction


// get_max_size

function int unsigned uvm_reg::get_max_size();
   return m_max_size;
endfunction: get_max_size


// get_fields

function void uvm_reg::get_fields(ref uvm_reg_field fields[$]);
   foreach(m_fields[i])
      fields.push_back(m_fields[i]);
endfunction


// get_field_by_name

function uvm_reg_field uvm_reg::get_field_by_name(string name);
   foreach (m_fields[i])
      if (m_fields[i].get_name() == name)
         return m_fields[i];
   `uvm_warning("RegModel", {"Unable to locate field '",name,
                            "' in register '",get_name(),"'"})
   return null;
endfunction


// Xget_field_accessX
//
// Returns "WO" if all of the fields in the registers are write-only
// Returns "RO" if all of the fields in the registers are read-only
// Returns "RW" otherwise.

function string uvm_reg::Xget_fields_accessX(uvm_reg_map map);
   bit is_R;
   bit is_W;
   
   foreach(m_fields[i]) begin
      case (m_fields[i].get_access(map))
       "RO",
         "RC",
         "RS":
            is_R = 1;
       
       "WO",
          "WOC",
          "WOS",
          "WO1":
             is_W = 1;
       
       default:
          return "RW";
      endcase
      
      if (is_R && is_W) return "RW";
   end

   case ({is_R, is_W})
    2'b01: return "WO";
    2'b10: return "RO";
   endcase
   return "RW";
endfunction

      
//---------
// COVERAGE
//---------


// include_coverage

function void uvm_reg::include_coverage(string scope,
                                        uvm_reg_cvr_t models,
                                        uvm_object accessor = null);
   uvm_reg_cvr_rsrc_db::set({"uvm_reg::", scope},
                            "include_coverage",
                            models, accessor);
endfunction


// build_coverage

function uvm_reg_cvr_t uvm_reg::build_coverage(uvm_reg_cvr_t models);
   build_coverage = UVM_NO_COVERAGE;
   void'(uvm_reg_cvr_rsrc_db::read_by_name({"uvm_reg::", get_full_name()},
                                           "include_coverage",
                                           build_coverage, this));
   return build_coverage & models;
endfunction: build_coverage


// add_coverage

function void uvm_reg::add_coverage(uvm_reg_cvr_t models);
   m_has_cover |= models;
endfunction: add_coverage


// has_coverage

function bit uvm_reg::has_coverage(uvm_reg_cvr_t models);
   return ((m_has_cover & models) == models);
endfunction: has_coverage


// set_coverage

function uvm_reg_cvr_t uvm_reg::set_coverage(uvm_reg_cvr_t is_on);
   if (is_on == uvm_reg_cvr_t'(UVM_NO_COVERAGE)) begin
      m_cover_on = is_on;
      return m_cover_on;
   end

   m_cover_on = m_has_cover & is_on;

   return m_cover_on;
endfunction: set_coverage


// get_coverage

function bit uvm_reg::get_coverage(uvm_reg_cvr_t is_on);
   if (has_coverage(is_on) == 0)
      return 0;
   return ((m_cover_on & is_on) == is_on);
endfunction: get_coverage



//---------
// ACCESS
//---------


// set

function void uvm_reg::set(uvm_reg_data_t  value,
                           string          fname = "",
                           int             lineno = 0);
   // Split the value into the individual fields
   m_fname = fname;
   m_lineno = lineno;

   foreach (m_fields[i])
      m_fields[i].set((value >> m_fields[i].get_lsb_pos()) &
                       ((1 << m_fields[i].get_n_bits()) - 1));
endfunction: set


// predict

function bit uvm_reg::predict (uvm_reg_data_t    value,
                               uvm_reg_byte_en_t be = -1,
                               uvm_predict_e     kind = UVM_PREDICT_DIRECT,
                               uvm_door_e        path = UVM_FRONTDOOR,
                               uvm_reg_map       map = null,
                               string            fname = "",
                               int               lineno = 0);
  uvm_reg_item rw = new;
  rw.value[0] = value;
  rw.path = path;
  rw.map = map;
  rw.fname = fname;
  rw.lineno = lineno;
  do_predict(rw, kind, be);
  predict = (rw.status == UVM_NOT_OK) ? 0 : 1;
endfunction: predict


// do_predict

function void uvm_reg::do_predict(uvm_reg_item      rw,
                                  uvm_predict_e     kind = UVM_PREDICT_DIRECT,
                                  uvm_reg_byte_en_t be = -1);

   uvm_reg_data_t reg_value = rw.value[0];
   m_fname = rw.fname;
   m_lineno = rw.lineno;
   
if (rw.status ==UVM_IS_OK )
   rw.status = UVM_IS_OK;

   if (m_is_busy && kind == UVM_PREDICT_DIRECT) begin
      `uvm_warning("RegModel", {"Trying to predict value of register '",
                  get_full_name(),"' while it is being accessed"})
      rw.status = UVM_NOT_OK;
      return;
   end
   
   foreach (m_fields[i]) begin
      rw.value[0] = (reg_value >> m_fields[i].get_lsb_pos()) &
                                 ((1 << m_fields[i].get_n_bits())-1);
      m_fields[i].do_predict(rw, kind, be>>(m_fields[i].get_lsb_pos()/8));
   end

   rw.value[0] = reg_value;

endfunction: do_predict


// get

function uvm_reg_data_t  uvm_reg::get(string  fname = "",
                                      int     lineno = 0);
   // Concatenate the value of the individual fields
   // to form the register value
   m_fname = fname;
   m_lineno = lineno;

   get = 0;
   
   foreach (m_fields[i])
      get |= m_fields[i].get() << m_fields[i].get_lsb_pos();
endfunction: get


// get_mirrored_value

function uvm_reg_data_t  uvm_reg::get_mirrored_value(string  fname = "",
                                      int     lineno = 0);
   // Concatenate the value of the individual fields
   // to form the register value
   m_fname = fname;
   m_lineno = lineno;

   get_mirrored_value = 0;
   
   foreach (m_fields[i])
      get_mirrored_value |= m_fields[i].get_mirrored_value() << m_fields[i].get_lsb_pos();
endfunction: get_mirrored_value


// reset

function void uvm_reg::reset(string kind = "HARD");
   foreach (m_fields[i])
      m_fields[i].reset(kind);
   // Put back a key in the semaphore if it is checked out
   // in case a thread was killed during an operation
   void'(m_atomic.try_get(1));
   m_atomic.put(1);
   m_process = null;
   Xset_busyX(0);
endfunction: reset


// get_reset

function uvm_reg_data_t uvm_reg::get_reset(string kind = "HARD");
   // Concatenate the value of the individual fields
   // to form the register value
   get_reset = 0;
   
   foreach (m_fields[i])
      get_reset |= m_fields[i].get_reset(kind) << m_fields[i].get_lsb_pos();
endfunction: get_reset


// has_reset

function bit uvm_reg::has_reset(string kind = "HARD",
                                bit    delete = 0);

   has_reset = 0;
   foreach (m_fields[i]) begin
      has_reset |= m_fields[i].has_reset(kind, delete);
      if (!delete && has_reset)
        return 1;
   end
endfunction: has_reset


// set_reset

function void uvm_reg::set_reset(uvm_reg_data_t value,
                                 string         kind = "HARD");
   foreach (m_fields[i]) begin
      m_fields[i].set_reset(value >> m_fields[i].get_lsb_pos(), kind);
   end
endfunction: set_reset


//-----------
// BUS ACCESS
//-----------

// needs_update

function bit uvm_reg::needs_update();
   needs_update = 0;
   foreach (m_fields[i]) begin
      if (m_fields[i].needs_update()) begin
         return 1;
      end
   end
endfunction: needs_update


// update

task uvm_reg::update(output uvm_status_e      status,
                     input  uvm_door_e        path = UVM_DEFAULT_DOOR,
                     input  uvm_reg_map       map = null,
                     input  uvm_sequence_base parent = null,
                     input  int               prior = -1,
                     input  uvm_object        extension = null,
                     input  string            fname = "",
                     input  int               lineno = 0);
   uvm_reg_data_t upd;

   status = UVM_IS_OK;

   if (!needs_update()) return;

   // Concatenate the write-to-update values from each field
   // Fields are stored in LSB or MSB order
   upd = 0;
   foreach (m_fields[i])
      upd |= m_fields[i].XupdateX() << m_fields[i].get_lsb_pos();

   write(status, upd, path, map, parent, prior, extension, fname, lineno);
endtask: update



// write

task uvm_reg::write(output uvm_status_e      status,
                    input  uvm_reg_data_t    value,
                    input  uvm_door_e        path = UVM_DEFAULT_DOOR,
                    input  uvm_reg_map       map = null,
                    input  uvm_sequence_base parent = null,
                    input  int               prior = -1,
                    input  uvm_object        extension = null,
                    input  string            fname = "",
                    input  int               lineno = 0);

   // create an abstract transaction for this operation
   uvm_reg_item rw;

   XatomicX(1);

   set(value);

   rw = uvm_reg_item::type_id::create("write_item",,get_full_name());
   rw.element      = this;
   rw.element_kind = UVM_REG;
   rw.kind         = UVM_WRITE;
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

   XatomicX(0);

endtask


// do_write

task uvm_reg::do_write (uvm_reg_item rw);

   uvm_reg_cb_iter  cbs = new(this);
   uvm_reg_map_info map_info;
   uvm_reg_data_t   value; 

   m_fname  = rw.fname;
   m_lineno = rw.lineno;

   if (!Xcheck_accessX(rw,map_info))
     return;

   XatomicX(1);

   m_write_in_progress = 1'b1;

   rw.value[0] &= ((1 << m_n_bits)-1);
   value = rw.value[0];

   rw.status = UVM_IS_OK;

   // PRE-WRITE CBS - FIELDS
   begin : pre_write_callbacks
      uvm_reg_data_t  msk;
      int lsb;

      foreach (m_fields[i]) begin
         uvm_reg_field_cb_iter cbs = new(m_fields[i]);
         uvm_reg_field f = m_fields[i];
         lsb = f.get_lsb_pos();
         msk = ((1<<f.get_n_bits())-1) << lsb;
         rw.value[0] = (value & msk) >> lsb;
         f.pre_write(rw);
         for (uvm_reg_cbs cb=cbs.first(); cb!=null; cb=cbs.next()) begin
            rw.element = f;
            rw.element_kind = UVM_FIELD;
            cb.pre_write(rw);
         end

         value = (value & ~msk) | (rw.value[0] << lsb);
      end
   end
   rw.element = this;
   rw.element_kind = UVM_REG;
   rw.value[0] = value;

   // PRE-WRITE CBS - REG
   pre_write(rw);
   for (uvm_reg_cbs cb=cbs.first(); cb!=null; cb=cbs.next())
      cb.pre_write(rw);

   if (rw.status != UVM_IS_OK) begin
     m_write_in_progress = 1'b0;

     XatomicX(0);
         
     return;
   end
         
   // EXECUTE WRITE...
   case (rw.path)
      
      // ...VIA USER BACKDOOR
      UVM_BACKDOOR: begin
         uvm_reg_data_t final_val;
         uvm_reg_backdoor bkdr = get_backdoor();
  
         if (rw.map != null)
           rw.local_map = rw.map;
         else 
           rw.local_map = get_default_map();

         value = rw.value[0];

         // Mimick the final value after a physical read
         rw.kind = UVM_READ;
         if (bkdr != null)
           bkdr.read(rw);
         else
           backdoor_read(rw);

         if (rw.status == UVM_NOT_OK) begin
           m_write_in_progress = 1'b0;
           return;
         end

         begin
            foreach (m_fields[i]) begin
               uvm_reg_data_t field_val;
               int lsb = m_fields[i].get_lsb_pos();
               int sz  = m_fields[i].get_n_bits();
               field_val = m_fields[i].XpredictX((rw.value[0] >> lsb) & ((1<<sz)-1),
                                                 (value >> lsb) & ((1<<sz)-1),
                                                 rw.local_map);
               final_val |= field_val << lsb;
            end
         end
         rw.kind = UVM_WRITE;
         rw.value[0] = final_val;

        if (get_rights(rw.local_map) inside {"RW", "WO"}) begin
          if (bkdr != null)
           bkdr.write(rw);
          else
           backdoor_write(rw);

          do_predict(rw, UVM_PREDICT_WRITE);
        end
        else begin
           rw.status = UVM_NOT_OK;
        end
        
      
      end

      UVM_FRONTDOOR: begin

         uvm_reg_map system_map = rw.local_map.get_root_map();

         m_is_busy = 1;

         // ...VIA USER FRONTDOOR
         if (map_info.frontdoor != null) begin
            uvm_reg_frontdoor fd = map_info.frontdoor;
            fd.rw_info = rw;
            if (fd.sequencer == null)
              fd.sequencer = system_map.get_sequencer();
            fd.start(fd.sequencer, rw.parent);
         end

         // ...VIA BUILT-IN FRONTDOOR
         else begin : built_in_frontdoor

            rw.local_map.do_write(rw);

         end

         m_is_busy = 0;

         if (system_map.get_auto_predict()) begin
            uvm_status_e status;
            if (rw.status != UVM_NOT_OK) begin
               sample(value, -1, 0, rw.map);
               m_parent.XsampleX(map_info.offset, 0, rw.map);
            end

            status = rw.status; // do_predict will override rw.status, so we save it here
            do_predict(rw, UVM_PREDICT_WRITE);
            rw.status = status;
         end
      end
      
   endcase

   value = rw.value[0];

   // POST-WRITE CBS - REG
   for (uvm_reg_cbs cb=cbs.first(); cb!=null; cb=cbs.next())
      cb.post_write(rw);
   post_write(rw);

   // POST-WRITE CBS - FIELDS
   foreach (m_fields[i]) begin
      uvm_reg_field_cb_iter cbs = new(m_fields[i]);
      uvm_reg_field f = m_fields[i];
      
      rw.element = f;
      rw.element_kind = UVM_FIELD;
      rw.value[0] = (value >> f.get_lsb_pos()) & ((1<<f.get_n_bits())-1);
      
      for (uvm_reg_cbs cb=cbs.first(); cb!=null; cb=cbs.next())
         cb.post_write(rw);
      f.post_write(rw);
   end
   
   rw.value[0] = value;
   rw.element = this;
   rw.element_kind = UVM_REG;

   // REPORT
   if (uvm_report_enabled(UVM_HIGH, UVM_INFO, "RegModel")) begin
     string path_s,value_s;
     if (rw.path == UVM_FRONTDOOR)
       path_s = (map_info.frontdoor != null) ? "user frontdoor" :
                                               {"map ",rw.map.get_full_name()};
     else
       path_s = (get_backdoor() != null) ? "user backdoor" : "DPI backdoor";

     value_s = $sformatf("=0x%0h",rw.value[0]);

      uvm_report_info("RegModel", {"Wrote register via ",path_s,": ",
                                   get_full_name(),value_s}, UVM_HIGH);
   end

   m_write_in_progress = 1'b0;

   XatomicX(0);

endtask: do_write

// read

task uvm_reg::read(output uvm_status_e      status,
                   output uvm_reg_data_t    value,
                   input  uvm_door_e        path = UVM_DEFAULT_DOOR,
                   input  uvm_reg_map       map = null,
                   input  uvm_sequence_base parent = null,
                   input  int               prior = -1,
                   input  uvm_object        extension = null,
                   input  string            fname = "",
                   input  int               lineno = 0);
   XatomicX(1);
   XreadX(status, value, path, map, parent, prior, extension, fname, lineno);
   XatomicX(0);
endtask: read


// XreadX

task uvm_reg::XreadX(output uvm_status_e      status,
                     output uvm_reg_data_t    value,
                     input  uvm_door_e        path,
                     input  uvm_reg_map       map,
                     input  uvm_sequence_base parent = null,
                     input  int               prior = -1,
                     input  uvm_object        extension = null,
                     input  string            fname = "",
                     input  int               lineno = 0);
   
   // create an abstract transaction for this operation
   uvm_reg_item rw;
   rw = uvm_reg_item::type_id::create("read_item",,get_full_name());
   rw.element      = this;
   rw.element_kind = UVM_REG;
   rw.kind         = UVM_READ;
   rw.value[0]     = 0;
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

endtask: XreadX


// do_read

task uvm_reg::do_read(uvm_reg_item rw);

   uvm_reg_cb_iter  cbs = new(this);
   uvm_reg_map_info map_info;
   uvm_reg_data_t   value;
   uvm_reg_data_t   exp;

   m_fname   = rw.fname;
   m_lineno  = rw.lineno;
   
   if (!Xcheck_accessX(rw,map_info))
     return;

   m_read_in_progress = 1'b1;

   rw.status = UVM_IS_OK;

   // PRE-READ CBS - FIELDS
   foreach (m_fields[i]) begin
      uvm_reg_field_cb_iter cbs = new(m_fields[i]);
      uvm_reg_field f = m_fields[i];
      rw.element = f;
      rw.element_kind = UVM_FIELD;
      m_fields[i].pre_read(rw);
      for (uvm_reg_cbs cb=cbs.first(); cb!=null; cb=cbs.next())
         cb.pre_read(rw);
   end

   rw.element = this;
   rw.element_kind = UVM_REG;

   // PRE-READ CBS - REG
   pre_read(rw);
   for (uvm_reg_cbs cb=cbs.first(); cb!=null; cb=cbs.next())
      cb.pre_read(rw);

   if (rw.status != UVM_IS_OK) begin
     m_read_in_progress = 1'b0;

     return;
   end
         
   // EXECUTE READ...
   case (rw.path)
      
      // ...VIA USER BACKDOOR
      UVM_BACKDOOR: begin
         uvm_reg_backdoor bkdr = get_backdoor();

         uvm_reg_map map;  // = uvm_reg_map::backdoor();
         if (rw.map != null)
            rw.local_map = rw.map;
         else
            rw.local_map = get_default_map();  
         
         map = rw.local_map;
          
         if (map.get_check_on_read()) exp = get();
   
         if (get_rights(rw.local_map) inside {"RW", "RO"}) begin
           if (bkdr != null)
             bkdr.read(rw);
           else
             backdoor_read(rw);
         end
         else begin
             rw.status = UVM_NOT_OK;
         end
         
         value = rw.value[0];

         // Need to clear RC fields, set RS fields and mask WO fields
         if (rw.status != UVM_NOT_OK) begin

            uvm_reg_data_t wo_mask;

            foreach (m_fields[i]) begin
              // string acc = m_fields[i].get_access(uvm_reg_map::backdoor());
               string acc = m_fields[i].get_access(rw.local_map);
               if (acc == "RC" ||
                   acc == "WRC" ||
                   acc == "WSRC" ||
                   acc == "W1SRC" ||
                   acc == "W0SRC") begin
                  value &= ~(((1<<m_fields[i].get_n_bits())-1)
                                          << m_fields[i].get_lsb_pos());
               end
               else if (acc == "RS" ||
                        acc == "WRS" ||
                        acc == "WCRS" ||
                        acc == "W1CRS" ||
                        acc == "W0CRS") begin
                  value |= (((1<<m_fields[i].get_n_bits())-1)
                                          << m_fields[i].get_lsb_pos());
               end
               else if (acc == "WO" ||
                        acc == "WOC" ||
                        acc == "WOS" ||
                        acc == "WO1") begin
                  wo_mask |= ((1<<m_fields[i].get_n_bits())-1)
                                          << m_fields[i].get_lsb_pos();
               end
            end

           if (get_rights(rw.local_map) inside {"RW", "RO"}) begin

            if (value != rw.value[0]) begin
              uvm_reg_data_t saved;
              saved = rw.value[0];
              rw.value[0] = value;
              if (bkdr != null)
                 bkdr.write(rw);
              else
                 backdoor_write(rw);
              rw.value[0] = saved;
            end

            rw.value[0] &= ~wo_mask;

            if (map.get_check_on_read() &&
               rw.status != UVM_NOT_OK) begin
               void'(do_check(exp, rw.value[0], map));
            end
       
            do_predict(rw, UVM_PREDICT_READ);
           end
           else begin
              rw.status = UVM_NOT_OK;
           end
        
         end
      end


      UVM_FRONTDOOR: begin

         uvm_reg_map system_map = rw.local_map.get_root_map();

         m_is_busy = 1;

         if (rw.local_map.get_check_on_read()) exp = get();
   
         // ...VIA USER FRONTDOOR
         if (map_info.frontdoor != null) begin
            uvm_reg_frontdoor fd = map_info.frontdoor;
            fd.rw_info = rw;
            if (fd.sequencer == null)
              fd.sequencer = system_map.get_sequencer();
            fd.start(fd.sequencer, rw.parent);
         end

         // ...VIA BUILT-IN FRONTDOOR
         else begin
            rw.local_map.do_read(rw);
         end

         m_is_busy = 0;

         if (system_map.get_auto_predict()) begin
            uvm_status_e status;
            if (rw.local_map.get_check_on_read() &&
                rw.status != UVM_NOT_OK) begin
               void'(do_check(exp, rw.value[0], system_map));
            end

            if (rw.status != UVM_NOT_OK) begin
               sample(rw.value[0], -1, 1, rw.map);
               m_parent.XsampleX(map_info.offset, 1, rw.map);
            end

            status = rw.status; // do_predict will override rw.status, so we save it here
            do_predict(rw, UVM_PREDICT_READ);
            rw.status = status;
         end
      end
      
   endcase

   value = rw.value[0]; // preserve 

   // POST-READ CBS - REG
   for (uvm_reg_cbs cb = cbs.first(); cb != null; cb = cbs.next())
      cb.post_read(rw);
   post_read(rw);

   // POST-READ CBS - FIELDS
   foreach (m_fields[i]) begin
      uvm_reg_field_cb_iter cbs = new(m_fields[i]);
      uvm_reg_field f = m_fields[i];

      rw.element = f;
      rw.element_kind = UVM_FIELD;
      rw.value[0] = (value >> f.get_lsb_pos()) & ((1<<f.get_n_bits())-1);

      for (uvm_reg_cbs cb=cbs.first(); cb!=null; cb=cbs.next())
         cb.post_read(rw);
      f.post_read(rw);
   end

   rw.value[0] = value; // restore
   rw.element = this;
   rw.element_kind = UVM_REG;

   // REPORT
   if (uvm_report_enabled(UVM_HIGH, UVM_INFO, "RegModel")) begin
     string path_s,value_s;
     if (rw.path == UVM_FRONTDOOR)
       path_s = (map_info.frontdoor != null) ? "user frontdoor" :
                                               {"map ",rw.map.get_full_name()};
     else
       path_s = (get_backdoor() != null) ? "user backdoor" : "DPI backdoor";

     value_s = $sformatf("=%0h",rw.value[0]);

      uvm_report_info("RegModel", {"Read  register via ",path_s,": ",
                                   get_full_name(),value_s}, UVM_HIGH);
   end

   m_read_in_progress = 1'b0;

endtask: do_read


// Xcheck_accessX

function bit uvm_reg::Xcheck_accessX (input uvm_reg_item rw,
                                      output uvm_reg_map_info map_info);


   if (rw.path == UVM_DEFAULT_DOOR)
     rw.path = m_parent.get_default_door();

   if (rw.path == UVM_BACKDOOR) begin
      if (get_backdoor() == null && !has_hdl_path()) begin
         `uvm_warning("RegModel",
            {"No backdoor access available for register '",get_full_name(),
            "' . Using frontdoor instead."})
         rw.path = UVM_FRONTDOOR;
      end
      else if (rw.map == null) begin
        uvm_reg_map  bkdr_map = get_default_map();
        if (bkdr_map != null)
            rw.map = bkdr_map;
        else
            rw.map = uvm_reg_map::backdoor();
      end
      
   end


   if (rw.path != UVM_BACKDOOR) begin

     rw.local_map = get_local_map(rw.map);

     if (rw.local_map == null) begin
        `uvm_error(get_type_name(), 
           {"No transactor available to physically access register on map '",
            rw.map.get_full_name(),"'"})
        rw.status = UVM_NOT_OK;
        return 0;
     end

     map_info = rw.local_map.get_reg_map_info(this);

     if (map_info.frontdoor == null && map_info.unmapped) begin
          `uvm_error("RegModel", {"Register '",get_full_name(),
             "' unmapped in map '",
             (rw.map==null)? rw.local_map.get_full_name():rw.map.get_full_name(),
             "' and does not have a user-defined frontdoor"})
          rw.status = UVM_NOT_OK;
          return 0;
     end

     if (rw.map == null)
       rw.map = rw.local_map;
   end
   return 1;
endfunction


// is_busy

function bit uvm_reg::is_busy();
   return m_is_busy;
endfunction
    

// Xset_busyX

function void uvm_reg::Xset_busyX(bit busy);
   m_is_busy = busy;
endfunction
    

// Xis_loacked_by_fieldX

function bit uvm_reg::Xis_locked_by_fieldX();
  return m_is_locked_by_field;
endfunction
    

// backdoor_write

task  uvm_reg::backdoor_write(uvm_reg_item rw);
  uvm_hdl_path_concat paths[$];
  bit ok=1;
  get_full_hdl_path(paths,rw.bd_kind);
  foreach (paths[i]) begin
     uvm_hdl_path_concat hdl_concat = paths[i];
     foreach (hdl_concat.slices[j]) begin
        `uvm_info("RegMem", $sformatf("backdoor_write to %s",
                  hdl_concat.slices[j].path),UVM_DEBUG)

        if (hdl_concat.slices[j].offset < 0) begin
           ok &= uvm_hdl_deposit(hdl_concat.slices[j].path,rw.value[0]);
           continue;
        end
        begin
           uvm_reg_data_t slice;
           slice = rw.value[0] >> hdl_concat.slices[j].offset;
           slice &= (1 << hdl_concat.slices[j].size)-1;
           ok &= uvm_hdl_deposit(hdl_concat.slices[j].path, slice);
        end
     end
  end
  rw.status = (ok ? UVM_IS_OK : UVM_NOT_OK);
endtask


// backdoor_read

task  uvm_reg::backdoor_read (uvm_reg_item rw);
  rw.status = backdoor_read_func(rw);
endtask


// backdoor_read_func

function uvm_status_e uvm_reg::backdoor_read_func(uvm_reg_item rw);
  uvm_hdl_path_concat paths[$];
  uvm_reg_data_t val;
  bit ok=1;
  get_full_hdl_path(paths,rw.bd_kind);
  foreach (paths[i]) begin
     uvm_hdl_path_concat hdl_concat = paths[i];
     val = 0;
     foreach (hdl_concat.slices[j]) begin
        `uvm_info("RegMem", $sformatf("backdoor_read from %s ",
               hdl_concat.slices[j].path),UVM_DEBUG)

        if (hdl_concat.slices[j].offset < 0) begin
           ok &= uvm_hdl_read(hdl_concat.slices[j].path,val);
           continue;
        end
        begin
           uvm_reg_data_t slice;
           int k = hdl_concat.slices[j].offset;
           
           ok &= uvm_hdl_read(hdl_concat.slices[j].path, slice);
      
           repeat (hdl_concat.slices[j].size) begin
              val[k++] = slice[0];
              slice >>= 1;
           end
        end
     end

     val &= (1 << m_n_bits)-1;

     if (i == 0)
        rw.value[0] = val;

     if (val != rw.value[0]) begin
        `uvm_error("RegModel", $sformatf("Backdoor read of register %s with multiple HDL copies: values are not the same: %0h at path '%s', and %0h at path '%s'. Returning first value.",
               get_full_name(),
               rw.value[0], uvm_hdl_concat2string(paths[0]),
               val, uvm_hdl_concat2string(paths[i])))
        return UVM_NOT_OK;
      end
      `uvm_info("RegMem", 
         $sformatf("returned backdoor value 0x%0x",rw.value[0]),UVM_DEBUG)
      
  end

  rw.status = (ok) ? UVM_IS_OK : UVM_NOT_OK;
  return rw.status;
endfunction


// poke

task uvm_reg::poke(output uvm_status_e      status,
                   input  uvm_reg_data_t    value,
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
      `uvm_error("RegModel",
        {"No backdoor access available to poke register '",get_full_name(),"'"})
      status = UVM_NOT_OK;
      return;
   end

   if (!m_is_locked_by_field)
     XatomicX(1);

   // create an abstract transaction for this operation
   rw = uvm_reg_item::type_id::create("reg_poke_item",,get_full_name());
   rw.element      = this;
   rw.path         = UVM_BACKDOOR;
   rw.element_kind = UVM_REG;
   rw.kind         = UVM_WRITE;
   rw.bd_kind      = kind;
   rw.value[0]     = value & ((1 << m_n_bits)-1);
   rw.parent       = parent;
   rw.extension    = extension;
   rw.fname        = fname;
   rw.lineno       = lineno;

   if (bkdr != null)
     bkdr.write(rw);
   else
     backdoor_write(rw);

   status = rw.status;

   `uvm_info("RegModel", $sformatf("Poked register \"%s\": 'h%h",
                              get_full_name(), value),UVM_HIGH)

   do_predict(rw, UVM_PREDICT_WRITE);

   if (!m_is_locked_by_field)
     XatomicX(0);
endtask: poke


// peek

task uvm_reg::peek(output uvm_status_e      status,
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
      `uvm_error("RegModel",
        $sformatf("No backdoor access available to peek register \"%s\"",
                  get_full_name()))
      status = UVM_NOT_OK;
      return;
   end

   if(!m_is_locked_by_field)
      XatomicX(1);

   // create an abstract transaction for this operation
   rw = uvm_reg_item::type_id::create("mem_peek_item",,get_full_name());
   rw.element      = this;
   rw.path         = UVM_BACKDOOR;
   rw.element_kind = UVM_REG;
   rw.kind         = UVM_READ;
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
   value = rw.value[0];

   `uvm_info("RegModel", $sformatf("Peeked register \"%s\": 'h%h",
                          get_full_name(), value),UVM_HIGH)

   do_predict(rw, UVM_PREDICT_READ);

   if (!m_is_locked_by_field)
      XatomicX(0);
endtask: peek


// do_check
function bit uvm_reg::do_check(input uvm_reg_data_t expected,
                               input uvm_reg_data_t actual,
                               uvm_reg_map          map);

   uvm_reg_data_t  valid_bits_mask = 0; // elements 1 indicating bit we care about

   foreach(m_fields[i]) begin
      string acc = m_fields[i].get_access(map);
      acc = acc.substr(0, 1);
      if (!(m_fields[i].get_compare() == UVM_NO_CHECK ||acc == "WO")) begin
         valid_bits_mask |= ((1 << m_fields[i].get_n_bits())-1)<< m_fields[i].get_lsb_pos();
      end
   end

   if ((actual&valid_bits_mask) === (expected&valid_bits_mask)) return 1;
   
   `uvm_error("RegModel", $sformatf("Register \"%s\" value read from DUT (0x%h) does not match mirrored value (0x%h) (valid bit mask = 0x%h)",
                                    get_full_name(), actual, expected,valid_bits_mask))
                                     
   foreach(m_fields[i]) begin
      string acc = m_fields[i].get_access(map);
      acc = acc.substr(0, 1);
      if (!(m_fields[i].get_compare() == UVM_NO_CHECK ||
            acc == "WO")) begin
         uvm_reg_data_t mask  = ((1 << m_fields[i].get_n_bits())-1);
         uvm_reg_data_t val   = actual   >> m_fields[i].get_lsb_pos() & mask;
         uvm_reg_data_t exp   = expected >> m_fields[i].get_lsb_pos() & mask;

         if (val !== exp) begin
            `uvm_info("RegModel",
                      $sformatf("Field %s (%s[%0d:%0d]) mismatch read=%0d'h%0h mirrored=%0d'h%0h ",
                                m_fields[i].get_name(), get_full_name(),
                                m_fields[i].get_lsb_pos() + m_fields[i].get_n_bits() - 1,
                                m_fields[i].get_lsb_pos(),
                                m_fields[i].get_n_bits(), val,
                                m_fields[i].get_n_bits(), exp),
                      UVM_NONE)
         end
      end
   end

   return 0;
endfunction
       

// mirror

task uvm_reg::mirror(output uvm_status_e       status,
                     input  uvm_check_e        check = UVM_NO_CHECK,
                     input  uvm_door_e         path = UVM_DEFAULT_DOOR,
                     input  uvm_reg_map        map = null,
                     input  uvm_sequence_base  parent = null,
                     input  int                prior = -1,
                     input  uvm_object         extension = null,
                     input  string             fname = "",
                     input  int                lineno = 0);
   uvm_reg_data_t  v;
   uvm_reg_data_t  exp;
   uvm_reg_backdoor bkdr = get_backdoor();

   XatomicX(1);
   m_fname = fname;
   m_lineno = lineno;


   if (path == UVM_DEFAULT_DOOR)
     path = m_parent.get_default_door();

   if (path == UVM_BACKDOOR && (bkdr != null || has_hdl_path()))
     map = uvm_reg_map::backdoor();
   else
     map = get_local_map(map);

   if (map == null)
     return;
   
   // Remember what we think the value is before it gets updated
   if (check == UVM_CHECK)
     exp = get_mirrored_value();

   XreadX(status, v, path, map, parent, prior, extension, fname, lineno);

   if (status == UVM_NOT_OK) begin
      XatomicX(0);
      return;
   end

   if (check == UVM_CHECK) void'(do_check(exp, v, map));

   XatomicX(0);
endtask: mirror


// XatomicX

task uvm_reg::XatomicX(bit on);
   process m_reg_process;
   m_reg_process=process::self();

   if (on) begin
     if (m_reg_process == m_process)
       return;
     m_atomic.get(1);
     m_process = m_reg_process; 
   end
   else begin
      // Maybe a key was put back in by a spurious call to reset()
      void'(m_atomic.try_get(1));
      m_atomic.put(1);
      m_process = null;
   end
endtask: XatomicX


//-------------
// STANDARD OPS
//-------------

// convert2string

function string uvm_reg::convert2string();
   string res_str;
   string t_str;
   bit with_debug_info;

   string prefix;

   $sformat(convert2string, "Register %s -- %0d bytes, mirror value:'h%h",
            get_full_name(), get_n_bytes(),get());

   if (m_maps.num()==0)
     convert2string = {convert2string, "  (unmapped)\n"};
   else
     convert2string = {convert2string, "\n"};
   foreach (m_maps[map]) begin
     uvm_reg_map parent_map = map;
     int unsigned offset;
     while (parent_map != null) begin
       uvm_reg_map this_map = parent_map;
       parent_map = this_map.get_parent_map();
       offset = parent_map == null ? this_map.get_base_addr(UVM_NO_HIER) :
                                     parent_map.get_submap_offset(this_map);
       prefix = {prefix, "  "};
       begin
            uvm_endianness_e e = this_map.get_endian();
            $sformat(convert2string, 
                "%sMapped in '%s' -- %d bytes, %s, offset 'h%0h\n",
                prefix, this_map.get_full_name(), this_map.get_n_bytes(),
                e.name(), offset);
       end
     end
   end
   prefix = "  ";
   foreach(m_fields[i]) begin
      $sformat(convert2string, "%s\n%s", convert2string,
               m_fields[i].convert2string());
   end

   if (m_read_in_progress == 1'b1) begin
      if (m_fname != "" && m_lineno != 0)
         $sformat(res_str, "%s:%0d ",m_fname, m_lineno);
      convert2string = {convert2string, "\n", res_str,
                        "currently executing read method"}; 
   end
   if ( m_write_in_progress == 1'b1) begin
      if (m_fname != "" && m_lineno != 0)
         $sformat(res_str, "%s:%0d ",m_fname, m_lineno);
      convert2string = {convert2string, "\n", res_str,
                        "currently executing write method"}; 
   end

endfunction: convert2string


// do_print

function void uvm_reg::do_print (uvm_printer printer);
  uvm_reg_field f[$];
  super.do_print(printer);
  get_fields(f);
  foreach(f[i]) printer.print_generic(f[i].get_name(),f[i].get_type_name(),-2,f[i].convert2string());
endfunction



// clone

function uvm_object uvm_reg::clone();
  `uvm_fatal("RegModel","RegModel registers cannot be cloned")
  return null;
endfunction

// do_copy

function void uvm_reg::do_copy(uvm_object rhs);
  `uvm_fatal("RegModel","RegModel registers cannot be copied")
endfunction


// do_compare

function bit uvm_reg::do_compare (uvm_object  rhs,
                                        uvm_comparer comparer);
  `uvm_warning("RegModel","RegModel registers cannot be compared")
  return 0;
endfunction


// do_pack

function void uvm_reg::do_pack (uvm_packer packer);
  `uvm_warning("RegModel","RegModel registers cannot be packed")
endfunction


// do_unpack

function void uvm_reg::do_unpack (uvm_packer packer);
  `uvm_warning("RegModel","RegModel registers cannot be unpacked")
endfunction

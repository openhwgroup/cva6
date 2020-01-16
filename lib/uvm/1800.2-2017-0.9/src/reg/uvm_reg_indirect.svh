//
// -------------------------------------------------------------
// Copyright 2010-2011 Mentor Graphics Corporation
// Copyright 2010-2012 Synopsys, Inc.
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

typedef class uvm_reg_indirect_ftdr_seq;

//-----------------------------------------------------------------
// CLASS -- NODOCS -- uvm_reg_indirect_data
// Indirect data access abstraction class
//
// Models the behavior of a register used to indirectly access
// a register array, indexed by a second ~address~ register.
//
// This class should not be instantiated directly.
// A type-specific class extension should be used to
// provide a factory-enabled constructor and specify the
// ~n_bits~ and coverage models.
//-----------------------------------------------------------------

// @uvm-ieee 1800.2-2017 auto 18.7.1
class uvm_reg_indirect_data extends uvm_reg;

   protected uvm_reg m_idx;
   protected uvm_reg m_tbl[];


   // @uvm-ieee 1800.2-2017 auto 18.7.2.1
   function new(string name = "uvm_reg_indirect",
                int unsigned n_bits,
                int has_cover);
      super.new(name,n_bits,has_cover);
   endfunction: new

   virtual function void build();
   endfunction: build


   // @uvm-ieee 1800.2-2017 auto 18.7.2.2
   function void configure (uvm_reg idx,
                            uvm_reg reg_a[],
                            uvm_reg_block blk_parent,
                            uvm_reg_file regfile_parent = null);
      super.configure(blk_parent, regfile_parent, "");
      m_idx = idx;
      m_tbl = reg_a;

      // Not testable using pre-defined sequences
      uvm_resource_db#(bit)::set({"REG::", get_full_name()},
                                 "NO_REG_TESTS", 1);

      // Add a frontdoor to each indirectly-accessed register
      // for every address map this register is in.
      foreach (m_maps[map]) begin
         add_frontdoors(map);
      end
   endfunction
   
   /*local*/ virtual function void add_map(uvm_reg_map map);
      super.add_map(map);
      add_frontdoors(map);
   endfunction
   
   
   local function void add_frontdoors(uvm_reg_map map);
      foreach (m_tbl[i]) begin
         uvm_reg_indirect_ftdr_seq fd;
         if (m_tbl[i] == null) begin
            `uvm_error(get_full_name(),
                       $sformatf("Indirect register #%0d is NULL", i))
            continue;
         end
         fd = new(m_idx, i, this);
         if (m_tbl[i].is_in_map(map))
            m_tbl[i].set_frontdoor(fd, map);
         else
            map.add_reg(m_tbl[i], -1, "RW", 1, fd);
      end
   endfunction
   
   virtual function void do_predict (uvm_reg_item      rw,
                                     uvm_predict_e     kind = UVM_PREDICT_DIRECT,
                                     uvm_reg_byte_en_t be = -1);
      if (m_idx.get() >= m_tbl.size()) begin
         `uvm_error(get_full_name(), $sformatf("Address register %s has a value (%0d) greater than the maximum indirect register array size (%0d)", m_idx.get_full_name(), m_idx.get(), m_tbl.size()))
         rw.status = UVM_NOT_OK;
         return;
      end

      //NOTE limit to 2**32 registers
      begin
         int unsigned idx = m_idx.get();
         m_tbl[idx].do_predict(rw, kind, be);
      end
   endfunction


   virtual function uvm_reg_map get_local_map(uvm_reg_map map);
      return  m_idx.get_local_map(map);
   endfunction

   //
   // Just for good measure, to catch and short-circuit non-sensical uses
   //
   virtual function void add_field  (uvm_reg_field field);
      `uvm_error(get_full_name(), "Cannot add field to an indirect data access register")
   endfunction

   virtual function void set (uvm_reg_data_t  value,
                              string          fname = "",
                              int             lineno = 0);
      `uvm_error(get_full_name(), "Cannot set() an indirect data access register")
   endfunction
   
   virtual function uvm_reg_data_t  get(string  fname = "",
                                        int     lineno = 0);
      `uvm_error(get_full_name(), "Cannot get() an indirect data access register")
      return 0;
   endfunction
   
   virtual function uvm_reg get_indirect_reg(string  fname = "",
                                        int     lineno = 0);
      int unsigned idx = m_idx.get_mirrored_value();
      return(m_tbl[idx]);
   endfunction

   virtual function bit needs_update();
      return 0;
   endfunction

   virtual task write(output uvm_status_e      status,
                      input  uvm_reg_data_t    value,
                      input  uvm_door_e        path = UVM_DEFAULT_DOOR,
                      input  uvm_reg_map       map = null,
                      input  uvm_sequence_base parent = null,
                      input  int               prior = -1,
                      input  uvm_object        extension = null,
                      input  string            fname = "",
                      input  int               lineno = 0);

      if (path == UVM_DEFAULT_DOOR) begin
         uvm_reg_block blk = get_parent();
         path = blk.get_default_door();
      end
      
      if (path == UVM_BACKDOOR) begin
         `uvm_warning(get_full_name(), "Cannot backdoor-write an indirect data access register. Switching to frontdoor.")
         path = UVM_FRONTDOOR;
      end

      // Can't simply call super.write() because it'll call set()
      begin
         uvm_reg_item rw;

         XatomicX(1);

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
      end
   endtask

   virtual task read(output uvm_status_e      status,
                     output uvm_reg_data_t    value,
                     input  uvm_door_e        path = UVM_DEFAULT_DOOR,
                     input  uvm_reg_map       map = null,
                     input  uvm_sequence_base parent = null,
                     input  int               prior = -1,
                     input  uvm_object        extension = null,
                     input  string            fname = "",
                     input  int               lineno = 0);

      if (path == UVM_DEFAULT_DOOR) begin
         uvm_reg_block blk = get_parent();
         path = blk.get_default_door();
      end
      
      if (path == UVM_BACKDOOR) begin
         `uvm_warning(get_full_name(), "Cannot backdoor-read an indirect data access register. Switching to frontdoor.")
         path = UVM_FRONTDOOR;
      end
      
      super.read(status, value, path, map, parent, prior, extension, fname, lineno);
   endtask

   virtual task poke(output uvm_status_e      status,
                     input  uvm_reg_data_t    value,
                     input  string            kind = "",
                     input  uvm_sequence_base parent = null,
                     input  uvm_object        extension = null,
                     input  string            fname = "",
                     input  int               lineno = 0);
      `uvm_error(get_full_name(), "Cannot poke() an indirect data access register")
      status = UVM_NOT_OK;
   endtask

   virtual task peek(output uvm_status_e      status,
                     output uvm_reg_data_t    value,
                     input  string            kind = "",
                     input  uvm_sequence_base parent = null,
                     input  uvm_object        extension = null,
                     input  string            fname = "",
                     input  int               lineno = 0);
      `uvm_error(get_full_name(), "Cannot peek() an indirect data access register")
      status = UVM_NOT_OK;
   endtask

   virtual task update(output uvm_status_e      status,
                       input  uvm_door_e        path = UVM_DEFAULT_DOOR,
                       input  uvm_reg_map       map = null,
                       input  uvm_sequence_base parent = null,
                       input  int               prior = -1,
                       input  uvm_object        extension = null,
                       input  string            fname = "",
                       input  int               lineno = 0);
      status = UVM_IS_OK;
   endtask
   
   virtual task mirror(output uvm_status_e      status,
                       input uvm_check_e        check  = UVM_NO_CHECK,
                       input uvm_door_e         path = UVM_DEFAULT_DOOR,
                       input uvm_reg_map        map = null,
                       input uvm_sequence_base  parent = null,
                       input int                prior = -1,
                       input  uvm_object        extension = null,
                       input string             fname = "",
                       input int                lineno = 0);
      status = UVM_IS_OK;
   endtask
   
endclass : uvm_reg_indirect_data


class uvm_reg_indirect_ftdr_seq extends uvm_reg_frontdoor;
   local uvm_reg m_addr_reg;
   local uvm_reg m_data_reg;
   local int     m_idx;
   
   function new(uvm_reg addr_reg,
                int idx,
                uvm_reg data_reg);
      super.new("uvm_reg_indirect_ftdr_seq");
      m_addr_reg = addr_reg;
      m_idx      = idx;
      m_data_reg = data_reg;
   endfunction: new

   virtual task body();

      uvm_reg_item rw;
      
      $cast(rw,rw_info.clone());
      rw.element = m_addr_reg;
      rw.kind    = UVM_WRITE;
      rw.value[0]= m_idx;

      m_addr_reg.XatomicX(1);
      m_data_reg.XatomicX(1);
      
      m_addr_reg.do_write(rw);

      if (rw.status == UVM_NOT_OK)
        return;

      $cast(rw,rw_info.clone());
      rw.element = m_data_reg;

      if (rw_info.kind == UVM_WRITE)
        m_data_reg.do_write(rw);
      else begin
        m_data_reg.do_read(rw);
        rw_info.value[0] = rw.value[0];
      end

      m_addr_reg.XatomicX(0);
      m_data_reg.XatomicX(0);
      
      rw_info.status = rw.status;
   endtask

endclass

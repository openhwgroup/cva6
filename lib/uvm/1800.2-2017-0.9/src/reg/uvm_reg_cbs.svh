//
// -------------------------------------------------------------
// Copyright 2010-2011 Mentor Graphics Corporation
// Copyright 2004-2018 Synopsys, Inc.
// Copyright 2010-2018 Cadence Design Systems, Inc.
// Copyright 2010 AMD
// Copyright 2014-2018 NVIDIA Corporation
// Copyright 2014 Cisco Systems, Inc.
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

typedef class uvm_reg;
typedef class uvm_mem;
typedef class uvm_reg_backdoor;

//------------------------------------------------------------------------------
// Title -- NODOCS -- Register Callbacks
//
// This section defines the base class used for all register callback
// extensions. It also includes pre-defined callback extensions for use on
// read-only and write-only registers.
//------------------------------------------------------------------------------


//------------------------------------------------------------------------------
// Class -- NODOCS -- uvm_reg_cbs
//
// Facade class for field, register, memory and backdoor
// access callback methods. 
//------------------------------------------------------------------------------

// @uvm-ieee 1800.2-2017 auto 18.11.1
class uvm_reg_cbs extends uvm_callback;

   `uvm_object_utils(uvm_reg_cbs)


   // @uvm-ieee 1800.2-2017 auto 18.11.2.1
   function new(string name = "uvm_reg_cbs");
      super.new(name);
   endfunction



   // @uvm-ieee 1800.2-2017 auto 18.11.2.2
   virtual task pre_write(uvm_reg_item rw); endtask



   // @uvm-ieee 1800.2-2017 auto 18.11.2.3
   virtual task post_write(uvm_reg_item rw); endtask



   // @uvm-ieee 1800.2-2017 auto 18.11.2.4
   virtual task pre_read(uvm_reg_item rw); endtask



   // @uvm-ieee 1800.2-2017 auto 18.11.2.5
   virtual task post_read(uvm_reg_item rw); endtask



   // @uvm-ieee 1800.2-2017 auto 18.11.2.6
   virtual function void post_predict(input uvm_reg_field  fld,
                                      input uvm_reg_data_t previous,
                                      inout uvm_reg_data_t value,
                                      input uvm_predict_e  kind,
                                      input uvm_door_e     path,
                                      input uvm_reg_map    map);
   endfunction



   // @uvm-ieee 1800.2-2017 auto 18.11.2.7
   virtual function void encode(ref uvm_reg_data_t data[]);
   endfunction



   // @uvm-ieee 1800.2-2017 auto 18.11.2.8
   virtual function void decode(ref uvm_reg_data_t data[]);
   endfunction



endclass


//------------------
// Section -- NODOCS -- Typedefs
//------------------


// Type -- NODOCS -- uvm_reg_cb
//
// Convenience callback type declaration for registers
//
// Use this declaration to register the register callbacks rather than
// the more verbose parameterized class
//
typedef uvm_callbacks#(uvm_reg, uvm_reg_cbs) uvm_reg_cb /* @uvm-ieee 1800.2-2017 auto D.4.6.1*/   ;


// Type -- NODOCS -- uvm_reg_cb_iter
//
// Convenience callback iterator type declaration for registers
//
// Use this declaration to iterate over registered register callbacks
// rather than the more verbose parameterized class
//
typedef uvm_callback_iter#(uvm_reg, uvm_reg_cbs) uvm_reg_cb_iter /* @uvm-ieee 1800.2-2017 auto D.4.6.2*/   ;


// Type -- NODOCS -- uvm_reg_bd_cb
//
// Convenience callback type declaration for backdoor
//
// Use this declaration to register register backdoor callbacks rather than
// the more verbose parameterized class
//
typedef uvm_callbacks#(uvm_reg_backdoor, uvm_reg_cbs) uvm_reg_bd_cb /* @uvm-ieee 1800.2-2017 auto D.4.6.3*/   ;


// Type -- NODOCS -- uvm_reg_bd_cb_iter
// Convenience callback iterator type declaration for backdoor
//
// Use this declaration to iterate over registered register backdoor callbacks
// rather than the more verbose parameterized class
//

typedef uvm_callback_iter#(uvm_reg_backdoor, uvm_reg_cbs) uvm_reg_bd_cb_iter /* @uvm-ieee 1800.2-2017 auto D.4.6.4*/   ;


// Type -- NODOCS -- uvm_mem_cb
//
// Convenience callback type declaration for memories
//
// Use this declaration to register memory callbacks rather than
// the more verbose parameterized class
//
typedef uvm_callbacks#(uvm_mem, uvm_reg_cbs) uvm_mem_cb /* @uvm-ieee 1800.2-2017 auto D.4.6.5*/   ;


// Type -- NODOCS -- uvm_mem_cb_iter
//
// Convenience callback iterator type declaration for memories
//
// Use this declaration to iterate over registered memory callbacks
// rather than the more verbose parameterized class
//
typedef uvm_callback_iter#(uvm_mem, uvm_reg_cbs) uvm_mem_cb_iter /* @uvm-ieee 1800.2-2017 auto D.4.6.6*/   ;


// Type -- NODOCS -- uvm_reg_field_cb
//
// Convenience callback type declaration for fields
//
// Use this declaration to register field callbacks rather than
// the more verbose parameterized class
//
typedef uvm_callbacks#(uvm_reg_field, uvm_reg_cbs) uvm_reg_field_cb /* @uvm-ieee 1800.2-2017 auto D.4.6.7*/   ;


// Type -- NODOCS -- uvm_reg_field_cb_iter
//
// Convenience callback iterator type declaration for fields
//
// Use this declaration to iterate over registered field callbacks
// rather than the more verbose parameterized class
//
typedef uvm_callback_iter#(uvm_reg_field, uvm_reg_cbs) uvm_reg_field_cb_iter /* @uvm-ieee 1800.2-2017 auto D.4.6.8*/   ;


//-----------------------------
// Group -- NODOCS -- Predefined Extensions
//-----------------------------

//------------------------------------------------------------------------------
// Class -- NODOCS -- uvm_reg_read_only_cbs
//
// Pre-defined register callback method for read-only registers
// that will issue an error if a write() operation is attempted.
//
//------------------------------------------------------------------------------

// @uvm-ieee 1800.2-2017 auto 18.11.4.1
class uvm_reg_read_only_cbs extends uvm_reg_cbs;
// SEE MANTIS 6040. This is supposed to be Virtual, but cannot since an instance is 
// created.  leaving NON virtual for now. 

   function new(string name = "uvm_reg_read_only_cbs");
      super.new(name);
   endfunction

   `uvm_object_utils(uvm_reg_read_only_cbs)

   

   // @uvm-ieee 1800.2-2017 auto 18.11.4.2.1
   virtual task pre_write(uvm_reg_item rw);
      string name = rw.element.get_full_name();
      
      if (rw.status != UVM_IS_OK)
         return;

      if (rw.element_kind == UVM_FIELD) begin
         uvm_reg_field fld;
         uvm_reg rg;
         $cast(fld, rw.element);
         rg = fld.get_parent();
         name = rg.get_full_name();
      end
      
      `uvm_error("UVM/REG/READONLY",
                 {name, " is read-only. Cannot call write() method."})

      rw.status = UVM_NOT_OK;
   endtask

   local static uvm_reg_read_only_cbs m_me;
   local static function uvm_reg_read_only_cbs get();
      if (m_me == null) m_me = new;
      return m_me;
   endfunction



   // @uvm-ieee 1800.2-2017 auto 18.11.4.2.2
   static function void add(uvm_reg rg);
      uvm_reg_field flds[$];
      
      uvm_reg_cb::add(rg, get());
      rg.get_fields(flds);
      foreach (flds[i]) begin
         uvm_reg_field_cb::add(flds[i], get());
      end
   endfunction



   // @uvm-ieee 1800.2-2017 auto 18.11.4.2.3
   static function void remove(uvm_reg rg);
      uvm_reg_cb_iter cbs = new(rg);
      uvm_reg_field flds[$];

      void'(cbs.first());
      while (cbs.get_cb() != get()) begin
         if (cbs.get_cb() == null)
            return;
         void'(cbs.next());
      end
      uvm_reg_cb::delete(rg, get());
      rg.get_fields(flds);
      foreach (flds[i]) begin
         uvm_reg_field_cb::delete(flds[i], get());
      end
   endfunction
endclass


//------------------------------------------------------------------------------
// Class -- NODOCS -- uvm_reg_write_only_cbs
//
// Pre-defined register callback method for write-only registers
// that will issue an error if a read() operation is attempted.
//
//------------------------------------------------------------------------------


// @uvm-ieee 1800.2-2017 auto 18.11.5.1
class uvm_reg_write_only_cbs extends uvm_reg_cbs;
// SEE MANTIS 6040. This is supposed to be Virtual, but cannot since an instance is 
// created.  leaving NON virtual for now. 

   // @uvm-ieee 1800.2-2017 auto 18.1.2.1
   function new(string name = "uvm_reg_write_only_cbs");
      super.new(name);
   endfunction

   `uvm_object_utils(uvm_reg_write_only_cbs)
   

   // @uvm-ieee 1800.2-2017 auto 18.11.5.2.1
   virtual task pre_read(uvm_reg_item rw);
      string name = rw.element.get_full_name();
      
      if (rw.status != UVM_IS_OK)
         return;

      if (rw.element_kind == UVM_FIELD) begin
         uvm_reg_field fld;
         uvm_reg rg;
         $cast(fld, rw.element);
         rg = fld.get_parent();
         name = rg.get_full_name();
      end
      
      `uvm_error("UVM/REG/WRTEONLY",
                 {name, " is write-only. Cannot call read() method."})

      rw.status = UVM_NOT_OK;
   endtask

   local static uvm_reg_write_only_cbs m_me;
   local static function uvm_reg_write_only_cbs get();
      if (m_me == null) m_me = new;
      return m_me;
   endfunction



   // @uvm-ieee 1800.2-2017 auto 18.11.5.2.2
   static function void add(uvm_reg rg);
      uvm_reg_field flds[$];
      
      uvm_reg_cb::add(rg, get());
      rg.get_fields(flds);
      foreach (flds[i]) begin
         uvm_reg_field_cb::add(flds[i], get());
      end
   endfunction



   // @uvm-ieee 1800.2-2017 auto 18.11.5.2.3
   static function void remove(uvm_reg rg);
      uvm_reg_cb_iter cbs = new(rg);
      uvm_reg_field flds[$];

      void'(cbs.first());
      while (cbs.get_cb() != get()) begin
         if (cbs.get_cb() == null)
            return;
         void'(cbs.next());
      end
      uvm_reg_cb::delete(rg, get());
      rg.get_fields(flds);
      foreach (flds[i]) begin
         uvm_reg_field_cb::delete(flds[i], get());
      end
   endfunction
endclass

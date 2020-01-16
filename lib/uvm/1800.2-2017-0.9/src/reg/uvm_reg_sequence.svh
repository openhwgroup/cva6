//
// -------------------------------------------------------------
// Copyright 2010-2011 Mentor Graphics Corporation
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
// TITLE -- NODOCS -- Register Sequence Classes
//------------------------------------------------------------------------------
//
// This section defines the base classes used for register stimulus generation.
//------------------------------------------------------------------------------

                                                              
//------------------------------------------------------------------------------
//
// CLASS -- NODOCS -- uvm_reg_sequence
//
// This class provides base functionality for both user-defined RegModel test
// sequences and "register translation sequences".
//
// - When used as a base for user-defined RegModel test sequences, this class
//   provides convenience methods for reading and writing registers and
//   memories. Users implement the body() method to interact directly with
//   the RegModel model (held in the <model> property) or indirectly via the
//   delegation methods in this class. 
//
// - When used as a translation sequence, objects of this class are
//   executed directly on a bus sequencer which are used in support of a layered sequencer
//   use model, a pre-defined convert-and-execute algorithm is provided.
//
// Register operations do not require extending this class if none of the above
// services are needed. Register test sequences can be extend from the base
// <uvm_sequence #(REQ,RSP)> base class or even from outside a sequence. 
//
// Note- The convenience API not yet implemented.
//------------------------------------------------------------------------------

// @uvm-ieee 1800.2-2017 auto 19.4.1.1
class uvm_reg_sequence #(type BASE=uvm_sequence #(uvm_reg_item)) extends BASE;

  `uvm_object_param_utils(uvm_reg_sequence #(BASE))

  // Parameter -- NODOCS -- BASE
  //
  // Specifies the sequence type to extend from.
  //
  // When used as a translation sequence running on a bus sequencer, ~BASE~ must
  // be compatible with the sequence type expected by the bus sequencer.
  //
  // When used as a test sequence running on a particular sequencer, ~BASE~
  // must be compatible with the sequence type expected by that sequencer.
  //
  // When used as a virtual test sequence without a sequencer, ~BASE~ does
  // not need to be specified, i.e. the default specialization is adequate.
  // 
  // To maximize opportunities for reuse, user-defined RegModel sequences should
  // "promote" the BASE parameter.
  //
  // | class my_reg_sequence #(type BASE=uvm_sequence #(uvm_reg_item))
  // |                               extends uvm_reg_sequence #(BASE);
  //
  // This way, the RegModel sequence can be extended from 
  // user-defined base sequences.


  // Variable -- NODOCS -- model
  //
  // Block abstraction this sequence executes on, defined only when this
  // sequence is a user-defined test sequence.
  //
  uvm_reg_block model;


  // Variable -- NODOCS -- adapter
  //
  // Adapter to use for translating between abstract register transactions
  // and physical bus transactions, defined only when this sequence is a
  // translation sequence.
  //
  uvm_reg_adapter adapter;


  // Variable -- NODOCS -- reg_seqr
  //
  // Layered upstream "register" sequencer.
  //
  // Specifies the upstream sequencer between abstract register transactions
  // and physical bus transactions. Defined only when this sequence is a
  // translation sequence, and we want to "pull" from an upstream sequencer.
  //
  uvm_sequencer #(uvm_reg_item) reg_seqr;



  // @uvm-ieee 1800.2-2017 auto 19.4.1.4.1
  function new (string name="uvm_reg_sequence_inst");
    super.new(name);
  endfunction



  // @uvm-ieee 1800.2-2017 auto 19.4.1.4.2
  virtual task body();
    if (m_sequencer == null) begin
      `uvm_fatal("NO_SEQR", {"Sequence executing as translation sequence, ",
         "but is not associated with a sequencer (m_sequencer == null)"})
    end
    if (reg_seqr == null) begin
      `uvm_warning("REG_XLATE_NO_SEQR",
         {"Executing RegModel translation sequence on sequencer ",
       m_sequencer.get_full_name(),"' does not have an upstream sequencer defined. ",
       "Execution of register items available only via direct calls to 'do_reg_item'"})
      wait(0);
    end
    `uvm_info("REG_XLATE_SEQ_START",
       {"Starting RegModel translation sequence on sequencer ",
       m_sequencer.get_full_name(),"'"},UVM_LOW)
    forever begin
      uvm_reg_item reg_item;
      reg_seqr.peek(reg_item);
      do_reg_item(reg_item);
      reg_seqr.get(reg_item);
      #0;
    end
  endtask


  typedef enum { LOCAL, UPSTREAM } seq_parent_e;

  seq_parent_e parent_select = LOCAL;

  uvm_sequence_base upstream_parent;



  // @uvm-ieee 1800.2-2017 auto 19.4.1.4.3
  virtual task do_reg_item(uvm_reg_item rw);
     string rws=rw.convert2string();
    if (m_sequencer == null)
     `uvm_fatal("REG/DO_ITEM/NULL","do_reg_item: m_sequencer is null") 
    if (adapter == null)
     `uvm_fatal("REG/DO_ITEM/NULL","do_reg_item: adapter handle is null") 

    `uvm_info("DO_RW_ACCESS",{"Doing transaction: ",rws},UVM_HIGH)

    if (parent_select == LOCAL) begin
      upstream_parent = rw.parent;
      rw.parent = this;
    end

    if (rw.kind == UVM_WRITE)
      rw.local_map.do_bus_write(rw, m_sequencer, adapter);
    else
      rw.local_map.do_bus_read(rw, m_sequencer, adapter);
    
    if (parent_select == LOCAL)
       rw.parent = upstream_parent;
  endtask


   //----------------------------------
   // Group -- NODOCS -- Convenience Write/Read API
   //----------------------------------
   //
   // The following methods delegate to the corresponding method in the 
   // register or memory element. They allow a sequence ~body()~ to do
   // reads and writes without having to explicitly supply itself to
   // ~parent~ sequence argument. Thus, a register write
   //
   //| model.regA.write(status, value, .parent(this));
   //
   // can be written instead as
   //
   //| write_reg(model.regA, status, value);
   //



   // @uvm-ieee 1800.2-2017 auto 19.4.1.5.1
   virtual task write_reg(input  uvm_reg           rg,
                          output uvm_status_e      status,
                          input  uvm_reg_data_t    value,
                          input  uvm_door_e        path = UVM_DEFAULT_DOOR,
                          input  uvm_reg_map       map = null,
                          input  int               prior = -1,
                          input  uvm_object        extension = null,
                          input  string            fname = "",
                          input  int               lineno = 0);
      if (rg == null)
        `uvm_error("NO_REG","Register argument is null")
      else
        rg.write(status,value,path,map,this,prior,extension,fname,lineno);
   endtask



   // @uvm-ieee 1800.2-2017 auto 19.4.1.5.2
   virtual task read_reg(input  uvm_reg           rg,
                         output uvm_status_e      status,
                         output uvm_reg_data_t    value,
                         input  uvm_door_e        path = UVM_DEFAULT_DOOR,
                         input  uvm_reg_map       map = null,
                         input  int               prior = -1,
                         input  uvm_object        extension = null,
                         input  string            fname = "",
                         input  int               lineno = 0);
      if (rg == null)
        `uvm_error("NO_REG","Register argument is null")
      else
        rg.read(status,value,path,map,this,prior,extension,fname,lineno);
   endtask




   // @uvm-ieee 1800.2-2017 auto 19.4.1.5.3
   virtual task poke_reg(input  uvm_reg           rg,
                         output uvm_status_e      status,
                         input  uvm_reg_data_t    value,
                         input  string            kind = "",
                         input  uvm_object        extension = null,
                         input  string            fname = "",
                         input  int               lineno = 0);
      if (rg == null)
        `uvm_error("NO_REG","Register argument is null")
      else
        rg.poke(status,value,kind,this,extension,fname,lineno);
   endtask




   // @uvm-ieee 1800.2-2017 auto 19.4.1.5.4
   virtual task peek_reg(input  uvm_reg           rg,
                         output uvm_status_e      status,
                         output uvm_reg_data_t    value,
                         input  string            kind = "",
                         input  uvm_object        extension = null,
                         input  string            fname = "",
                         input  int               lineno = 0);
      if (rg == null)
        `uvm_error("NO_REG","Register argument is null")
      else
        rg.peek(status,value,kind,this,extension,fname,lineno);
   endtask

   
   

   // @uvm-ieee 1800.2-2017 auto 19.4.1.5.5
   virtual task update_reg(input  uvm_reg           rg,
                           output uvm_status_e      status,
                           input  uvm_door_e        path = UVM_DEFAULT_DOOR,
                           input  uvm_reg_map       map = null,
                           input  int               prior = -1,
                           input  uvm_object        extension = null,
                           input  string            fname = "",
                           input  int               lineno = 0);
      if (rg == null)
        `uvm_error("NO_REG","Register argument is null")
      else
        rg.update(status,path,map,this,prior,extension,fname,lineno);
   endtask




   // @uvm-ieee 1800.2-2017 auto 19.4.1.5.6
   virtual task mirror_reg(input  uvm_reg       rg,
                           output uvm_status_e  status,
                           input  uvm_check_e   check  = UVM_NO_CHECK,
                           input  uvm_door_e    path = UVM_DEFAULT_DOOR,
                           input  uvm_reg_map   map = null,
                           input  int           prior = -1,
                           input  uvm_object    extension = null,
                           input  string        fname = "",
                           input  int           lineno = 0);
      if (rg == null)
        `uvm_error("NO_REG","Register argument is null")
      else
        rg.mirror(status,check,path,map,this,prior,extension,fname,lineno);
   endtask

  


   // @uvm-ieee 1800.2-2017 auto 19.4.1.5.7
   virtual task write_mem(input  uvm_mem           mem,
                          output uvm_status_e      status,
                          input  uvm_reg_addr_t    offset,
                          input  uvm_reg_data_t    value,
                          input  uvm_door_e        path = UVM_DEFAULT_DOOR,
                          input  uvm_reg_map       map = null,
                          input  int               prior = -1,
                          input  uvm_object        extension = null,
                          input  string            fname = "",
                          input  int               lineno = 0);
      if (mem == null)
        `uvm_error("NO_MEM","Memory argument is null")
      else
        mem.write(status,offset,value,path,map,this,prior,extension,fname,lineno);
   endtask



   // @uvm-ieee 1800.2-2017 auto 19.4.1.5.8
   virtual task read_mem(input  uvm_mem           mem,
                         output uvm_status_e      status,
                         input  uvm_reg_addr_t    offset,
                         output uvm_reg_data_t    value,
                         input  uvm_door_e        path = UVM_DEFAULT_DOOR,
                         input  uvm_reg_map       map = null,
                         input  int               prior = -1,
                         input  uvm_object        extension = null,
                         input  string            fname = "",
                         input  int               lineno = 0);
      if (mem == null)
        `uvm_error("NO_MEM","Memory argument is null")
      else
        mem.read(status,offset,value,path,map,this,prior,extension,fname,lineno);
   endtask




   // @uvm-ieee 1800.2-2017 auto 19.4.1.5.9
   virtual task poke_mem(input  uvm_mem           mem,
                         output uvm_status_e      status,
                         input  uvm_reg_addr_t    offset,
                         input  uvm_reg_data_t    value,
                         input  string            kind = "",
                         input  uvm_object        extension = null,
                         input  string            fname = "",
                         input  int               lineno = 0);
      if (mem == null)
        `uvm_error("NO_MEM","Memory argument is null")
      else
        mem.poke(status,offset,value,kind,this,extension,fname,lineno);
   endtask




   // @uvm-ieee 1800.2-2017 auto 19.4.1.5.10
   virtual task peek_mem(input  uvm_mem           mem,
                         output uvm_status_e      status,
                         input  uvm_reg_addr_t    offset,
                         output uvm_reg_data_t    value,
                         input  string            kind = "",
                         input  uvm_object        extension = null,
                         input  string            fname = "",
                         input  int               lineno = 0);
      if (mem == null)
        `uvm_error("NO_MEM","Memory argument is null")
      else
        mem.peek(status,offset,value,kind,this,extension,fname,lineno);
   endtask

   
  // Function- put_response
  //
  // not user visible. Needed to populate this sequence's response
  // queue with any bus item type. 
  //
  virtual function void put_response(uvm_sequence_item response_item);
    put_base_response(response_item);
  endfunction

endclass



// @uvm-ieee 1800.2-2017 auto 19.4.2.1
virtual class uvm_reg_frontdoor extends uvm_reg_sequence #(uvm_sequence #(uvm_sequence_item));

   `uvm_object_abstract_utils(uvm_reg_frontdoor)


   // Variable -- NODOCS -- rw_info
   //
   // Holds information about the register being read or written
   //
   uvm_reg_item rw_info;

   // Variable -- NODOCS -- sequencer
   //
   // Sequencer executing the operation
   //
   uvm_sequencer_base sequencer;


   // @uvm-ieee 1800.2-2017 auto 19.4.2.3
   function new(string name="");
      super.new(name);
   endfunction

   string fname;
   int lineno;

endclass: uvm_reg_frontdoor

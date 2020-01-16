//
//--------------------------------------------------------------
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
//--------------------------------------------------------------
//
 
//------------------------------------------------------------------------------
// Title -- NODOCS -- Generic Register Operation Descriptors
//
// This section defines the abstract register transaction item. It also defines
// a descriptor for a physical bus operation that is used by <uvm_reg_adapter>
// subtypes to convert from a protocol-specific address/data/rw operation to
// a bus-independent, canonical r/w operation.
//------------------------------------------------------------------------------


//------------------------------------------------------------------------------
// CLASS -- NODOCS -- uvm_reg_item
//
// Defines an abstract register transaction item. No bus-specific information
// is present, although a handle to a <uvm_reg_map> is provided in case a user
// wishes to implement a custom address translation algorithm.
//------------------------------------------------------------------------------

// @uvm-ieee 1800.2-2017 auto 19.1.1.1
class uvm_reg_item extends uvm_sequence_item;

  `uvm_object_utils(uvm_reg_item)

  // Variable -- NODOCS -- element_kind
  //
  // Kind of element being accessed: REG, MEM, or FIELD. See <uvm_elem_kind_e>.
  //
  uvm_elem_kind_e element_kind;


  // Variable -- NODOCS -- element
  //
  // A handle to the RegModel model element associated with this transaction.
  // Use <element_kind> to determine the type to cast  to: <uvm_reg>,
  // <uvm_mem>, or <uvm_reg_field>.
  //
  uvm_object element;


  // Variable -- NODOCS -- kind
  //
  // Kind of access: READ or WRITE.
  //
  rand uvm_access_e kind;


  // Variable -- NODOCS -- value
  //
  // The value to write to, or after completion, the value read from the DUT.
  // Burst operations use the <values> property.
  //
  rand uvm_reg_data_t value[];


  // TODO: parameterize
  constraint max_values { value.size() > 0 && value.size() < 1000; }

  // Variable -- NODOCS -- offset
  //
  // For memory accesses, the offset address. For bursts,
  // the ~starting~ offset address.
  //
  rand uvm_reg_addr_t offset;


  // Variable -- NODOCS -- status
  //
  // The result of the transaction: IS_OK, HAS_X, or ERROR.
  // See <uvm_status_e>.
  //
  uvm_status_e status;


  // Variable -- NODOCS -- local_map
  //
  // The local map used to obtain addresses. Users may customize 
  // address-translation using this map. Access to the sequencer
  // and bus adapter can be obtained by getting this map's root map,
  // then calling <uvm_reg_map::get_sequencer> and 
  // <uvm_reg_map::get_adapter>.
  //
  uvm_reg_map local_map;


  // Variable -- NODOCS -- map
  //
  // The original map specified for the operation. The actual <map>
  // used may differ when a test or sequence written at the block
  // level is reused at the system level.
  //
  uvm_reg_map map;


  // Variable -- NODOCS -- path
  //
  // The path being used: <UVM_FRONTDOOR> or <UVM_BACKDOOR>.
  //
  uvm_door_e path;


  // Variable -- NODOCS -- parent
  //
  // The sequence from which the operation originated.
  //
  rand uvm_sequence_base parent;


  // Variable -- NODOCS -- prior
  //
  // The priority requested of this transfer, as defined by
  // <uvm_sequence_base::start_item>.
  //
  int prior = -1;


  // Variable -- NODOCS -- extension
  //
  // Handle to optional user data, as conveyed in the call to
  // write(), read(), mirror(), or update() used to trigger the operation.
  //
  rand uvm_object extension;


  // Variable -- NODOCS -- bd_kind
  //
  // If path is UVM_BACKDOOR, this member specifies the abstraction 
  // kind for the backdoor access, e.g. "RTL" or "GATES".
  //
  string bd_kind;


  // Variable -- NODOCS -- fname
  //
  // The file name from where this transaction originated, if provided
  // at the call site.
  //
  string fname;


  // Variable -- NODOCS -- lineno
  //
  // The file name from where this transaction originated, if provided 
  // at the call site.
  //
  int lineno;



  // @uvm-ieee 1800.2-2017 auto 19.1.1.3.1
  function new(string name="");
    super.new(name);
    value = new[1];
  endfunction



  // @uvm-ieee 1800.2-2017 auto 19.1.1.3.2
  virtual function string convert2string();
    string s,value_s;
    s = {"kind=",kind.name(),
         " ele_kind=",element_kind.name(),
         " ele_name=",element==null?"null":element.get_full_name() };

    if (value.size() > 1 && uvm_report_enabled(UVM_HIGH, UVM_INFO, "RegModel")) begin
      value_s = "'{";
      foreach (value[i])
         value_s = {value_s,$sformatf("%0h,",value[i])};
      value_s[value_s.len()-1]="}";
    end
    else
      value_s = $sformatf("%0h",value[0]);
    s = {s, " value=",value_s};

    if (element_kind == UVM_MEM)
      s = {s, $sformatf(" offset=%0h",offset)};
    s = {s," map=",(map==null?"null":map.get_full_name())," path=",path.name()};
    s = {s," status=",status.name()};
    return s;
  endfunction


  // Function -- NODOCS -- do_copy
  //
  // Copy the ~rhs~ object into this object. The ~rhs~ object must
  // derive from <uvm_reg_item>.
  //
  virtual function void do_copy(uvm_object rhs);
    uvm_reg_item rhs_;
    if (rhs == null)
     `uvm_fatal("REG/NULL","do_copy: rhs argument is null") 

    if (!$cast(rhs_,rhs)) begin
      `uvm_error("WRONG_TYPE","Provided rhs is not of type uvm_reg_item")
      return;
    end
    super.do_copy(rhs);
    element_kind = rhs_.element_kind;
    element = rhs_.element;
    kind = rhs_.kind;
    value = rhs_.value;
    offset = rhs_.offset;
    status = rhs_.status;
    local_map = rhs_.local_map;
    map = rhs_.map;
    path = rhs_.path;
    extension = rhs_.extension;
    bd_kind = rhs_.bd_kind;
    parent = rhs_.parent;
    prior = rhs_.prior;
    fname = rhs_.fname;
    lineno = rhs_.lineno;
  endfunction

endclass




typedef struct {


  uvm_access_e kind;



  uvm_reg_addr_t addr;



  uvm_reg_data_t data;

   

  int n_bits;

  /*
  constraint valid_n_bits {
     n_bits > 0;
     n_bits <= `UVM_REG_DATA_WIDTH;
  }
  */



  uvm_reg_byte_en_t byte_en;



  uvm_status_e status;

} uvm_reg_bus_op;

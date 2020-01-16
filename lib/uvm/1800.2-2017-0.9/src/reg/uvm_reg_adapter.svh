//
// -------------------------------------------------------------
// Copyright 2010-2011 Mentor Graphics Corporation
// Copyright 2014 Semifore
// Copyright 2004-2018 Synopsys, Inc.
// Copyright 2010-2018 Cadence Design Systems, Inc.
// Copyright 2010 AMD
// Copyright 2014-2015 NVIDIA Corporation
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
// Title -- NODOCS -- Classes for Adapting Between Register and Bus Operations
//
// This section defines classes used to convert transaction streams between
// generic register address/data reads and writes and physical bus accesses. 
//------------------------------------------------------------------------------


//------------------------------------------------------------------------------
//
// Class -- NODOCS -- uvm_reg_adapter
//
// This class defines an interface for converting between <uvm_reg_bus_op>
// and a specific bus transaction. 
//------------------------------------------------------------------------------

// @uvm-ieee 1800.2-2017 auto 19.2.1.1
virtual class uvm_reg_adapter extends uvm_object;


   `uvm_object_abstract_utils(uvm_reg_adapter)


  // Function -- NODOCS -- new
  //
  // Create a new instance of this type, giving it the optional ~name~.

  // @uvm-ieee 1800.2-2017 auto 19.2.1.2.1
  function new(string name="");
    super.new(name);
  endfunction


  // Variable -- NODOCS -- supports_byte_enable
  //
  // Set this bit in extensions of this class if the bus protocol supports
  // byte enables.
  
  bit supports_byte_enable;


  // Variable -- NODOCS -- provides_responses
  //
  // Set this bit in extensions of this class if the bus driver provides
  // separate response items.

  bit provides_responses; 


  // Variable -- NODOCS -- parent_sequence
  //
  // Set this member in extensions of this class if the bus driver requires
  // bus items be executed via a particular sequence base type. The sequence
  // assigned to this member must implement do_clone().

  uvm_sequence_base parent_sequence; 


  // Function -- NODOCS -- reg2bus
  //
  // Extensions of this class ~must~ implement this method to convert the specified
  // <uvm_reg_bus_op> to a corresponding <uvm_sequence_item> subtype that defines the bus
  // transaction.
  //
  // The method must allocate a new bus-specific <uvm_sequence_item>,
  // assign its members from
  // the corresponding members from the given generic ~rw~ bus operation, then
  // return it.

  // @uvm-ieee 1800.2-2017 auto 19.2.1.2.5
  pure virtual function uvm_sequence_item reg2bus(const ref uvm_reg_bus_op rw);


  // Function -- NODOCS -- bus2reg
  //
  // Extensions of this class ~must~ implement this method to copy members
  // of the given bus-specific ~bus_item~ to corresponding members of the provided
  // ~bus_rw~ instance. Unlike <reg2bus>, the resulting transaction
  // is not allocated from scratch. This is to accommodate applications
  // where the bus response must be returned in the original request.

  // @uvm-ieee 1800.2-2017 auto 19.2.1.2.6
  pure virtual function void bus2reg(uvm_sequence_item bus_item,
                                     ref uvm_reg_bus_op rw);


  local uvm_reg_item m_item;

  
  // @uvm-ieee 1800.2-2017 auto 19.2.1.2.7
  virtual function uvm_reg_item get_item();
    return m_item;
  endfunction
  
  virtual function void m_set_item(uvm_reg_item item);
    m_item = item;
  endfunction
endclass


//------------------------------------------------------------------------------
// Group -- NODOCS -- Example
//
// The following example illustrates how to implement a RegModel-BUS adapter class
// for the APB bus protocol.
//
//|class rreg2apb_adapter extends uvm_reg_adapter;
//|  `uvm_object_utils(reg2apb_adapter)
//|
//|  function new(string name="reg2apb_adapter");
//|    super.new(name);
//|    
//|  endfunction
//|
//|  virtual function uvm_sequence_item reg2bus(uvm_reg_bus_op rw);
//|    apb_item apb = apb_item::type_id::create("apb_item");
//|    apb.op   = (rw.kind == UVM_READ) ? apb::READ : apb::WRITE;
//|    apb.addr = rw.addr;
//|    apb.data = rw.data;
//|    return apb;
//|  endfunction
//|
//|  virtual function void bus2reg(uvm_sequencer_item bus_item,
//|                                uvm_reg_bus_op rw);
//|    apb_item apb;
//|    if (!$cast(apb,bus_item)) begin
//|      `uvm_fatal("CONVERT_APB2REG","Bus item is not of type apb_item")
//|    end
//|    rw.kind  = apb.op==apb::READ ? UVM_READ : UVM_WRITE;
//|    rw.addr = apb.addr;
//|    rw.data = apb.data;
//|    rw.status = UVM_IS_OK;
//|  endfunction
//|
//|endclass
//
//------------------------------------------------------------------------------


//------------------------------------------------------------------------------
//
// Class -- NODOCS -- uvm_reg_tlm_adapter
//
// For converting between <uvm_reg_bus_op> and <uvm_tlm_gp> items.
//
//------------------------------------------------------------------------------

// @uvm-ieee 1800.2-2017 auto 19.2.2.1
class uvm_reg_tlm_adapter extends uvm_reg_adapter;

  `uvm_object_utils(uvm_reg_tlm_adapter)

  function new(string name = "uvm_reg_tlm_adapter");
    super.new(name);
  endfunction

  // Function -- NODOCS -- reg2bus
  //
  // Converts a <uvm_reg_bus_op> struct to a <uvm_tlm_gp> item.

  // @uvm-ieee 1800.2-2017 auto 19.2.2.2.1
  virtual function uvm_sequence_item reg2bus(const ref uvm_reg_bus_op rw);

     uvm_tlm_gp gp = uvm_tlm_gp::type_id::create("tlm_gp",, this.get_full_name());
     int nbytes = (rw.n_bits-1)/8+1;
     uvm_reg_addr_t addr=rw.addr;

     if (rw.kind == UVM_WRITE)
        gp.set_command(UVM_TLM_WRITE_COMMAND);
     else
        gp.set_command(UVM_TLM_READ_COMMAND);

     gp.set_address(addr);

     gp.m_byte_enable = new [nbytes];
     gp.m_byte_enable_length = nbytes;

     gp.set_streaming_width (nbytes);

     gp.m_data = new [gp.get_streaming_width()];
     gp.m_length = nbytes; 

     for (int i = 0; i < nbytes; i++) begin
        gp.m_data[i] = rw.data[i*8+:8];
        gp.m_byte_enable[i] = (i > nbytes) ? 8'h00 : (rw.byte_en[i] ? 8'hFF : 8'h00);
     end

     return gp;

  endfunction



  // @uvm-ieee 1800.2-2017 auto 19.2.2.2.2
  virtual function void bus2reg(uvm_sequence_item bus_item,
                                ref uvm_reg_bus_op rw);

    uvm_tlm_gp gp;
    int nbytes;

    if (bus_item == null)
     `uvm_fatal("REG/NULL_ITEM","bus2reg: bus_item argument is null") 

    if (!$cast(gp,bus_item)) begin
      `uvm_error("WRONG_TYPE","Provided bus_item is not of type uvm_tlm_gp")
      return;
    end

    if (gp.get_command() == UVM_TLM_WRITE_COMMAND)
      rw.kind = UVM_WRITE;
    else
      rw.kind = UVM_READ;

    rw.addr = gp.get_address();

    rw.byte_en = 0;
    foreach (gp.m_byte_enable[i])
      rw.byte_en[i] = gp.m_byte_enable[i];

    rw.data = 0;
    foreach (gp.m_data[i])
      rw.data[i*8+:8] = gp.m_data[i];

    rw.status = (gp.is_response_ok()) ? UVM_IS_OK : UVM_NOT_OK;


  endfunction

endclass

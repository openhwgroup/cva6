// 
// Copyright 2021 OpenHW Group
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


`ifndef __UVMA_OBI_REG_ADAPTER_SV__
`define __UVMA_OBI_REG_ADAPTER_SV__


/**
 * Object that converts between abstract register operations (UVM) and
 * Open Bus Interface operations.
 * 
 * Must be overriden by user if there are more than one slave to be selected.
 */
class uvma_obi_reg_adapter_c extends uvml_ral_reg_adapter_c;
   
   `uvm_object_utils(uvma_obi_reg_adapter_c)
   
   
   /**
    * Default constructor
    */
   extern function new(string name="uvma_obi_reg_adapter");
   
   /**
    * Converts from UVM register operation to Open Bus Interface.
    */
   extern virtual function uvm_sequence_item reg2bus(const ref uvm_reg_bus_op rw);
   
   /**
    * Converts from Open Bus Interface to UVM register operation.
    */
   extern virtual function void bus2reg(uvm_sequence_item bus_item, ref uvm_reg_bus_op rw);
   
endclass : uvma_obi_reg_adapter_c


function uvma_obi_reg_adapter_c::new(string name="uvma_obi_reg_adapter");
   
   super.new(name);
   
endfunction : new


function uvm_sequence_item uvma_obi_reg_adapter_c::reg2bus(const ref uvm_reg_bus_op rw);
   
   uvma_obi_mstr_seq_item_c  obi_trn = uvma_obi_mstr_seq_item_c::type_id::create("obi_trn");
   
   obi_trn.access_type = (rw.kind == UVM_READ) ? UVMA_OBI_ACCESS_READ : UVMA_OBI_ACCESS_WRITE;
   obi_trn.address     = rw.addr;
   obi_trn.be          = {(`UVMA_OBI_DATA_MAX_WIDTH/8){1'b1}};
   
   if (rw.kind == UVM_WRITE) begin
      obi_trn.wdata = rw.data;
   end
   
   return obi_trn;
   
endfunction : reg2bus


function void uvma_obi_reg_adapter_c::bus2reg(uvm_sequence_item bus_item, ref uvm_reg_bus_op rw);
   
   uvma_obi_mstr_seq_item_c  obi_trn;
   
   if (!$cast(obi_trn, bus_item)) begin
      `uvm_fatal("OBI", $sformatf("Could not cast bus_item (%s) into obi_trn (%s)", $typename(bus_item), $typename(obi_trn)))
   end
   
   rw.kind = (obi_trn.access_type == UVMA_OBI_ACCESS_READ) ? UVM_READ : UVM_WRITE;
   rw.addr = obi_trn.address;
   
   case (obi_trn.access_type)
      UVMA_OBI_ACCESS_READ : rw.data = obi_trn.rdata;
      UVMA_OBI_ACCESS_WRITE: rw.data = obi_trn.wdata;
      
      default: `uvm_fatal("OBI_MON", $sformatf("Invalid access_type: %0d", obi_trn.access_type))
   endcase
   
   if (obi_trn.__has_error) begin
      rw.status = UVM_NOT_OK;
   end
   else begin
      rw.status = UVM_IS_OK;
   end
   
endfunction : bus2reg


`endif // __UVMA_OBI_REG_ADAPTER_SV__

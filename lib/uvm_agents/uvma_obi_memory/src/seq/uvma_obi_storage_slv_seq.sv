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


`ifndef __UVMA_OBI_STORAGE_SLV_SEQ_SV__
`define __UVMA_OBI_STORAGE_SLV_SEQ_SV__


/**
 * 'slv' sequence that reads back '0' as data, unless the address has been
 * written to.
 */
class uvma_obi_storage_slv_seq_c extends uvma_obi_slv_base_seq_c;
   
   // Fields
   rand longint unsigned  min_address;
   rand longint unsigned  max_address;
   uvma_obi_data_b_t      mem[int unsigned];
   
   
   `uvm_object_utils_begin(uvma_obi_storage_slv_seq_c)
      `uvm_field_int(min_address, UVM_DEFAULT)
      `uvm_field_int(max_address, UVM_DEFAULT)
      `uvm_field_aa_int_int_unsigned(mem, UVM_DEFAULT)
   `uvm_object_utils_end
   
   
   /**
    * Describe defaults_cons
    */
   constraint defaults_cons {
      /*soft*/min_address ==     0;
      /*soft*/max_address == 2**32;
   }
   
   
   /**
    * Default constructor.
    */
   extern function new(string name="uvma_obi_storage_slv_seq");
   
   /**
    * TODO Describe uvma_obi_storage_slv_seq_c::do_response()
    */
   extern virtual task do_response(ref uvma_obi_mon_trn_c mon_req);
   
endclass : uvma_obi_storage_slv_seq_c


function uvma_obi_storage_slv_seq_c::new(string name="uvma_obi_storage_slv_seq");
   
   super.new(name);
   
endfunction : new


task uvma_obi_storage_slv_seq_c::do_response(ref uvma_obi_mon_trn_c mon_req);
   
   uvma_obi_addr_b_t        addr  = 0;
   bit                      error = 0;
   uvma_obi_slv_seq_item_c  _req;
   
   // Ignore malformed requests
   if (mon_req.__has_error) begin
      return;
   end
   
   if (!(mon_req.address inside {[min_address:max_address]})) begin
      error = 1;
   end
   
   for (int unsigned ii=0; ii<cfg.addr_width; ii++) begin
      addr[ii] = mon_req.address[ii];
   end
   case (mon_req.access_type)
      UVMA_OBI_ACCESS_READ: begin
         if (mem.exists(addr)) begin
            // The following code is currently incompatible with xsim (2020.2)
            // Temporary replacement below
            //`uvm_do_with(_req, {
            //   _req.access_type == UVMA_OBI_ACCESS_READ;
            //   _req.err         == error;
            //   foreach (_req.rdata[ii]) {
            //      if (ii < cfg.data_width) {
            //         _req.rdata[ii] == mem[addr][ii];
            //      }
            //   }
            //})
            `uvm_create(_req)
            //if (_req.randomize()) begin
               _req.access_type    = UVMA_OBI_ACCESS_READ;
               _req.err            = error;
               _req.gnt_latency    = 1;
               _req.access_latency = 1;
               _req.hold_duration  = 1;
               _req.tail_length    = 1;
               foreach (_req.rdata[ii]) begin
                  if (ii < cfg.data_width) begin
                     _req.rdata[ii] = mem[addr][ii];
                  end
               end
               `uvm_send(_req)
            //end
            //else begin
            //   `uvm_fatal("OBI_SLV_SEQ", $sformatf("Failed to randomize _req:\n%s", _req.sprint()))
            //end
         end
         else begin
            // The following code is currently incompatible with xsim (2020.2)
            // Temporary replacement below
            //`uvm_do_with(_req, {
            //   _req.access_type == UVMA_OBI_ACCESS_READ;
            //   _req.err         == error;
            //   foreach (_req.rdata[ii]) {
            //      _req.rdata[ii] == 1'b0;
            //   }
            //})
            `uvm_create(_req)
            //if (_req.randomize()) begin
               _req.access_type    = UVMA_OBI_ACCESS_READ;
               _req.err            = error;
               _req.rdata          = 0;
               _req.gnt_latency    = 1;
               _req.access_latency = 1;
               _req.hold_duration  = 1;
               _req.tail_length    = 1;
               `uvm_send(_req)
            //end
            //else begin
            //   `uvm_fatal("OBI_SLV_SEQ", $sformatf("Failed to randomize _req:\n%s", _req.sprint()))
            //end
         end
      end
      
      UVMA_OBI_ACCESS_WRITE: begin
         if (!error) begin
            foreach (mon_req.data[ii]) begin
               if (ii < cfg.data_width) begin
                  mem[addr][ii] = mon_req.data[ii];
               end
            end
         end
         // The following code is currently incompatible with xsim (2020.3)
         // Temporary replacement below
         //`uvm_do_with(_req, {
         //   _req.access_type    == UVMA_OBI_ACCESS_WRITE;
         //   _req.err            == error;
         //   _req.gnt_latency    == 1;
         //   _req.access_latency == 1;
         //   _req.hold_duration  == 1;
         //   _req.tail_length    == 1;
         //})
         `uvm_create(_req)
         _req.access_type    = UVMA_OBI_ACCESS_WRITE;
         _req.err            = error;
         _req.gnt_latency    = 1;
         _req.access_latency = 1;
         _req.hold_duration  = 1;
         _req.tail_length    = 1;
         `uvm_send(_req)
      end
      
      default: `uvm_fatal("OBI_SLV_SEQ", $sformatf("Invalid access_type (%0d):\n%s", mon_req.access_type, mon_req.sprint()))
   endcase
   
endtask : do_response


`endif // __UVMA_OBI_STORAGE_SLV_SEQ_SV__

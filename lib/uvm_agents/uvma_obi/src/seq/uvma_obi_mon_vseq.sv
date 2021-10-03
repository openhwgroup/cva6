// Copyright 2021 OpenHW Group
// Copyright 2021 Datum Technology Corporation
// Copyright 2021 Silicon Labs
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
// Licensed under the Solderpad Hardware License v 2.1 (the "License"); you may not use this file except in compliance
// with the License, or, at your option, the Apache License version 2.0.  You may obtain a copy of the License at
//                                        https://solderpad.org/licenses/SHL-2.1/
// Unless required by applicable law or agreed to in writing, any work distributed under the License is distributed on
// an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.  See the License for the
// specific language governing permissions and limitations under the License.
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////


`ifndef __UVMA_OBI_MON_VSEQ_SV__
`define __UVMA_OBI_MON_VSEQ_SV__


/**
 * TODO Describe uvma_obi_mon_vseq_c
 */
class uvma_obi_mon_vseq_c extends uvma_obi_base_vseq_c;
   
   `uvm_object_utils(uvma_obi_mon_vseq_c)
   
   /**
    * Default constructor.
    */
   extern function new(string name="uvma_obi_mon_vseq");
   
   /**
    * TODO Describe uvma_obi_mon_vseq_c::body()
    */
   extern virtual task body();
   
endclass : uvma_obi_mon_vseq_c


function uvma_obi_mon_vseq_c::new(string name="uvma_obi_mon_vseq");
   
   super.new(name);
   
endfunction : new


task uvma_obi_mon_vseq_c::body();
   
   forever begin
      fork
         begin : chan_a
            wait (cntxt.reset_state == UVML_RESET_STATE_POST_RESET);
            process_chan_a();
         end
         
         begin : chan_r
            wait (cntxt.reset_state == UVML_RESET_STATE_POST_RESET);
            process_chan_r();
         end
         
         begin : reset
            wait (cntxt.reset_state == UVML_RESET_STATE_POST_RESET);
            wait (cntxt.reset_state != UVML_RESET_STATE_POST_RESET);
         end
      join_any
      disable fork;
   end
   
endtask : body


task uvma_obi_mon_vseq_c::process_chan_a();
   
   uvma_obi_mstr_a_mon_trn_c  mstr_a_mon_trn;
   uvma_obi_slv_a_mon_trn_c   slv_a_mon_trn ;
   
   forever begin
      do begin
         fork
            get_mstr_a_mon_trn(mstr_a_mon_trn);
            get_slv_a_mon_trn (slv_a_mon_trn );
         join
      end while ((mstr_a_mon_trn.req !== 1'b1) || (slv_a_mon_trn.gnt !== 1'b1));
      
      cntxt.mon_outstanding_operations.push_back(mstr_a_mon_trn);
      `uvml_hrtbt()
   end
   
endtask : process_chan_a


task uvma_obi_mon_vseq_c::process_chan_r();
   
   uvma_obi_mon_trn_c         mon_trn       ;
   uvma_obi_mstr_a_mon_trn_c  mstr_a_mon_trn;
   uvma_obi_mstr_r_mon_trn_c  mstr_r_mon_trn;
   uvma_obi_slv_r_mon_trn_c   slv_r_mon_trn ;
   
   forever begin
      do begin
         fork
            get_slv_r_mon_trn (slv_r_mon_trn );
            get_mstr_r_mon_trn(mstr_r_mon_trn);
         join
      end while (((slv_r_mon_trn.rvalid !== 1'b1)) || (mstr_r_mon_trn.rready !== 1'b1));
      
      mstr_a_mon_trn = cntxt.mon_outstanding_operations.pop_front();
      mon_trn = uvma_obi_mon_trn_c::type_id::create("mon_trn");
      mon_trn.set_initiator(p_sequencer);
      mon_trn.cfg         = cfg;
      mon_trn.access_type = uvma_obi_access_type_enum'(mstr_a_mon_trn.we);
      mon_trn.address     = mstr_a_mon_trn.addr   ;
      mon_trn.be          = mstr_a_mon_trn.be     ;
      mon_trn.auser       = mstr_a_mon_trn.auser  ;
      mon_trn.wuser       = mstr_a_mon_trn.wuser  ;
      mon_trn.ruser       = slv_r_mon_trn.ruser   ;
      mon_trn.aid         = mstr_a_mon_trn.aid    ;
      mon_trn.rid         = slv_r_mon_trn.rid     ;
      mon_trn.err         = slv_r_mon_trn.err     ;
      mon_trn.exokay      = slv_r_mon_trn.exokay  ;
      mon_trn.atop        = mstr_a_mon_trn.atop   ;
      mon_trn.memtype     = mstr_a_mon_trn.memtype;
      mon_trn.prot        = mstr_a_mon_trn.prot   ;
      mon_trn.achk        = mstr_a_mon_trn.achk   ;
      mon_trn.rchk        = mstr_a_mon_trn.rchk   ;
      if (mstr_a_mon_trn.we) begin
         mon_trn.data = mstr_a_mon_trn.wdata;
      end
      else begin
         mon_trn.data = slv_r_mon_trn.rdata;
      end
      
      `uvml_hrtbt()
      write_mon_trn(mon_trn);
   end
   
endtask : process_chan_r


`endif // __UVMA_OBI_BASE_SEQ_SV__

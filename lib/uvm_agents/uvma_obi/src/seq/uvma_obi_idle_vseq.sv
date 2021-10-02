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


`ifndef __UVMA_OBI_IDLE_VSEQ_SV__
`define __UVMA_OBI_IDLE_VSEQ_SV__


/**
 * TODO Describe uvma_obi_idle_vseq_c
 */
class uvma_obi_idle_vseq_c extends uvma_obi_base_vseq_c;
   
   `uvm_object_utils(uvma_obi_idle_vseq_c)
   
   /**
    * Default constructor.
    */
   extern function new(string name="uvma_obi_idle_vseq");
   
   /**
    * TODO Describe uvma_obi_idle_vseq_c::body()
    */
   extern virtual task body();
   
   /**
    * TODO Describe uvma_obi_idle_vseq_c::do_idle_mstr()
    */
   extern task do_idle_mstr();
   
   /**
    * TODO Describe uvma_obi_idle_vseq_c::do_idle_slv()
    */
   extern task do_idle_slv();
   
   /**
    * TODO Describe uvma_obi_idle_vseq_c::do_idle_mstr_a()
    */
   extern task do_idle_mstr_a();
   
   /**
    * TODO Describe uvma_obi_idle_vseq_c::do_idle_mstr_r()
    */
   extern task do_idle_mstr_r();
   
   /**
    * TODO Describe uvma_obi_idle_vseq_c::do_idle_slv_a()
    */
   extern task do_idle_slv_a();
   
   /**
    * TODO Describe uvma_obi_idle_vseq_c::do_idle_slv_r()
    */
   extern task do_idle_slv_r();
   
endclass : uvma_obi_idle_vseq_c


function uvma_obi_idle_vseq_c::new(string name="uvma_obi_idle_vseq");
   
   super.new(name);
   
endfunction : new


task uvma_obi_idle_vseq_c::body();
   
   case (cfg.mode)
      UVMA_OBI_MODE_MSTR: do_idle_mstr();
      UVMA_OBI_MODE_SLV : do_idle_slv ();
   endcase
   
endtask : body


task uvma_obi_idle_vseq_c::do_idle_mstr();
   
   fork
      begin : chan_a
         forever begin
            do_idle_mstr_a()
         end
      end
      
      begin : chan_r
         forever begin
            do_idle_mstr_r();
         end
      end
   join
   
endtask : do_idle_mstr


task uvma_obi_idle_vseq_c::do_idle_slv();
   
   fork
      begin : chan_a
         forever begin
            do_idle_slv_a();
         end
      end
      
      begin : chan_r
         forever begin
            do_idle_slv_r();
         end
      end
   join
   
endtask : do_idle_slv


task uvma_obi_idle_vseq_c::do_idle_mstr_a();
   
   uvma_obi_mstr_a_seq_item_c  mstr_a_seq_item;
   
   `uvm_create_on(mstr_a_seq_item, p_sequencer.slv_a_sequencer)
   // TODO Add support for cfg.drv_idle
   `uvm_rand_send_pri_with(mstr_a_seq_item, 0, {
      req     == 0;
      addr    == 0;
      we      == 0;
      be      == 0;
      wdata   == 0;
      auser   == 0;
      wuser   == 0;
      aid     == 0;
      atop    == 0;
      memtype == 0;
      prot    == 0;
      achk    == 0;
   })
   
endtask : do_idle_mstr_a


task uvma_obi_idle_vseq_c::do_idle_mstr_r();
   
   uvma_obi_mstr_r_seq_item_c  mstr_r_seq_item;
   
   `uvm_create_on(mstr_r_seq_item, p_sequencer.slv_r_sequencer)
   // TODO Add support for cfg.drv_idle
   `uvm_rand_send_pri_with(mstr_r_seq_item, 0, {
      //rready == 0;
   })
   
endtask : do_idle_mstr_r


task uvma_obi_idle_vseq_c::do_idle_slv_a();
   
   uvma_obi_slv_a_seq_item_c  slv_a_seq_item;
   
   `uvm_create_on(slv_a_seq_item, p_sequencer.slv_a_sequencer)
   // TODO Add support for cfg.drv_idle
   `uvm_rand_send_pri_with(slv_a_seq_item, 0, {
      //gnt == 0;
   })
   
endtask : do_idle_slv_a


task uvma_obi_idle_vseq_c::do_idle_slv_r();
   
   uvma_obi_slv_r_seq_item_c  slv_r_seq_item;
   
   `uvm_create_on(slv_r_seq_item, p_sequencer.slv_r_sequencer)
   // TODO Add support for cfg.drv_idle
   `uvm_rand_send_pri_with(slv_r_seq_item, 0, {
      rvalid    == 0;
      rdata     == 0;
      err       == 0;
      ruser     == 0;
      rid       == 0;
      exokay    == 0;
      rchk      == 0;
   })
   
endtask : do_idle_slv_r


`endif // __UVMA_OBI_BASE_SEQ_SV__

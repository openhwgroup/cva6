// Copyright 2022 Thales DIS SAS
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
// You may obtain a copy of the License at https://solderpad.org/licenses/
//
// Original Author: Alae Eddine EZ ZEJJARI (alae-eddine.ez-zejjari@external.thalesgroup.com)
// Co-Author: Abdelaali Khardazi


`ifndef __UVMA_AXI_VSEQ_SV__
`define __UVMA_AXI_VSEQ_SV__

class uvma_axi_vseq_c extends uvm_sequence;

   // Environment handles
   uvma_axi_cfg_c    cfg;
   uvma_axi_cntxt_c  cntxt;


   `uvm_object_utils(uvma_axi_vseq_c)
   `uvm_declare_p_sequencer(uvma_axi_vsqr_c)


   /**
    * Default constructor.
    */
   extern function new(string name="uvma_axi_vseq");

   /**
    * Retrieve cfg and cntxt handles from p_sequencer.
    */
   extern virtual task pre_start();
   
   
   extern virtual task body();

endclass : uvma_axi_vseq_c


function uvma_axi_vseq_c::new(string name="uvma_axi_vseq");

   super.new(name);

endfunction : new


task uvma_axi_vseq_c::pre_start();

   cfg   = p_sequencer.cfg  ;
   cntxt = p_sequencer.cntxt;

endtask : pre_start

task uvma_axi_vseq_c::body();

   uvma_axi_fw_preload_seq_c   axi_preload_seq;
   axi_preload_seq = uvma_axi_fw_preload_seq_c::type_id::create("axi_preload_seq");
   axi_preload_seq.start(p_sequencer.r_sequencer);
   fork
      begin
         if(cfg.is_active == UVM_ACTIVE) begin
            uvma_axi_aw_seq_c  aw_axi_seq;
            aw_axi_seq = uvma_axi_aw_seq_c::type_id::create("aw_axi_seq");
            aw_axi_seq.start(p_sequencer.aw_sequencer);
         end
      end
      
      begin
         if(cfg.is_active == UVM_ACTIVE) begin
            uvma_axi_w_seq_c  w_axi_seq;
            w_axi_seq = uvma_axi_w_seq_c::type_id::create("w_axi_seq");
            w_axi_seq.start(p_sequencer.w_sequencer);
         end
      end

      begin
         if(cfg.is_active == UVM_ACTIVE) begin
            uvma_axi_ar_seq_c  ar_axi_seq;
            ar_axi_seq = uvma_axi_ar_seq_c::type_id::create("ar_axi_seq");
            ar_axi_seq.start(p_sequencer.ar_sequencer);
         end
      end
      
      begin
         if(cfg.is_active == UVM_ACTIVE) begin
            uvma_axi_r_seq_c  r_axi_seq;
            r_axi_seq = uvma_axi_r_seq_c::type_id::create("r_axi_seq");
            r_axi_seq.start(p_sequencer.r_sequencer);
         end
      end
      
      begin
         if(cfg.is_active == UVM_ACTIVE) begin
            uvma_axi_b_seq_c  b_axi_seq;
            b_axi_seq = uvma_axi_b_seq_c::type_id::create("b_axi_seq");
            b_axi_seq.start(p_sequencer.b_sequencer);
         end
      end
   join_none

endtask : body

`endif // __uvma_axi_vseq_SV__

// Copyright 2022 Thales DIS SAS
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
// You may obtain a copy of the License at https://solderpad.org/licenses/
//
// Original Author: Alae Eddine EZ ZEJJARI (alae-eddine.ez-zejjari@external.thalesgroup.com)


`ifndef __UVMA_AXI_SEQ_LIB_SV__
`define __UVMA_AXI_SEQ_LIB_SV__


`include "uvma_axi_fw_preload_seq.sv"
`include "uvma_axi_ar_seq.sv"
`include "uvma_axi_aw_seq.sv"
`include "uvma_axi_w_seq.sv"
`include "uvma_axi_r_seq.sv"
`include "uvma_axi_b_seq.sv"
`include "uvma_axi_vseq.sv"

/**
 * Object holding sequence library for Open Bus Interface agent.
 */
class uvma_axi_seq_lib_c extends uvm_sequence_library;

   `uvm_object_utils          (uvma_axi_seq_lib_c)
   `uvm_sequence_library_utils(uvma_axi_seq_lib_c)

   /**
    * Initializes sequence library
    */
   extern function new(string name="uvma_axi_seq_lib");
   
endclass : uvma_axi_seq_lib_c


function uvma_axi_seq_lib_c::new(string name="uvma_axi_seq_lib");

   super.new(name);
   init_sequence_library();

endfunction : new

`endif // __UVMA_AXI_SEQ_LIB_SV__


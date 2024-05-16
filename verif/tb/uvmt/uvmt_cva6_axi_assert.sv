// Copyright 2022 Thales DIS SAS
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
// You may obtain a copy of the License at https://solderpad.org/licenses/
//
// Original Author: Alae Eddine EZ ZEJJARI (alae-eddine.ez-zejjari@external.thalesgroup.com) – sub-contractor MU-Electronics for Thales group

// *************************** AXI features supported by CVA6  ************************** //

`include "uvm_macros.svh"

module  uvmt_cva6_axi_assert#(int HPDCache=2)
        (uvma_axi_intf axi_assert_if);

   import uvm_pkg::*;

   //check if the CVA6 identify read transaction with an ID equal to 0 or 1
   property AXI4_CVA6_ARID;
      @(posedge axi_assert_if.clk && (HPDCache != 2)) disable iff (!axi_assert_if.rst_n) axi_assert_if.ar_valid |-> axi_assert_if.ar_id == 0 || axi_assert_if.ar_id == 1 || (axi_assert_if.ar_id == 3 && axi_assert_if.ar_lock == 1);
   endproperty

   //check if the CVA6 identify write transaction with an ID equal to 0 or 1
   property AXI4_CVA6_AWID;
      @(posedge axi_assert_if.clk && (HPDCache != 2)) disable iff (!axi_assert_if.rst_n) axi_assert_if.aw_valid |-> axi_assert_if.aw_id == 1 || (axi_assert_if.aw_id == 3 && axi_assert_if.aw_atop != 0) || (axi_assert_if.aw_id == 3 && axi_assert_if.aw_lock == 1);
   endproperty

   //Check if user-defined extension for read address channel is equal to 0b00
   property AXI4_CVA6_ARUSER;
      @(posedge axi_assert_if.clk) disable iff (!axi_assert_if.rst_n) axi_assert_if.ar_valid |-> axi_assert_if.ar_user == 0;
   endproperty

   //Check if user-defined extension for write address channel is equal to 0b00
   property AXI4_CVA6_AWUSER;
      @(posedge axi_assert_if.clk) disable iff (!axi_assert_if.rst_n) axi_assert_if.aw_valid |-> axi_assert_if.aw_user == 0;
   endproperty

   //Check if Quality of Service identifier for write transaction is equal to 0b0000
   property AXI4_CVA6_AWQOS;
      @(posedge axi_assert_if.clk) disable iff (!axi_assert_if.rst_n) axi_assert_if.aw_valid |-> axi_assert_if.aw_qos == 0;
   endproperty

   //Check if Quality of Service identifier for read transaction is equal to 0b0000
   property AXI4_CVA6_ARQOS;
      @(posedge axi_assert_if.clk) disable iff (!axi_assert_if.rst_n) axi_assert_if.ar_valid |-> axi_assert_if.ar_qos == 0;
   endproperty

   //Check if Region indicator for write transaction is equal to 0b0000
   property AXI4_CVA6_AWREGION;
      @(posedge axi_assert_if.clk) disable iff (!axi_assert_if.rst_n) axi_assert_if.aw_valid |-> axi_assert_if.aw_region == 0;
   endproperty

   //Check if Region indicator for read transaction is equal to 0b0000
   property AXI4_CVA6_ARREGION;
      @(posedge axi_assert_if.clk) disable iff (!axi_assert_if.rst_n) axi_assert_if.ar_valid |-> axi_assert_if.ar_region == 0;
   endproperty

   //Check if AWCACHE is always equal to 0b0000
   property AXI4_CVA6_AWCACHE;
      @(posedge axi_assert_if.clk && (HPDCache != 2)) disable iff (!axi_assert_if.rst_n) axi_assert_if.aw_valid |-> axi_assert_if.aw_cache == 2;
   endproperty

   //Check if ARCACHE is always equal to 0b0000
   property AXI4_CVA6_ARCACHE;
      @(posedge axi_assert_if.clk && (HPDCache != 2)) disable iff (!axi_assert_if.rst_n) axi_assert_if.ar_valid |-> axi_assert_if.ar_cache == 2;
   endproperty

   //Check if Protection attributes for write transaction always take the 0b000
   property AXI4_CVA6_AWPROT;
      @(posedge axi_assert_if.clk) disable iff (!axi_assert_if.rst_n) axi_assert_if.aw_valid |-> axi_assert_if.aw_prot == 0;
   endproperty

   //Check if Protection attributes for read transaction always take the 0b000
   property AXI4_CVA6_ARPROT;
      @(posedge axi_assert_if.clk) disable iff (!axi_assert_if.rst_n) axi_assert_if.ar_valid |-> axi_assert_if.ar_prot == 0;
   endproperty

   //Check if all write transaction performed by CVA6 are of type INCR
   property AXI4_CVA6_AWBURST;
      @(posedge axi_assert_if.clk) disable iff (!axi_assert_if.rst_n) axi_assert_if.aw_valid |-> axi_assert_if.aw_burst == 1;
   endproperty

   //Check if all read transaction performed by CVA6 are of type INCR
   property AXI4_CVA6_ARBURST;
      @(posedge axi_assert_if.clk) disable iff (!axi_assert_if.rst_n) axi_assert_if.ar_valid |-> axi_assert_if.ar_burst == 1;
   endproperty

   //Check if all write transaction performed by CVA6 are equal to 0
   property AXI4_CVA6_AWLEN;
      @(posedge axi_assert_if.clk) disable iff (!axi_assert_if.rst_n) axi_assert_if.aw_valid |-> axi_assert_if.aw_len == 0;
   endproperty

   //Check if all Read transaction performed by CVA6 are equal to 0 or 1
   property AXI4_CVA6_ARLEN;
      @(posedge axi_assert_if.clk) disable iff (!axi_assert_if.rst_n) axi_assert_if.ar_valid |-> axi_assert_if.ar_len == 0 || axi_assert_if.ar_len == 1;
   endproperty

   //Check if all Write transaction performed by CVA6 are of type Non atomic, AtomicLoad or AtomicSwap
   property AXI4_CVA6_AWATOP;
      @(posedge axi_assert_if.clk) disable iff (!axi_assert_if.rst_n) axi_assert_if.aw_valid |-> (axi_assert_if.aw_atop[5:4] == 0 || axi_assert_if.aw_atop[5:4] == 2 || axi_assert_if.aw_atop[5:4] == 3) && axi_assert_if.aw_atop[3] == 0;
   endproperty

/********************************************** Assert Property ******************************************************/

   cva6_arid                : assert property (AXI4_CVA6_ARID)
                         else `uvm_error (" AXI4 protocol checks assertion ", "Violation of AXI4_CVA6_ARID");

   cva6_awid                : assert property (AXI4_CVA6_AWID)
                         else `uvm_error (" AXI4 protocol checks assertion ", "Violation of AXI4_CVA6_AWID");

   cva6_aruser              : assert property (AXI4_CVA6_ARUSER)
                         else `uvm_error (" AXI4 protocol checks assertion ", "Violation of AXI4_CVA6_ARUSER");

   cva6_awuser              : assert property (AXI4_CVA6_AWUSER)
                         else `uvm_error (" AXI4 protocol checks assertion ", "Violation of AXI4_CVA6_AWUSER");

   cva6_arqos               : assert property (AXI4_CVA6_ARQOS)
                         else `uvm_error (" AXI4 protocol checks assertion ", "Violation of AXI4_CVA6_ARQOS");

   cva6_awqos               : assert property (AXI4_CVA6_AWQOS)
                         else `uvm_error (" AXI4 protocol checks assertion ", "Violation of AXI4_CVA6_AWQOS");

   cva6_arregion            : assert property (AXI4_CVA6_ARREGION)
                         else `uvm_error (" AXI4 protocol checks assertion ", "Violation of AXI4_CVA6_ARREGION");

   cva6_awregion            : assert property (AXI4_CVA6_AWREGION)
                         else `uvm_error (" AXI4 protocol checks assertion ", "Violation of AXI4_CVA6_AWREGION");

   cva6_arcache             : assert property (AXI4_CVA6_ARCACHE)
                         else `uvm_error (" AXI4 protocol checks assertion ", "Violation of AXI4_CVA6_ARCAHCE");

   cva6_awcache             : assert property (AXI4_CVA6_AWCACHE)
                         else `uvm_error (" AXI4 protocol checks assertion ", "Violation of AXI4_CVA6_AWCAHCE");

   cva6_arprot              : assert property (AXI4_CVA6_ARPROT)
                         else `uvm_error (" AXI4 protocol checks assertion ", "Violation of AXI4_CVA6_ARPROT");

   cva6_awprot              : assert property (AXI4_CVA6_AWPROT)
                         else `uvm_error (" AXI4 protocol checks assertion ", "Violation of AXI4_CVA6_AWPROT");

   cva6_arburst             : assert property (AXI4_CVA6_ARBURST)
                         else `uvm_error (" AXI4 protocol checks assertion ", "Violation of AXI4_CVA6_ARBURST");

   cva6_awburst             : assert property (AXI4_CVA6_AWBURST)
                         else `uvm_error (" AXI4 protocol checks assertion ", "Violation of AXI4_CVA6_AWBURST");

   cva6_arlen               : assert property (AXI4_CVA6_ARLEN)
                         else `uvm_error (" AXI4 protocol checks assertion ", "Violation of AXI4_CVA6_ARLEN");

   cva6_awlen               : assert property (AXI4_CVA6_AWLEN)
                         else `uvm_error (" AXI4 protocol checks assertion ", "Violation of AXI4_CVA6_AWLEN");

   cva6_awatop              : assert property (AXI4_CVA6_AWATOP)
                         else `uvm_error (" AXI4 protocol checks assertion ", "Violation of AXI4_CVA6_AWATOP");

/********************************************** Cover Property ******************************************************/


   cov_cva6_arid        : cover property(AXI4_CVA6_ARID);

   cov_cva6_awid        : cover property(AXI4_CVA6_AWID);

   cov_cva6_aruser      : cover property(AXI4_CVA6_ARUSER);

   cov_cva6_awuser      : cover property(AXI4_CVA6_AWUSER);

   cov_cva6_arqos       : cover property(AXI4_CVA6_ARQOS);

   cov_cva6_awqos       : cover property(AXI4_CVA6_AWQOS);

   cov_cva6_arregion    : cover property(AXI4_CVA6_ARREGION);

   cov_cva6_awregion    : cover property(AXI4_CVA6_AWREGION);

   cov_cva6_arcache     : cover property(AXI4_CVA6_ARCACHE);

   cov_cva6_awcache     : cover property(AXI4_CVA6_AWCACHE);

   cov_cva6_arprot      : cover property(AXI4_CVA6_ARPROT);

   cov_cva6_awprot      : cover property(AXI4_CVA6_AWPROT);

   cov_cva6_arburst     : cover property(AXI4_CVA6_ARBURST);

   cov_cva6_awburst     : cover property(AXI4_CVA6_AWBURST);

   cov_cva6_arlen       : cover property(AXI4_CVA6_ARLEN);

   cov_cva6_awlen       : cover property(AXI4_CVA6_AWLEN);

   cov_cva6_awatop       : cover property(AXI4_CVA6_AWATOP);


endmodule : uvmt_cva6_axi_assert

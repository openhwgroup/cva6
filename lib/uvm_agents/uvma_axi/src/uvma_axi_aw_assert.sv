// Copyright 2022 Thales DIS SAS
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
// You may obtain a copy of the License at https://solderpad.org/licenses/
//
// Original Author: Alae Eddine EZ ZEJJARI (alae-eddine.ez-zejjari@external.thalesgroup.com)
// Co-Author: Abdelaali Khardazi

// ***************************WRITE ADDRESS CHANNEL ************************** //

module  uvma_axi_aw_assert (uvma_axi_intf.passive axi_assert, input bit clk, input rst_n);

   import uvm_pkg::*;

// *************************** Check if control information Signals are not equal to X or Z when WVALID is HIGH (Section A3.2.2) ************************** //

   property AXI4_AWID_X;
      @(posedge clk) disable iff (!rst_n) axi_assert.psv_axi_cb.aw_valid |-> (!$isunknown(axi_assert.psv_axi_cb.aw_id));
   endproperty

   property AXI4_AWADDR_X;
      @(posedge clk) disable iff (!rst_n) axi_assert.psv_axi_cb.aw_valid |-> (!$isunknown(axi_assert.psv_axi_cb.aw_addr));
   endproperty

   property AXI4_AWLEN_X;
      @(posedge clk) disable iff (!rst_n) axi_assert.psv_axi_cb.aw_valid |-> (!$isunknown(axi_assert.psv_axi_cb.aw_len));
   endproperty

   property AXI4_AWSIZE_X;
      @(posedge clk) disable iff (!rst_n) axi_assert.psv_axi_cb.aw_valid |-> (!$isunknown(axi_assert.psv_axi_cb.aw_size));
   endproperty

   property AXI4_AWBURST_X;
      @(posedge clk) disable iff (!rst_n) axi_assert.psv_axi_cb.aw_valid |-> (!$isunknown(axi_assert.psv_axi_cb.aw_burst));
   endproperty

   property AXI4_AWLOCK_X;
      @(posedge clk) disable iff (!rst_n) axi_assert.psv_axi_cb.aw_valid |-> (!$isunknown(axi_assert.psv_axi_cb.aw_lock));
   endproperty

   property AXI4_AWCACHE_X;
      @(posedge clk) disable iff (!rst_n) axi_assert.psv_axi_cb.aw_valid |-> (!$isunknown(axi_assert.psv_axi_cb.aw_cache));
   endproperty

   property AXI4_AWPROT_X;
      @(posedge clk) disable iff (!rst_n) axi_assert.psv_axi_cb.aw_valid |-> (!$isunknown(axi_assert.psv_axi_cb.aw_prot));
   endproperty

   property AXI4_AWUSER_X;
      @(posedge clk) disable iff (!rst_n) axi_assert.psv_axi_cb.aw_valid |-> (!$isunknown(axi_assert.psv_axi_cb.aw_user));
   endproperty

   property AXI4_AWQOS_X;
      @(posedge clk) disable iff (!rst_n) axi_assert.psv_axi_cb.aw_valid |-> (!$isunknown(axi_assert.psv_axi_cb.aw_qos));
   endproperty

   property AXI4_AWREGION_X;
      @(posedge clk) disable iff (!rst_n) axi_assert.psv_axi_cb.aw_valid |-> (!$isunknown(axi_assert.psv_axi_cb.aw_region));
   endproperty

   // A value of X on AWVALID is not permitted when not in reset (Section A3.1.2)
   property AXI4_AWVALID_X;
      @(posedge clk) disable iff (!rst_n) (!$isunknown(axi_assert.psv_axi_cb.aw_valid));
   endproperty

   // A value of X on AWREADY is not permitted when not in reset (Section A3.1.2)
   property AXI4_AWREADY_X;
      @(posedge clk) disable iff (!rst_n) (!$isunknown(axi_assert.psv_axi_cb.aw_ready));
   endproperty

// *************************** Check if control information Signals are stable when AWVALID is HIGH (Section A3.2.1) ************************** //

   property AXI4_AWID_STABLE;
      @(posedge clk) disable iff (!rst_n) axi_assert.psv_axi_cb.aw_valid |-> (!axi_assert.psv_axi_cb.aw_ready |=> ($stable(axi_assert.psv_axi_cb.aw_id)));
   endproperty

   property AXI4_AWADDR_STABLE;
      @(posedge clk) disable iff (!rst_n) axi_assert.psv_axi_cb.aw_valid |-> (!axi_assert.psv_axi_cb.aw_ready |=> ($stable(axi_assert.psv_axi_cb.aw_addr)));
   endproperty

   property AXI4_AWLEN_STABLE;
      @(posedge clk) disable iff (!rst_n) axi_assert.psv_axi_cb.aw_valid |-> (!axi_assert.psv_axi_cb.aw_ready |=> ($stable(axi_assert.psv_axi_cb.aw_len)));
   endproperty

   property AXI4_AWSIZE_STABLE;
      @(posedge clk) disable iff (!rst_n) axi_assert.psv_axi_cb.aw_valid |-> (!axi_assert.psv_axi_cb.aw_ready |=> ($stable(axi_assert.psv_axi_cb.aw_size)));
   endproperty

   property AXI4_AWBURST_STABLE;
      @(posedge clk) disable iff (!rst_n) axi_assert.psv_axi_cb.aw_valid |-> (!axi_assert.psv_axi_cb.aw_ready |=> ($stable(axi_assert.psv_axi_cb.aw_burst)));
   endproperty

   property AXI4_AWLOCK_STABLE;
      @(posedge clk) disable iff (!rst_n) axi_assert.psv_axi_cb.aw_valid |-> (!axi_assert.psv_axi_cb.aw_ready |=> ($stable(axi_assert.psv_axi_cb.aw_lock)));
   endproperty

   property AXI4_AWCACHE_STABLE;
      @(posedge clk) disable iff (!rst_n) axi_assert.psv_axi_cb.aw_valid |-> (!axi_assert.psv_axi_cb.aw_ready |=> ($stable(axi_assert.psv_axi_cb.aw_cache)));
   endproperty

   property AXI4_AWPROT_STABLE;
      @(posedge clk) disable iff (!rst_n) axi_assert.psv_axi_cb.aw_valid |-> (!axi_assert.psv_axi_cb.aw_ready |=> ($stable(axi_assert.psv_axi_cb.aw_prot)));
   endproperty

   property AXI4_AWUSER_STABLE;
      @(posedge clk) disable iff (!rst_n) axi_assert.psv_axi_cb.aw_valid |-> (!axi_assert.psv_axi_cb.aw_ready |=> ($stable(axi_assert.psv_axi_cb.aw_user)));
   endproperty

   property AXI4_AWQOS_STABLE;
      @(posedge clk) disable iff (!rst_n) axi_assert.psv_axi_cb.aw_valid |-> (!axi_assert.psv_axi_cb.aw_ready |=> ($stable(axi_assert.psv_axi_cb.aw_qos)));
   endproperty

   property AXI4_AWREGION_STABLE;
      @(posedge clk) disable iff (!rst_n) axi_assert.psv_axi_cb.aw_valid |-> (!axi_assert.psv_axi_cb.aw_ready |=> ($stable(axi_assert.psv_axi_cb.aw_region)));
   endproperty

   // Check if, Once asserted, aw_valid must remain asserted until aw_ready is HIGH (Section A3.2.1)
   property AXI4_AW_VALID_READY;
      @(posedge clk) disable iff (!rst_n) axi_assert.psv_axi_cb.aw_valid |-> ( axi_assert.psv_axi_cb.aw_valid throughout (axi_assert.psv_axi_cb.aw_ready [->1]));
   endproperty

   // check if a write transaction with burst type WRAP has an aligned address (Section A3.4.1)
   property AXI_AWADDR_WRAP_ALIGN;
      @(posedge clk) disable iff (!rst_n) (axi_assert.psv_axi_cb.aw_valid && axi_assert.psv_axi_cb.aw_burst == 2'b10) |-> !((axi_assert.psv_axi_cb.aw_addr) % (2**axi_assert.psv_axi_cb.aw_size));
   endproperty

   // check if The size of a write transfer does not exceed the width of the data interface (Section A3.4.1)
   property AXI_ERRM_AWSIZE;
      @(posedge clk) disable iff (!rst_n) axi_assert.psv_axi_cb.aw_valid  |-> (8 * (2**axi_assert.psv_axi_cb.aw_size) <= `UVMA_AXI_DATA_MAX_WIDTH);
   endproperty

   // check if burst crosses 4KB boundaries (Section A3.4.1)
   property AXI4_ERRM_AWADDR_BOUNDARY;
      @(posedge clk) disable iff (!rst_n) axi_assert.psv_axi_cb.aw_valid |-> (((axi_assert.psv_axi_cb.aw_addr + (axi_assert.psv_axi_cb.aw_len + 1) * (2**axi_assert.psv_axi_cb.aw_size)) % 4096) > (axi_assert.psv_axi_cb.aw_addr % 4096)) || !((axi_assert.psv_axi_cb.aw_addr + (axi_assert.psv_axi_cb.aw_len + 1) * (2**axi_assert.psv_axi_cb.aw_size)) % 4096);
   endproperty

   // Check if the burst length equal to 2, 4, 8, or 16, for wrapping bursts (Section A3.4.1)
   property AXI_AWLEN_WRAPP_BURST;
      @(posedge clk) disable iff (!rst_n) (axi_assert.psv_axi_cb.aw_valid && axi_assert.psv_axi_cb.aw_burst == 2'b10) |-> (axi_assert.psv_axi_cb.aw_len == 1) || (axi_assert.psv_axi_cb.aw_len == 3) || (axi_assert.psv_axi_cb.aw_len == 7) || (axi_assert.psv_axi_cb.aw_len == 15);
   endproperty

   // Check if aw_burst can’t be 2’b11 (Table A3-3)
   property AXI4_AW_BURST_CANT_2b11;
      @(posedge clk) disable iff (!rst_n) axi_assert.psv_axi_cb.aw_valid |-> (axi_assert.psv_axi_cb.aw_burst != 2'b11);
   endproperty

   // Check if AWVALID is LOW for the first cycle after ARESETn goes HIGH (Figure A3-1)
   property AXI4_AWVALID_RESET;
      @(posedge clk) $rose(rst_n) |=> !(axi_assert.psv_axi_cb.aw_valid);
   endproperty

   // Check if the length of an exclusive access transaction don't  pass 16 beats (Section A7.2.4)
   property AXI4_AWLEN_LOCK;
      @(posedge clk) disable iff (!rst_n) axi_assert.psv_axi_cb.aw_lock |-> (signed'(axi_assert.psv_axi_cb.aw_len)) <= 16;
   endproperty

   // Check if AWCACHE[3:2] are  LOW, When AWVALID is HIGH and AWCACHE[1] is LOW (Table A4-5)
   property AXI4_AWCACHE_LOW;
      @(posedge clk) disable iff (!rst_n) (axi_assert.psv_axi_cb.aw_valid) && !(axi_assert.psv_axi_cb.aw_cache[1]) |-> !(axi_assert.psv_axi_cb.aw_cache[3:2]);
   endproperty

   // Check if a transactions of burst type FIXED don't have a length greater than 16 beats (Section A3.4.1)
   property AXI4_AWLEN_FIXED;
      @(posedge clk) disable iff (!rst_n) (axi_assert.psv_axi_cb.aw_burst == 2'b00) |-> (axi_assert.psv_axi_cb.aw_len <= 15);
   endproperty

/********************************************** Assert Property ******************************************************/

   aw_valid_aw_ready         : assert property (AXI4_AW_VALID_READY)
                         else `uvm_error (" AXI4 protocol checks assertion ", "Violation of AXI4_AW_VALID_READY");

   awaddr_wrap_align         : assert property (AXI_AWADDR_WRAP_ALIGN)
                         else `uvm_error (" AXI4 protocol checks assertion ", "Violation of AXI_AWADDR_WRAP_ALIGN");

   assert_awsize             : assert property (AXI_ERRM_AWSIZE)
                         else `uvm_error (" AXI4 protocol checks assertion ", "Violation of AXI_ERRM_AWSIZE");

   awlen_wrapp_burst         : assert property (AXI_AWLEN_WRAPP_BURST)
                         else `uvm_error (" AXI4 protocol checks assertion ", "Violation of AXI_AWLEN_WRAPP_BURST");

   aw_burst_cant_2b11        : assert property (AXI4_AW_BURST_CANT_2b11)
                         else `uvm_error (" AXI4 protocol checks assertion ", "Violation of AXI4_AW_BURST_CANT_2b11");

   errm_awaddr_boundary      : assert property (AXI4_ERRM_AWADDR_BOUNDARY)
                         else `uvm_error (" AXI4 protocol checks assertion ", "Violation of AXI4_ERRM_AWADDR_BOUNDARY");

   awvalid_reset             : assert property (AXI4_AWVALID_RESET)
                         else `uvm_error (" AXI4 protocol checks assertion ", "Violation of AXI4_AWVALID_RESET");

   awlen_lock                : assert property (AXI4_AWLEN_LOCK)
                         else `uvm_error (" AXI4 protocol checks assertion ", "Violation of AXI4_AWLEN_LOCK");

   awcahce_low               : assert property (AXI4_AWCACHE_LOW)
                         else `uvm_error (" AXI4 protocol checks assertion ", "Violation of AXI4_AWCACHE_LOW");

   awlen_fixed               : assert property (AXI4_AWLEN_FIXED)
                         else `uvm_error (" AXI4 protocol checks assertion ", "Violation of AXI4_AWLEN_FIXED");

   awid_x                    : assert property (AXI4_AWID_X)
                         else `uvm_error (" AXI4 protocol checks assertion ", "Violation of AXI4_AWID_X");

   awaddr_x                  : assert property (AXI4_AWADDR_X)
                         else `uvm_error (" AXI4 protocol checks assertion ", "Violation of AXI4_AWADDR_X");

   awlen_x                   : assert property (AXI4_AWLEN_X)
                         else `uvm_error (" AXI4 protocol checks assertion ", "Violation of AXI4_AWLEN_X");

   awsize_x                  : assert property (AXI4_AWSIZE_X)
                         else `uvm_error (" AXI4 protocol checks assertion ", "Violation of AXI4_AWSIZE_X");

   awburst_x                 : assert property (AXI4_AWBURST_X)
                         else `uvm_error (" AXI4 protocol checks assertion ", "Violation of AXI4_AWBURST_X");

   awlock_x                  : assert property (AXI4_AWLOCK_X)
                         else `uvm_error (" AXI4 protocol checks assertion ", "Violation of AXI4_AWLOCK_X");

   awcache_x                 : assert property (AXI4_AWCACHE_X)
                         else `uvm_error (" AXI4 protocol checks assertion ", "Violation of AXI4_AWCACHE_X");

   awprot_x                  : assert property (AXI4_AWPROT_X)
                         else `uvm_error (" AXI4 protocol checks assertion ", "Violation of AXI4_AWPROT_X");

   awuser_x                  : assert property (AXI4_AWUSER_X)
                         else `uvm_error (" AXI4 protocol checks assertion ", "Violation of AXI4_AWUSER_X");

   awqos_x                   : assert property (AXI4_AWQOS_X)
                         else `uvm_error (" AXI4 protocol checks assertion ", "Violation of AXI4_AWQOS_X");

   awregion_x                : assert property (AXI4_AWREGION_X)
                         else `uvm_error (" AXI4 protocol checks assertion ", "Violation of AXI4_AWREGION_X");

   awvalid_x                 : assert property (AXI4_AWVALID_X)
                         else `uvm_error (" AXI4 protocol checks assertion ", "Violation of AXI4_AWVALID_X");

   awready_x                 : assert property (AXI4_AWREADY_X)
                         else `uvm_error (" AXI4 protocol checks assertion ", "Violation of AXI4_AWREADY_X");

   awid_stable               : assert property (AXI4_AWID_STABLE)
                         else `uvm_error (" AXI4 protocol checks assertion ", "Violation of AXI4_AWID_STABLE");

   awaddr_stable             : assert property (AXI4_AWADDR_STABLE)
                         else `uvm_error (" AXI4 protocol checks assertion ", "Violation of AXI4_AWADDR_STABLE");

   awlen_stable              : assert property (AXI4_AWLEN_STABLE)
                         else `uvm_error (" AXI4 protocol checks assertion ", "Violation of AXI4_AWLEN_STABLE");

   awsize_stable             : assert property (AXI4_AWSIZE_STABLE)
                         else `uvm_error (" AXI4 protocol checks assertion ", "Violation of AXI4_AWSIZE_STABLE");

   awburst_stable            : assert property (AXI4_AWBURST_STABLE)
                         else `uvm_error (" AXI4 protocol checks assertion ", "Violation of AXI4_AWBURST_STABLE");

   awlock_stable             : assert property (AXI4_AWLOCK_STABLE)
                         else `uvm_error (" AXI4 protocol checks assertion ", "Violation of AXI4_AWLOCK_STABLE");

   awcache_stable            : assert property (AXI4_AWCACHE_STABLE)
                         else `uvm_error (" AXI4 protocol checks assertion ", "Violation of AXI4_AWCACHE_STABLE");

   awprot_stable             : assert property (AXI4_AWPROT_STABLE)
                         else `uvm_error (" AXI4 protocol checks assertion ", "Violation of AXI4_AWPROT_STABLE");

   awuser_stable             : assert property (AXI4_AWUSER_STABLE)
                         else `uvm_error (" AXI4 protocol checks assertion ", "Violation of AXI4_AWUSER_STABLE");

   awqos_stable              : assert property (AXI4_AWQOS_STABLE)
                         else `uvm_error (" AXI4 protocol checks assertion ", "Violation of AXI4_AWQOS_STABLE");

   awregion_stable           : assert property (AXI4_AWREGION_STABLE)
                         else `uvm_error (" AXI4 protocol checks assertion ", "Violation of AXI4_AWREGION_STABLE");

/********************************************** Cover Property ******************************************************/

   cov_aw_valid_aw_ready       : cover property(AXI4_AW_VALID_READY);

   cov_awaddr_wrap_align       : cover property(AXI_AWADDR_WRAP_ALIGN);

   cov_awsize                  : cover property(AXI_ERRM_AWSIZE);

   cov_awvalid_reset           : cover property(AXI4_AWVALID_RESET);

   cov_awlen_wrapp_burst       : cover property(AXI_AWLEN_WRAPP_BURST);

   cov_aw_burst_cant_2b11      : cover property(AXI4_AW_BURST_CANT_2b11);

   cov_errm_awaddr_boundary    : cover property(AXI4_ERRM_AWADDR_BOUNDARY);

   cov_awlen_lock              : cover property(AXI4_AWLEN_LOCK);

   cov_awcache_low             : cover property(AXI4_AWCACHE_LOW);

   cov_awlen_fixed             : cover property(AXI4_AWLEN_FIXED);

   cov_awid_stable             : cover property(AXI4_AWID_STABLE);

   cov_awaddr_stable           : cover property(AXI4_AWADDR_STABLE);

   cov_awlen_stable            : cover property(AXI4_AWLEN_STABLE);

   cov_awsize_stable           : cover property(AXI4_AWSIZE_STABLE);

   cov_awburst_stable          : cover property(AXI4_AWBURST_STABLE);

   cov_awlock_stable           : cover property(AXI4_AWLOCK_STABLE);

   cov_awcache_stable          : cover property(AXI4_AWCACHE_STABLE);

   cov_awprot_stable           : cover property(AXI4_AWPROT_STABLE);

   cov_awuser_stable           : cover property(AXI4_AWUSER_STABLE);

   cov_awqos_stable            : cover property(AXI4_AWQOS_STABLE);

   cov_awregion_stable         : cover property(AXI4_AWREGION_STABLE);


endmodule : uvma_axi_aw_assert

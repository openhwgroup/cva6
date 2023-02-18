// Copyright 2022 Thales DIS SAS
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
// You may obtain a copy of the License at https://solderpad.org/licenses/
//
// Original Author: Alae Eddine EZ ZEJJARI (alae-eddine.ez-zejjari@external.thalesgroup.com)
// Co-Author: Abdelaali Khardazi

// *************************** READ ADDRESS CHANNEL ************************** //

module  uvma_axi_ar_assert (uvma_axi_intf.passive axi_assert, input bit clk, input rst_n);

   import uvm_pkg::*;


// *************************** Check if control information Signals are not equal to X or Z when ARVALID is HIGH (Section A3.2.2) ************************** //

   property AXI4_ARID_X;
      @(posedge clk) disable iff (!rst_n) axi_assert.psv_axi_cb.ar_valid |-> (!$isunknown(axi_assert.psv_axi_cb.ar_id));
   endproperty

   property AXI4_ARADDR_X;
      @(posedge clk) disable iff (!rst_n) axi_assert.psv_axi_cb.ar_valid |-> (!$isunknown(axi_assert.psv_axi_cb.ar_addr));
   endproperty

   property AXI4_ARLEN_X;
      @(posedge clk) disable iff (!rst_n) axi_assert.psv_axi_cb.ar_valid |-> (!$isunknown(axi_assert.psv_axi_cb.ar_len));
   endproperty

   property AXI4_ARSIZE_X;
      @(posedge clk) disable iff (!rst_n) axi_assert.psv_axi_cb.ar_valid |-> (!$isunknown(axi_assert.psv_axi_cb.ar_size));
   endproperty

   property AXI4_ARBURST_X;
      @(posedge clk) disable iff (!rst_n) axi_assert.psv_axi_cb.ar_valid |-> (!$isunknown(axi_assert.psv_axi_cb.ar_burst));
   endproperty

   property AXI4_ARLOCK_X;
      @(posedge clk) disable iff (!rst_n) axi_assert.psv_axi_cb.ar_valid |-> (!$isunknown(axi_assert.psv_axi_cb.ar_lock));
   endproperty

   property AXI4_ARCACHE_X;
      @(posedge clk) disable iff (!rst_n) axi_assert.psv_axi_cb.ar_valid |-> (!$isunknown(axi_assert.psv_axi_cb.ar_cache));
   endproperty

   property AXI4_ARPROT_X;
      @(posedge clk) disable iff (!rst_n) axi_assert.psv_axi_cb.ar_valid |-> (!$isunknown(axi_assert.psv_axi_cb.ar_prot));
   endproperty

   property AXI4_ARUSER_X;
      @(posedge clk) disable iff (!rst_n) axi_assert.psv_axi_cb.ar_valid |-> (!$isunknown(axi_assert.psv_axi_cb.ar_user));
   endproperty

   property AXI4_ARQOS_X;
      @(posedge clk) disable iff (!rst_n) axi_assert.psv_axi_cb.ar_valid |-> (!$isunknown(axi_assert.psv_axi_cb.ar_qos));
   endproperty

   property AXI4_ARREGION_X;
      @(posedge clk) disable iff (!rst_n) axi_assert.psv_axi_cb.ar_valid |-> (!$isunknown(axi_assert.psv_axi_cb.ar_region));
   endproperty

   // A value of X on ARVALID is not permitted when not in reset (Section A3.1.2)
   property AXI4_ARVALID_X;
      @(posedge clk) disable iff (!rst_n) (!$isunknown(axi_assert.psv_axi_cb.ar_valid));
   endproperty

   // A value of X on ARREADY is not permitted when not in reset (Section A3.1.2)
   property AXI4_ARREADY_X;
      @(posedge clk) disable iff (!rst_n) (!$isunknown(axi_assert.psv_axi_cb.ar_ready));
   endproperty

// *************************** Check if control information Signals are stable when ARVALID is HIGH (Section A3.2.1) ************************** //

   property AXI4_ARID_STABLE;
      @(posedge clk) disable iff (!rst_n) axi_assert.psv_axi_cb.ar_valid |-> (!axi_assert.psv_axi_cb.ar_ready |=> ($stable(axi_assert.psv_axi_cb.ar_id)));
   endproperty

   property AXI4_ARADDR_STABLE;
      @(posedge clk) disable iff (!rst_n) axi_assert.psv_axi_cb.ar_valid |-> (!axi_assert.psv_axi_cb.ar_ready |=> ($stable(axi_assert.psv_axi_cb.ar_addr)));
   endproperty

   property AXI4_ARLEN_STABLE;
      @(posedge clk) disable iff (!rst_n) axi_assert.psv_axi_cb.ar_valid |-> (!axi_assert.psv_axi_cb.ar_ready |=> ($stable(axi_assert.psv_axi_cb.ar_len)));
   endproperty

   property AXI4_ARSIZE_STABLE;
      @(posedge clk) disable iff (!rst_n) axi_assert.psv_axi_cb.ar_valid |-> (!axi_assert.psv_axi_cb.ar_ready |=> ($stable(axi_assert.psv_axi_cb.ar_size)));
   endproperty

   property AXI4_ARBURST_STABLE;
      @(posedge clk) disable iff (!rst_n) axi_assert.psv_axi_cb.ar_valid |-> (!axi_assert.psv_axi_cb.ar_ready |=> ($stable(axi_assert.psv_axi_cb.ar_burst)));
   endproperty

   property AXI4_ARLOCK_STABLE;
      @(posedge clk) disable iff (!rst_n) axi_assert.psv_axi_cb.ar_valid |-> (!axi_assert.psv_axi_cb.ar_ready |=> ($stable(axi_assert.psv_axi_cb.ar_lock)));
   endproperty

   property AXI4_ARCACHE_STABLE;
      @(posedge clk) disable iff (!rst_n) axi_assert.psv_axi_cb.ar_valid |-> (!axi_assert.psv_axi_cb.ar_ready |=> ($stable(axi_assert.psv_axi_cb.ar_cache)));
   endproperty

   property AXI4_ARPROT_STABLE;
      @(posedge clk) disable iff (!rst_n) axi_assert.psv_axi_cb.ar_valid |-> (!axi_assert.psv_axi_cb.ar_ready |=> ($stable(axi_assert.psv_axi_cb.ar_prot)));
   endproperty

   property AXI4_ARUSER_STABLE;
      @(posedge clk) disable iff (!rst_n) axi_assert.psv_axi_cb.ar_valid |-> (!axi_assert.psv_axi_cb.ar_ready |=> ($stable(axi_assert.psv_axi_cb.ar_user)));
   endproperty

   property AXI4_ARQOS_STABLE;
      @(posedge clk) disable iff (!rst_n) axi_assert.psv_axi_cb.ar_valid |-> (!axi_assert.psv_axi_cb.ar_ready |=> ($stable(axi_assert.psv_axi_cb.ar_qos)));
   endproperty

   property AXI4_ARREGION_STABLE;
      @(posedge clk) disable iff (!rst_n) axi_assert.psv_axi_cb.ar_valid |-> (!axi_assert.psv_axi_cb.ar_ready |=> ($stable(axi_assert.psv_axi_cb.ar_region)));
   endproperty

   // Check if, Once asserted, ar_valid must remain asserted until ar_ready is HIGH (Section A3.2.1)
   property AXI4_AR_VALID_READY ;
      @(posedge clk) disable iff (!rst_n) axi_assert.psv_axi_cb.ar_valid |-> (axi_assert.psv_axi_cb.ar_valid throughout (axi_assert.psv_axi_cb.ar_ready [->1]));
   endproperty

   // check if a read transaction with burst type WRAP has an aligned address (Section A3.4.1)
   property AXI_ARADDR_WRAP_ALIGN;
      @(posedge clk) disable iff (!rst_n) (axi_assert.psv_axi_cb.ar_valid && axi_assert.psv_axi_cb.ar_burst == 2'b10) |-> !((axi_assert.psv_axi_cb.ar_addr) % (2**axi_assert.psv_axi_cb.ar_size));
   endproperty

   // check if The size of a read transfer does not exceed the width of the data interface (Section A3.4.1)
   property AXI_ERRM_ARSIZE;
      @(posedge clk) disable iff (!rst_n) axi_assert.psv_axi_cb.ar_valid  |-> (8*(2**axi_assert.psv_axi_cb.ar_size) <= `UVMA_AXI_DATA_MAX_WIDTH);
   endproperty

   // check if burst crosses 4KB boundaries (Section A3.4.1)
   property AXI4_ERRM_ARADDR_BOUNDARY;
      @(posedge clk) disable iff (!rst_n) axi_assert.psv_axi_cb.ar_valid |-> (((axi_assert.psv_axi_cb.ar_addr + (axi_assert.psv_axi_cb.ar_len + 1)*(2**axi_assert.psv_axi_cb.ar_size)) % 4096) > (axi_assert.psv_axi_cb.ar_addr % 4096)) || !((axi_assert.psv_axi_cb.ar_addr+(axi_assert.psv_axi_cb.ar_len + 1) * (2**axi_assert.psv_axi_cb.ar_size)) % 4096) ;
   endproperty

   // Check if the burst length equal to 2, 4, 8, or 16, for wrapping bursts (Section A3.4.1)
   property AXI_ARLEN_WRAPP_BURST;
      @(posedge clk) disable iff (!rst_n) (axi_assert.psv_axi_cb.ar_valid && axi_assert.psv_axi_cb.ar_burst == 2'b10) |-> (axi_assert.psv_axi_cb.ar_len == 1) || (axi_assert.psv_axi_cb.ar_len == 3) || (axi_assert.psv_axi_cb.ar_len == 7) || (axi_assert.psv_axi_cb.ar_len == 15);
   endproperty

   // Check if ar_burst can’t be 2’b11 (Table A3-3)
   property AXI4_AR_BURST_CANT_2b11;
      @(posedge clk) disable iff (!rst_n) axi_assert.psv_axi_cb.ar_valid |-> (axi_assert.psv_axi_cb.ar_burst != 2'b11);
   endproperty

   // Check if ARVALID is LOW for the first cycle after ARESETn goes HIGH (Figure A3-1)
   property AXI4_ARVALID_RESET;
      @(posedge clk) $rose(rst_n) |=> !(axi_assert.psv_axi_cb.ar_valid);
   endproperty

   // Check if the length of an exclusive access transaction don't  pass 16 beats (Section A7.2.4)
   property AXI4_ARLEN_LOCK;
      @(posedge clk)  disable iff (!rst_n) axi_assert.psv_axi_cb.ar_lock |-> (signed' (axi_assert.psv_axi_cb.ar_len)) <= 16;
   endproperty

   // Check if ARCACHE[3:2] are  LOW, When ARVALID is HIGH and ARCACHE[1] is LOW (Table A4-5)
   property AXI4_ARCACHE_LOW;
      @(posedge clk)  disable iff (!rst_n) (axi_assert.psv_axi_cb.ar_valid) && !(axi_assert.psv_axi_cb.ar_cache[1]) |-> !(axi_assert.psv_axi_cb.ar_cache[3:2]);
   endproperty

   // Check if a transactions of burst type FIXED don't have a length greater than 16 beats (Section A3.4.1)
   property AXI4_ARLEN_FIXED;
      @(posedge clk)  disable iff (!rst_n) (axi_assert.psv_axi_cb.ar_burst == 2'b00) |-> (axi_assert.psv_axi_cb.ar_len <= 15);
   endproperty

/********************************************** Assert Property ******************************************************/

   ar_valid_ready            : assert property (AXI4_AR_VALID_READY)
                         else `uvm_error (" AXI4 protocol checks assertion ", "Violation of AXI4_AR_VALID_READY");

   arlen_wrapp_burst         : assert property (AXI_ARLEN_WRAPP_BURST)
                         else `uvm_error (" AXI4 protocol checks assertion ", "Violation of AXI_ARLEN_WRAPP_BURST");

   araddr_wrap_align         : assert property (AXI_ARADDR_WRAP_ALIGN)
                         else `uvm_error (" AXI4 protocol checks assertion ", "Violation of AXI_ARADDR_WRAP_ALIGN");

   assert_arsize             : assert property (AXI_ERRM_ARSIZE)
                         else `uvm_error (" AXI4 protocol checks assertion ", "Violation of AXI_ERRM_ARSIZE");

   ar_burst_cant_2b11        : assert property (AXI4_AR_BURST_CANT_2b11)
                         else `uvm_error (" AXI4 protocol checks assertion ", "Violation of AXI4_AR_BURST_CANT_2b11");

   araddr_boundary           : assert property (AXI4_ERRM_ARADDR_BOUNDARY)
                         else `uvm_error (" AXI4 protocol checks assertion ", "Violation of AXI4_ERRM_ARADDR_BOUNDARY");

   arvalid_reset             : assert property (AXI4_ARVALID_RESET)
                         else `uvm_error (" AXI4 protocol checks assertion ", "Violation of AXI4_ARVALID_RESET");

   arlen_lock                : assert property (AXI4_ARLEN_LOCK)
                         else `uvm_error (" AXI4 protocol checks assertion ", "Violation of AXI4_ARLEN_LOCK");

   arcahce_low               : assert property (AXI4_ARCACHE_LOW)
                         else `uvm_error (" AXI4 protocol checks assertion ", "Violation of AXI4_ARCACHE_LOW");

   arlen_fixed               : assert property (AXI4_ARLEN_FIXED)
                         else `uvm_error (" AXI4 protocol checks assertion ", "Violation of AXI4_ARLEN_FIXED");

   arid_x                    : assert property (AXI4_ARID_X)
                         else `uvm_error (" AXI4 protocol checks assertion ", "Violation of AXI4_ARID_X");

   araddr_x                  : assert property (AXI4_ARADDR_X)
                         else `uvm_error (" AXI4 protocol checks assertion ", "Violation of AXI4_ARADDR_X");

   arlen_x                   : assert property (AXI4_ARLEN_X)
                         else `uvm_error (" AXI4 protocol checks assertion ", "Violation of AXI4_ARLEN_X");

   arsize_x                  : assert property (AXI4_ARSIZE_X)
                         else `uvm_error (" AXI4 protocol checks assertion ", "Violation of AXI4_ARSIZE_X");

   arburst_x                 : assert property (AXI4_ARBURST_X)
                         else `uvm_error (" AXI4 protocol checks assertion ", "Violation of AXI4_ARBURST_X");

   arlock_x                  : assert property (AXI4_ARLOCK_X)
                         else `uvm_error (" AXI4 protocol checks assertion ", "Violation of AXI4_ARLOCK_X");

   arcache_x                 : assert property (AXI4_ARCACHE_X)
                         else `uvm_error (" AXI4 protocol checks assertion ", "Violation of AXI4_ARCACHE_X");

   arprot_x                  : assert property (AXI4_ARPROT_X)
                         else `uvm_error (" AXI4 protocol checks assertion ", "Violation of AXI4_ARPROT_X");

   arqos_x                   : assert property (AXI4_ARQOS_X)
                         else `uvm_error (" AXI4 protocol checks assertion ", "Violation of AXI4_ARQOS_X");

   arregion_x                : assert property (AXI4_ARREGION_X)
                         else `uvm_error (" AXI4 protocol checks assertion ", "Violation of AXI4_ARREGION_X");

   arvalid_x                 : assert property (AXI4_ARVALID_X)
                         else `uvm_error (" AXI4 protocol checks assertion ", "Violation of AXI4_ARVALID_X");

   arready_x                 : assert property (AXI4_ARREADY_X)
                         else `uvm_error (" AXI4 protocol checks assertion ", "Violation of AXI4_ARREADY_X");

   arid_stable               : assert property (AXI4_ARID_STABLE)
                         else `uvm_error (" AXI4 protocol checks assertion ", "Violation of AXI4_ARID_STABLE");

   araddr_stable             : assert property (AXI4_ARADDR_STABLE)
                         else `uvm_error (" AXI4 protocol checks assertion ", "Violation of AXI4_ARADDR_STABLE");

   arlen_stable              : assert property (AXI4_ARLEN_STABLE)
                         else `uvm_error (" AXI4 protocol checks assertion ", "Violation of AXI4_ARLEN_STABLE");

   arsize_stable             : assert property (AXI4_ARSIZE_STABLE)
                         else `uvm_error (" AXI4 protocol checks assertion ", "Violation of AXI4_ARSIZE_STABLE");

   arburst_stable            : assert property (AXI4_ARBURST_STABLE)
                         else `uvm_error (" AXI4 protocol checks assertion ", "Violation of AXI4_ARBURST_STABLE");

   arlock_stable             : assert property (AXI4_ARLOCK_STABLE)
                         else `uvm_error (" AXI4 protocol checks assertion ", "Violation of AXI4_ARLOCK_STABLE");

   arcache_stable            : assert property (AXI4_ARCACHE_STABLE)
                         else `uvm_error (" AXI4 protocol checks assertion ", "Violation of AXI4_ARCACHE_STABLE");

   arprot_stable             : assert property (AXI4_ARPROT_STABLE)
                         else `uvm_error (" AXI4 protocol checks assertion ", "Violation of AXI4_ARPROT_STABLE");

   aruser_stable             : assert property (AXI4_ARUSER_STABLE)
                         else `uvm_error (" AXI4 protocol checks assertion ", "Violation of AXI4_ARUSER_STABLE");

   arqos_stable              : assert property (AXI4_ARQOS_STABLE)
                         else `uvm_error (" AXI4 protocol checks assertion ", "Violation of AXI4_ARQOS_STABLE");

   arregion_stable           : assert property (AXI4_ARREGION_STABLE)
                         else `uvm_error (" AXI4 protocol checks assertion ", "Violation of AXI4_ARREGION_STABLE");

/********************************************** Cover Property ******************************************************/

   cov_ar_valid_ar_ready       : cover property(AXI4_AR_VALID_READY);

   cov_araddr_wrap_align       : cover property(AXI_ARADDR_WRAP_ALIGN);

   cov_arlen_wrapp_burst       : cover property(AXI_ARLEN_WRAPP_BURST);

   cov_arsize                  : cover property(AXI_ERRM_ARSIZE);

   cov_arvalid_reset           : cover property(AXI4_ARVALID_RESET);

   cov_ar_burst_cant_2b11      : cover property(AXI4_AR_BURST_CANT_2b11);

   cov_errm_ARaddr_boundary    : cover property(AXI4_ERRM_ARADDR_BOUNDARY);

   cov_arlen_lock              : cover property(AXI4_ARLEN_LOCK);

   cov_arcache_low             : cover property(AXI4_ARCACHE_LOW);

   cov_arlen_fixed             : cover property(AXI4_ARLEN_FIXED);

   cov_arid_stable             : cover property(AXI4_ARID_STABLE);

   cov_araddr_stable           : cover property(AXI4_ARADDR_STABLE);

   cov_arlen_stable            : cover property(AXI4_ARLEN_STABLE);

   cov_arsize_stable           : cover property(AXI4_ARSIZE_STABLE);

   cov_arburst_stable          : cover property(AXI4_ARBURST_STABLE);

   cov_arlock_stable           : cover property(AXI4_ARLOCK_STABLE);

   cov_arcache_stable          : cover property(AXI4_ARCACHE_STABLE);

   cov_arprot_stable           : cover property(AXI4_ARPROT_STABLE);

   cov_aruser_stable           : cover property(AXI4_ARUSER_STABLE);

   cov_arqos_stable            : cover property(AXI4_ARQOS_STABLE);

   cov_arregion_stable         : cover property(AXI4_ARREGION_STABLE);


endmodule : uvma_axi_ar_assert

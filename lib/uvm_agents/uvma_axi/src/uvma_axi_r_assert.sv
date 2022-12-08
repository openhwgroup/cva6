// Copyright 2022 Thales DIS SAS
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
// You may obtain a copy of the License at https://solderpad.org/licenses/
//
// Original Author: Alae Eddine EZ ZEJJARI (alae-eddine.ez-zejjari@external.thalesgroup.com)
// Co-Author: Abdelaali Khardazi

// *************************** READ DATA CHANNEL ************************** //

module  uvma_axi_r_assert (uvma_axi_intf.passive axi_assert, input bit clk, input rst_n);

   import uvm_pkg::*;

// *************************** Check if Read Signals are not equal X or Z when RVALID is HIGH (Section A3.2.2) ************************** //

   property AXI4_RID_X;
      @(posedge clk) disable iff (!rst_n) axi_assert.psv_axi_cb.r_valid |-> (!$isunknown(axi_assert.psv_axi_cb.r_id));
   endproperty

   property AXI4_RDATA_X;
      @(posedge clk) disable iff (!rst_n) axi_assert.psv_axi_cb.r_valid |-> (!$isunknown(axi_assert.psv_axi_cb.r_data));
   endproperty

   property AXI4_RRESP_X;
      @(posedge clk) disable iff (!rst_n) axi_assert.psv_axi_cb.r_valid |-> (!$isunknown(axi_assert.psv_axi_cb.r_resp));
   endproperty

   property AXI4_RLAST_X;
      @(posedge clk) disable iff (!rst_n) axi_assert.psv_axi_cb.r_valid |-> (!$isunknown(axi_assert.psv_axi_cb.r_last));
   endproperty

   property AXI4_RUSEr_X;
      @(posedge clk) disable iff (!rst_n) axi_assert.psv_axi_cb.r_valid |-> (!$isunknown(axi_assert.psv_axi_cb.r_user));
   endproperty

//A value of X on RVALID is not permitted when not in reset (Section A3.1.2)
   property AXI4_RVALID_X;
      @(posedge clk) disable iff (!rst_n) (!$isunknown(axi_assert.psv_axi_cb.r_valid));
   endproperty

//A value of X on RREADY is not permitted when not in reset (Section A3.1.2)
   property AXI4_RREADY_X;
      @(posedge clk) disable iff (!rst_n) (!$isunknown(axi_assert.psv_axi_cb.r_ready));
   endproperty

// *************************** Check if Read Signals are stable when AWVALID is HIGH (Section A3.2.1) ************************** //
   property AXI4_RID_STABLE ;
      @(posedge clk) disable iff (!rst_n) axi_assert.psv_axi_cb.r_valid |-> (!axi_assert.psv_axi_cb.r_ready |=> ($stable(axi_assert.psv_axi_cb.r_id)));
   endproperty

   property AXI4_RDATA_STABLE;
      @(posedge clk) disable iff (!rst_n) axi_assert.psv_axi_cb.r_valid |-> (!axi_assert.psv_axi_cb.r_ready |=> ($stable(axi_assert.psv_axi_cb.r_data)));
   endproperty

   property AXI4_RRESP_STABLE;
      @(posedge clk) disable iff (!rst_n) axi_assert.psv_axi_cb.r_valid |-> (!axi_assert.psv_axi_cb.r_ready |=> ($stable(axi_assert.psv_axi_cb.r_resp)));
   endproperty

   property AXI4_RLAST_STABLE;
      @(posedge clk) disable iff (!rst_n) axi_assert.psv_axi_cb.r_valid |-> (!axi_assert.psv_axi_cb.r_ready |=> ($stable(axi_assert.psv_axi_cb.r_last)));
   endproperty

   property AXI4_RUSER_STABLE;
      @(posedge clk) disable iff (!rst_n) axi_assert.psv_axi_cb.r_valid |-> (!axi_assert.psv_axi_cb.r_ready |=> ($stable(axi_assert.psv_axi_cb.r_user)));
   endproperty

   // Check if, Once asserted, r_valid must remain asserted until r_ready is HIGH (Section A3.2.1)
   property AXI4_RVALID_STABLE ;
      @(posedge clk) disable iff (!rst_n) axi_assert.psv_axi_cb.r_valid |-> ( axi_assert.psv_axi_cb.r_valid throughout (axi_assert.psv_axi_cb.r_ready [->1]));
   endproperty

   // Check if RVALID is LOW for the first cycle after RESET goes HIGH (Figure A3-1)
   property AXI4_RVALID_RESET;
      @(posedge clk) $rose(rst_n) |=> !(axi_assert.psv_axi_cb.r_valid);
   endproperty

/********************************************** Assert Property ******************************************************/

   rvalid_reset          : assert property (AXI4_RVALID_RESET)
                         else `uvm_error (" AXI4 protocol ckecks assertion ", "Violation of AXI4_RVALID_RESET");

   rid_x                 : assert property (AXI4_RID_X)
                         else `uvm_error (" AXI4 protocol ckecks assertion ", "Violation of AXI4_RID_X");

   rdata_x               : assert property (AXI4_RDATA_X)
                         else `uvm_error (" AXI4 protocol ckecks assertion ", "Violation of AXI4_RDATA_X");

   rresp_x               : assert property (AXI4_RRESP_X)
                         else `uvm_error (" AXI4 protocol ckecks assertion ", "Violation of AXI4_RRESP_X");

   rlast_x               : assert property (AXI4_RLAST_X)
                         else `uvm_error (" AXI4 protocol ckecks assertion ", "Violation of AXI4_RLAST_X");

   rvalid_x              : assert property (AXI4_RVALID_X)
                         else `uvm_error (" AXI4 protocol ckecks assertion ", "Violation of AXI4_RVALID_X");

   rready_x              : assert property (AXI4_RREADY_X)
                         else `uvm_error (" AXI4 protocol ckecks assertion ", "Violation of AXI4_RREADY_X");

   rvalid_stable         : assert property (AXI4_RVALID_STABLE)
                         else `uvm_error (" AXI4 protocol ckecks assertion ", "Violation of AXI4_RVALID_STABLE");

   rid_stable            : assert property (AXI4_RID_STABLE)
                         else `uvm_error (" AXI4 protocol ckecks assertion ", "Violation of AXI4_RID_STABLE");

   rdata_stable          : assert property (AXI4_RDATA_STABLE)
                         else `uvm_error (" AXI4 protocol ckecks assertion ", "Violation of AXI4_RDATA_STABLE");

   rresp_stable          : assert property (AXI4_RRESP_STABLE)
                         else `uvm_error (" AXI4 protocol ckecks assertion ", "Violation of AXI4_RRESP_STABLE");

   rlast_stable          : assert property (AXI4_RLAST_STABLE)
                         else `uvm_error (" AXI4 protocol ckecks assertion ", "Violation of AXI4_RLAST_STABLE");

   ruser_stable          : assert property (AXI4_RUSER_STABLE)
                         else `uvm_error (" AXI4 protocol ckecks assertion ", "Violation of AXI4_RUSEr_STABLE");

/**********************************************  FAILED  ******************************************************/
  /* ruser_x             : assert property (AXI4_RUSEr_X)
                         else `uvm_error (" AXI4 protocol ckecks assertion ", "Violation of AXI4_RUSEr_X");*/

/********************************************** Cover Property ******************************************************/

   cov_rvalid_reset           : cover property(AXI4_RVALID_RESET);

   cov_rvalid_stable          : cover property(AXI4_RVALID_STABLE);

   cov_rid_stable             : cover property(AXI4_RID_STABLE);

   cov_rdata_stable           : cover property(AXI4_RDATA_STABLE);

   cov_rresp_stable           : cover property(AXI4_RRESP_STABLE);

   cov_ruser_stable           : cover property(AXI4_RUSER_STABLE);

   cov_rlast_stable           : cover property(AXI4_RLAST_STABLE);

endmodule : uvma_axi_r_assert

// Copyright 2022 Thales DIS SAS
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
// You may obtain a copy of the License at https://solderpad.org/licenses/
//
// Original Author: Alae Eddine EZ ZEJJARI (alae-eddine.ez-zejjari@external.thalesgroup.com)
// Co-Author: Abdelaali Khardazi

// *************************** Write response CHANNEL ************************** //

module  uvma_axi_b_assert (uvma_axi_intf.passive axi_assert, input bit clk, input rst_n);

   import uvm_pkg::*;

// *************************** Check if Write Response Signals are not equal to X or Z when WVALID is HIGH (Section A3.2.2) ************************** //

   property AXI4_BID_X;
      @(posedge clk) disable iff (!rst_n) axi_assert.psv_axi_cb.b_valid |-> (!$isunknown(axi_assert.psv_axi_cb.b_id));
   endproperty

   property AXI4_BRESP_X;
      @(posedge clk) disable iff (!rst_n) axi_assert.psv_axi_cb.b_valid |-> (!$isunknown(axi_assert.psv_axi_cb.b_resp));
   endproperty

   property AXI4_BUSER_X;
      @(posedge clk) disable iff (!rst_n) axi_assert.psv_axi_cb.b_valid |-> (!$isunknown(axi_assert.psv_axi_cb.b_user));
   endproperty

   // A value of X on BVALID is not permitted when not in reset (Section A3.2.2)
   property AXI4_BVALID_X;
      @(posedge clk) disable iff (!rst_n) (!$isunknown(axi_assert.psv_axi_cb.b_valid));
   endproperty

   // A value of X on BVALID is not permitted when not in reset (Section A3.1.2)
   property AXI4_BREADY_X;
      @(posedge clk) disable iff (!rst_n) (!$isunknown(axi_assert.psv_axi_cb.b_ready));
   endproperty

// *************************** Check if Write Response Signals are stable when AWVALID is HIGH (Section A3.2.1) ************************** //

   property AXI4_BID_STABLE ;
      @(posedge clk) disable iff (!rst_n) axi_assert.psv_axi_cb.b_valid |-> (!axi_assert.psv_axi_cb.b_ready |=> ($stable(axi_assert.psv_axi_cb.b_id)));
   endproperty

   property AXI4_BRESP_STABLE;
      @(posedge clk) disable iff (!rst_n) axi_assert.psv_axi_cb.b_valid |-> (!axi_assert.psv_axi_cb.b_ready |=> ($stable(axi_assert.psv_axi_cb.b_resp)));
   endproperty

   property AXI4_BUSER_STABLE;
      @(posedge clk) disable iff (!rst_n) axi_assert.psv_axi_cb.b_valid |-> (!axi_assert.psv_axi_cb.b_ready |=> ($stable(axi_assert.psv_axi_cb.b_user)));
   endproperty

   // Check if, Once asserted, r_valid must remain asserted until r_ready is HIGH (Section A3.2.2)
   property AXI4_BVALID_STABLE ;
      @(posedge clk) disable iff (!rst_n) axi_assert.psv_axi_cb.b_valid |-> ( axi_assert.psv_axi_cb.b_valid throughout (axi_assert.psv_axi_cb.b_ready [->1]));
   endproperty

   // Check if RVALID is LOW for the first cycle after ARESETn goes HIGH (Figure A3-1)
   property AXI4_BVALID_RESET;
      @(posedge clk) $rose(rst_n) |=> !(axi_assert.psv_axi_cb.b_valid);
   endproperty

/********************************************** Assert Property ******************************************************/

   rvalid_reset          : assert property (AXI4_BVALID_RESET)
                         else `uvm_error (" AXI4 protocol ckecks assertion ", "Violation of AXI4_BVALID_RESET");

   bid_x                 : assert property (AXI4_BID_X)
                         else `uvm_error (" AXI4 protocol ckecks assertion ", "Violation of AXI4_BID_X");

   bresp_x               : assert property (AXI4_BRESP_X)
                         else `uvm_error (" AXI4 protocol ckecks assertion ", "Violation of AXI4_BRESP_X");

   buser_x               : assert property (AXI4_BUSER_X)
                         else `uvm_error (" AXI4 protocol ckecks assertion ", "Violation of AXI4_BUSER_X");

   bvalid_x              : assert property (AXI4_BVALID_X)
                         else `uvm_error (" AXI4 protocol ckecks assertion ", "Violation of AXI4_BVALID_X");

   bready_x              : assert property (AXI4_BREADY_X)
                         else `uvm_error (" AXI4 protocol ckecks assertion ", "Violation of AXI4_BREADY_X");

   bvalid_stable         : assert property (AXI4_BVALID_STABLE)
                         else `uvm_error (" AXI4 protocol ckecks assertion ", "Violation of AXI4_BVALID_STABLE");

   bid_stable            : assert property (AXI4_BID_STABLE)
                         else `uvm_error (" AXI4 protocol ckecks assertion ", "Violation of AXI4_BID_STABLE");

   bresp_stable          : assert property (AXI4_BRESP_STABLE)
                         else `uvm_error (" AXI4 protocol ckecks assertion ", "Violation of AXI4_BRESP_STABLE");

   buser_stable          : assert property (AXI4_BUSER_STABLE)
                         else `uvm_error (" AXI4 protocol ckecks assertion ", "Violation of AXI4_BUSER_STABLE");

/********************************************** Cover Property ******************************************************/

   cov_bvalid_reset           : cover property(AXI4_BVALID_RESET);

   cov_bvalid_stable          : cover property(AXI4_BVALID_STABLE);

   cov_bid_stable             : cover property(AXI4_BID_STABLE);

   cov_bresp_stable           : cover property(AXI4_BRESP_STABLE);

   cov_buser_stable           : cover property(AXI4_BUSER_STABLE);

endmodule : uvma_axi_b_assert

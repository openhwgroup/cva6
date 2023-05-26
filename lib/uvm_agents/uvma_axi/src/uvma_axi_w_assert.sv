// Copyright 2022 Thales DIS SAS
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
// You may obtain a copy of the License at https://solderpad.org/licenses/
//
// Original Author: Alae Eddine EZ ZEJJARI (alae-eddine.ez-zejjari@external.thalesgroup.com)
// Co-Author: Abdelaali Khardazi

// *************************** WRITE DATA CHANNEL ************************** //

module  uvma_axi_w_assert (uvma_axi_intf.passive axi_assert, input bit clk, input rst_n);

   import uvm_pkg::*;

// *************************** Check if Write Signals are not equal to X or Z when WVALID is HIGH  (Section A3.2.2)************************** //

   property AXI4_WDATA_X;
      @(posedge clk) disable iff (!rst_n) axi_assert.psv_axi_cb.w_valid |-> (!$isunknown(axi_assert.psv_axi_cb.w_data));
   endproperty

   property AXI4_WSTRB_X;
      @(posedge clk) disable iff (!rst_n) axi_assert.psv_axi_cb.w_valid |-> (!$isunknown(axi_assert.psv_axi_cb.w_strb));
   endproperty

   property AXI4_WLAST_X;
      @(posedge clk) disable iff (!rst_n) axi_assert.psv_axi_cb.w_valid |-> (!$isunknown(axi_assert.psv_axi_cb.w_last));
   endproperty

   property AXI4_WUSER_X;
      @(posedge clk) disable iff (!rst_n) axi_assert.psv_axi_cb.w_valid |-> (!$isunknown(axi_assert.psv_axi_cb.w_user));
   endproperty

   // A value of X on WVALID is not permitted when not in reset (Section A3.1.2)
   property AXI4_WVALID_X;
      @(posedge clk) disable iff (!rst_n) (!$isunknown(axi_assert.psv_axi_cb.w_valid));
   endproperty

   // A value of X on WREADY is not permitted when not in reset (Section A3.1.2)
   property AXI4_WREADY_X;
      @(posedge clk) disable iff (!rst_n) (!$isunknown(axi_assert.psv_axi_cb.w_ready));
   endproperty

// *************************** Check if Write Signals are stable when AWVALID is HIGH (Section A3.2.1) ************************** //

   property AXI4_WDATA_STABLE;
      @(posedge clk) disable iff (!rst_n) axi_assert.psv_axi_cb.w_valid |-> (!axi_assert.psv_axi_cb.w_ready |=> ($stable(axi_assert.psv_axi_cb.w_data)));
   endproperty

   property AXI4_WSTRB_STABLE;
      @(posedge clk) disable iff (!rst_n) axi_assert.psv_axi_cb.w_valid |-> (!axi_assert.psv_axi_cb.w_ready |=> ($stable(axi_assert.psv_axi_cb.w_strb)));
   endproperty

   property AXI4_WLAST_STABLE;
      @(posedge clk) disable iff (!rst_n) axi_assert.psv_axi_cb.w_valid |-> (!axi_assert.psv_axi_cb.w_ready |=> ($stable(axi_assert.psv_axi_cb.w_last)));
   endproperty

   property AXI4_WUSER_STABLE;
      @(posedge clk) disable iff (!rst_n) axi_assert.psv_axi_cb.w_valid |-> (!axi_assert.psv_axi_cb.w_ready |=> ($stable(axi_assert.psv_axi_cb.w_user)));
   endproperty

   // Check if, Once asserted, w_valid must remain asserted until w_ready is HIGH (Section A3.2.1)
   property AXI4_WVALID_STABLE ;
      @(posedge clk) disable iff (!rst_n) axi_assert.psv_axi_cb.w_valid |-> ( axi_assert.psv_axi_cb.w_valid throughout (axi_assert.psv_axi_cb.w_ready [->1]));
   endproperty

   //Check if WVALID is LOW for the first cycle after ARESETn goes HIGH (Figure A3-1)
   property AXI4_WVALID_RESET;
      @(posedge clk) $rose(rst_n) |=> !(axi_assert.psv_axi_cb.w_valid);
   endproperty

/********************************************** Assert Property ******************************************************/

   wvalid_reset          : assert property (AXI4_WVALID_RESET)
                         else `uvm_error (" AXI4 protocol ckecks assertion ", "Violation of AXI4_WVALID_RESET");

   wdata_x               : assert property (AXI4_WDATA_X)
                         else `uvm_error (" AXI4 protocol ckecks assertion ", "Violation of AXI4_WDATA_X");

   wstrb_x               : assert property (AXI4_WSTRB_X)
                         else `uvm_error (" AXI4 protocol ckecks assertion ", "Violation of AXI4_WSTRB_X");

   wlast_x               : assert property (AXI4_WLAST_X)
                         else `uvm_error (" AXI4 protocol ckecks assertion ", "Violation of AXI4_WLAST_X");

   wuser_x               : assert property (AXI4_WUSER_X)
                         else `uvm_error (" AXI4 protocol ckecks assertion ", "Violation of AXI4_WUSER_X");

   wvalid_x              : assert property (AXI4_WVALID_X)
                         else `uvm_error (" AXI4 protocol ckecks assertion ", "Violation of AXI4_WVALID_X");

   wready_x              : assert property (AXI4_WREADY_X)
                         else `uvm_error (" AXI4 protocol ckecks assertion ", "Violation of AXI4_WREADY_X");

   wvalid_stable         : assert property (AXI4_WVALID_STABLE)
                         else `uvm_error (" AXI4 protocol ckecks assertion ", "Violation of AXI4_WVALID_STABLE");

   wdata_stable          : assert property (AXI4_WDATA_STABLE)
                         else `uvm_error (" AXI4 protocol ckecks assertion ", "Violation of AXI4_WDATA_STABLE");

   wstrb_stable          : assert property (AXI4_WSTRB_STABLE)
                         else `uvm_error (" AXI4 protocol ckecks assertion ", "Violation of AXI4_WSTRB_STABLE");

   wlast_stable          : assert property (AXI4_WLAST_STABLE)
                         else `uvm_error (" AXI4 protocol ckecks assertion ", "Violation of AXI4_WLAST_STABLE");

   wuser_stable          : assert property (AXI4_WUSER_STABLE)
                         else `uvm_error (" AXI4 protocol ckecks assertion ", "Violation of AXI4_WUSER_STABLE");

/********************************************** Cover Property ******************************************************/

   cov_wvalid_reset           : cover property(AXI4_WVALID_RESET);

   cov_wvalid_stable          : cover property(AXI4_WVALID_STABLE);

   cov_wdata_stable           : cover property(AXI4_WDATA_STABLE);

   cov_wstrb_stable           : cover property(AXI4_WSTRB_STABLE);

   cov_wuser_stable           : cover property(AXI4_WUSER_STABLE);

   cov_wlast_stable           : cover property(AXI4_WLAST_STABLE);

endmodule : uvma_axi_w_assert

// Copyright 2021 Thales DIS design services SAS
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
// You may obtain a copy of the License at https://solderpad.org/licenses/
//
// Original Author: Zineb EL KACIMI (zineb.el-kacimi@external.thalesgroup.com)

/**
 * Encapsulates assertions targeting uvma_cvxif_intf.
 */
module uvma_cvxif_assert #(parameter X_ID_WIDTH = cvxif_pkg::X_ID_WIDTH)
   (uvma_cvxif_intf cvxif_assert,
    input bit clk
   );

   import uvm_pkg::*;

   // ---------------------------------------------------------------------------
    // Local variables
   // ---------------------------------------------------------------------------
   string info_tag = "CVXIF_ASSERT";

   // ---------------------------------------------------------------------------
    // Begin module code
   // ---------------------------------------------------------------------------

   /**
    * Issue_interface
   */
   property p_issue_resp_null_when_n_accept;
      @(posedge clk) (cvxif_assert.cvxif_req_i.x_issue_valid && !cvxif_assert.cvxif_resp_o.x_issue_resp.accept)
                     |-> (!cvxif_assert.cvxif_resp_o.x_issue_resp.writeback && !cvxif_assert.cvxif_resp_o.x_issue_resp.dualread
                          && !cvxif_assert.cvxif_resp_o.x_issue_resp.loadstore && !cvxif_assert.cvxif_resp_o.x_issue_resp.exc);
   endproperty

   a_issue_resp_null_when_n_accept:assert property (p_issue_resp_null_when_n_accept)
      else `uvm_error(info_tag, "Failure:  writeback ; dualwrite ; dualread; loadstore; exc; shall be equal to 0");
   c_issue_resp_null_when_n_accept:cover property (p_issue_resp_null_when_n_accept);

   /**
    * Commit_interface
   */
   property p_commit_valid_pulse;
      bit [X_ID_WIDTH-1:0] id;
      @(posedge clk) (cvxif_assert.cvxif_req_i.x_commit_valid, id=cvxif_assert.cvxif_req_i.x_commit.id)
                    |=> !(cvxif_assert.cvxif_req_i.x_commit_valid && cvxif_assert.cvxif_req_i.x_commit.id==id);
   endproperty
   a_commit_valid_pulse:assert property (p_commit_valid_pulse)
      else `uvm_error(info_tag, "Failure: commit_valid is asserted more than 1 cycle");

   property p_issue_commit;
      bit [X_ID_WIDTH-1:0] id;
      @(posedge clk) ((cvxif_assert.cvxif_resp_o.x_issue_ready && cvxif_assert.cvxif_req_i.x_issue_valid), id=cvxif_assert.cvxif_req_i.x_issue_req.id)
                     |-> (s_eventually (cvxif_assert.cvxif_req_i.x_commit_valid && cvxif_assert.cvxif_req_i.x_commit.id==id));
   endproperty
   a_issue_commit:assert property (p_issue_commit)
      else `uvm_error(info_tag, "Failure: for every issue transaction, a commit transaction shall present ");


   /**
    * Result_interface
   */
   property p_sync_exc;
      @(posedge clk) cvxif_assert.cvxif_resp_o.x_result.exc |-> !cvxif_assert.cvxif_resp_o.x_result.we;
   endproperty
   a_sync_exc:assert property (p_sync_exc)
      else `uvm_error(info_tag, "Failure: 'we' shall be driven to 0 by the Coprocessor for synchronous exceptions");
   c_sync_exc:cover property (p_sync_exc);


endmodule : uvma_cvxif_assert




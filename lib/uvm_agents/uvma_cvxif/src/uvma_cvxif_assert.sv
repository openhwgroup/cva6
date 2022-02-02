// Copyright 2021 Thales DIS design services SAS
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
// You may obtain a copy of the License at https://solderpad.org/licenses/
//
// Original Author: Zineb EL KACIMI (zineb.el-kacimi@external.thalesgroup.com)

/**
 * Encapsulates assertions targeting uvma_cvxif_if.
 */
module uvma_cvxif_assert #(parameter X_ID_WIDTH = cvxif_pkg::X_ID_WIDTH)
   (uvma_cvxif_if cvxif_assert,
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
   property IssueRespNull_when_Naccept;
      @(posedge clk) (cvxif_assert.cvxif_req_i.x_issue_valid && !cvxif_assert.cvxif_resp_o.x_issue_resp.accept)
                     |-> (!cvxif_assert.cvxif_resp_o.x_issue_resp.writeback && !cvxif_assert.cvxif_resp_o.x_issue_resp.dualread
                          && !cvxif_assert.cvxif_resp_o.x_issue_resp.loadstore && !cvxif_assert.cvxif_resp_o.x_issue_resp.exc);
   endproperty

   ASSERT_IssueRespNull:assert property (IssueRespNull_when_Naccept)
   else `uvm_error(info_tag, "Failure:  writeback ; dualwrite ; dualread; loadstore; exc; shall be equal to 0");
   COV_IssueRespNull:cover property (IssueRespNull_when_Naccept);

   /**
    * Commit_interface
   */
   property commit_valid_pulse;
     bit [X_ID_WIDTH-1:0] id;
     @(posedge clk) (cvxif_assert.cvxif_req_i.x_commit_valid, id=cvxif_assert.cvxif_req_i.x_commit.id)
                    |=> !(cvxif_assert.cvxif_req_i.x_commit_valid && cvxif_assert.cvxif_req_i.x_commit.id==id);
   endproperty
   ASSERT_COMMIT_VALID_PULSE:assert property (commit_valid_pulse)
   else `uvm_error(info_tag, "Failure: commit_valid is asserted more than 1 cycle");

    property issue_commit ;
      bit [X_ID_WIDTH-1:0] id;
      @(posedge clk) ((cvxif_assert.cvxif_resp_o.x_issue_ready && cvxif_assert.cvxif_req_i.x_issue_valid), id=cvxif_assert.cvxif_req_i.x_issue_req.id)
                     |-> (s_eventually (cvxif_assert.cvxif_req_i.x_commit_valid && cvxif_assert.cvxif_req_i.x_commit.id==id));
    endproperty
    ASSERT_ISSUE_COMMIT:assert property (issue_commit)
    else `uvm_error(info_tag, "Failure: for every issue transaction, a commit transaction shall present ");


   /**
    * Result_interface
   */
    property synchronious_exception ;
      @(posedge clk) cvxif_assert.cvxif_resp_o.x_result.exc |-> !cvxif_assert.cvxif_resp_o.x_result.we;
    endproperty
    ASSERT_SYC_EX:assert property (synchronious_exception)
    else `uvm_error(info_tag, "Failure: 'we' shall be driven to 0 by the Coprocessor for synchronous exceptions");
    COV_SYC_EX:cover property (synchronious_exception);

endmodule : uvma_cvxif_assert




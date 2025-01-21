// Copyright 2025 Thales DIS France SAS
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     https://solderpad.org/licenses/
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0

`ifndef __UVMT_WORKFLOW_PKG_SV__
`define __UVMT_WORKFLOW_PKG_SV__

/**
 * Variable to customize testbench in function of tools and step in workflow
 */
package uvmt_workflow_pkg;

   parameter logic gate_simulation = 1;

endpackage : uvmt_workflow_pkg

`endif // __UVMT_WORKFLOW_PKG_SV__

// Copyright 2020 OpenHW Group
// Copyright 2020 Datum Technology Corporation
// Copyright 2020 Silicon Labs, Inc.
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


`ifndef __UVMA_FENCEI_IF_SV__
`define __UVMA_FENCEI_IF_SV__

/**
 * Encapsulates all signals and clocking of FENCEI flush request/acknowledge interface
 */
interface uvma_fencei_if
  import uvma_fencei_pkg::*;
  (
    input                      clk,
    input                      reset_n
  );

  // -------------------------------------------------------------------
  // Interface signals
  // -------------------------------------------------------------------
  wire flush_req;
  wire flush_ack;

  // -------------------------------------------------------------------
  // Local variables
  // -------------------------------------------------------------------

  // -------------------------------------------------------------------
  // Begin module code
  // -------------------------------------------------------------------

  clocking drv_mst_cb @(posedge clk or reset_n);
    input  #1step flush_ack;
    output        flush_req;
  endclocking : drv_mst_cb

  clocking drv_slv_cb @(posedge clk or reset_n);
    input  #1step flush_req;
    input  #1step output flush_ack;
  endclocking : drv_slv_cb

  clocking mon_cb @(posedge clk or reset_n);
    input  #1step flush_req,
                  flush_ack;
  endclocking : mon_cb

endinterface : uvma_fencei_if


`endif // __UVMA_FENCEI_IF_SV__

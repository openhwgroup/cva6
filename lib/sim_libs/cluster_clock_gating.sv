// Copyright 2020 OpenHW Group
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
///////////////////////////////////////////////////////////////////////////////
//
// Copyright 2017 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
///////////////////////////////////////////////////////////////////////////////
//
// This is a simulation-only model of a clock-gating cell.  It is intended to
// be used ONLY for simulation, and will generate a warning message to that
// effect.  It _should_ fail to compile for synthesis.
//
///////////////////////////////////////////////////////////////////////////////

`ifndef VERILATOR
`include "uvm_pkg.sv"
import uvm_pkg::*;
`endif

module cluster_clock_gating
(
    input  logic clk_i,
    input  logic en_i,
    input  logic test_en_i,
    output logic clk_o
  );

`ifndef __USE_COREV_SIMULATION_MODELS__
  // This module should only be used in simulation
  // Deliberately create a compiler error
  bitter this_is_a_simulation_model_only;
`endif

`ifndef VERILATOR
initial `uvm_warning("cluster_clock_gating", "You are using CLUSTER_CLOCK_GATING, an unsanctioned simulation model!")
`else
initial $write("!!!\n!!! %m: t=%0t\n!!! WARNING!!! You are using CLUSTER_CLOCK_GATING, an unsanctioned simulation model\n!!!\n", $time);
`endif

`ifdef PULP_FPGA_EMUL
  // no clock gates in FPGA flow
  assign clk_o = clk_i;
`else
  logic clk_en;

  always_latch
  begin
     if (clk_i == 1'b0)
       clk_en <= en_i | test_en_i;
  end

  assign clk_o = clk_i & clk_en;
`endif

endmodule // cluster_clock_gating

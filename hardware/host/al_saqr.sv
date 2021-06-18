// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// Author: Luca Valente, University of Bologna
// Date: 18.06.2021
// Description: AlSaqr platform, it holds host_domain and cluster

module al_saqr 
  import axi_pkg::xbar_cfg_t;
#(
  parameter int unsigned AXI_USER_WIDTH    = 1,
  parameter int unsigned AXI_ADDRESS_WIDTH = 64,
  parameter int unsigned AXI_DATA_WIDTH    = 64,
`ifdef DROMAJO
  parameter bit          InclSimDTM        = 1'b0,
`else
  parameter bit          InclSimDTM        = 1'b1,
`endif
  parameter int unsigned NUM_WORDS         = 2**25,         // memory size
  parameter bit          StallRandomOutput = 1'b0,
  parameter bit          StallRandomInput  = 1'b0
) (
  input  logic                           clk_i,
  input  logic                           rtc_i,
  input  logic                           rst_ni,
  output logic [31:0]                    exit_o
);

   
    host_domain #(
        .NUM_WORDS         ( NUM_WORDS ),
        .InclSimDTM        ( 1'b1      ),
        .StallRandomOutput ( 1'b1      ),
        .StallRandomInput  ( 1'b1      )
    ) i_host_domain (
        .clk_i,
        .rst_ni,
        .rtc_i,
        .exit_o
    );


endmodule

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
// Author: Luca Valente
// Description: Contains SoC information as constants

package apb_soc_pkg;

   typedef struct packed {
      logic [31:0] idx;
      logic [31:0] start_addr;
      logic [31:0] end_addr;
   } addr_map_rule_t;

   localparam NUM_APB_SLAVES = 2;
   
     
   localparam logic [31:0] UDMALength    = 32'h2000;
   localparam logic [31:0] EVNTGENLength = 32'h1000;
  
   
   typedef enum logic [31:0] {
     UDMABase     = 32'hC100_0000,
     EVNTGENBase  = 32'hC100_2000
    } soc_apb_bus_start_t;
   
endpackage

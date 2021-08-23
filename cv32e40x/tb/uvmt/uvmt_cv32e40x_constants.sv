//
// Copyright 2020 OpenHW Group
// Copyright 2020 Datum Technology Corporation
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

`ifndef __UVMT_CV32E40X_CONSTANTS_SV__
`define __UVMT_CV32E40X_CONSTANTS_SV__


   `ifdef PMA_CUSTOM_CFG
      parameter int unsigned               CORE_PARAM_PMA_NUM_REGIONS = 3;
      parameter cv32e40x_pkg::pma_region_t CORE_PARAM_PMA_CFG[CORE_PARAM_PMA_NUM_REGIONS-1:0] = '{
         // Overlap "shadow" of main code (.text), for testing overlap priority
         cv32e40x_pkg::pma_region_t'{
            word_addr_low  : '0,
            word_addr_high : ('h 1a11_0800 + 'd 16) >> 2,  // should be identical to the prioritized region below
            main           : 0,  // Would stop all execution, but should be overruled
            bufferable     : 0,
            cacheable      : 0,
            atomic         : 0},
         // Main code (.text) is executable up til into dbg region
         cv32e40x_pkg::pma_region_t'{
            word_addr_low  : '0,
            word_addr_high : ('h 1a11_0800 + 'd 16) >> 2,  // "dbg" address plus arbitrary offset to have a known usable area
            main           : 1,
            bufferable     : 1,
            cacheable      : 1,
            atomic         : 1},
         // Second portion of dbg up til end is exec
         cv32e40x_pkg::pma_region_t'{
            word_addr_low  : 'h 1A11_1000 >> 2,  // after ".debugger"
            word_addr_high : 'h FFFF_FFFF,
            main           : 1,
            bufferable     : 0,
            cacheable      : 0,
            atomic         : 1}
         };
   `elsif PMA_DEBUG_CFG
      parameter int unsigned               CORE_PARAM_PMA_NUM_REGIONS = 2;
      parameter cv32e40x_pkg::pma_region_t CORE_PARAM_PMA_CFG[CORE_PARAM_PMA_NUM_REGIONS-1:0] = '{
         // Everything is initially executable
         cv32e40x_pkg::pma_region_t'{
            word_addr_low  : '0,
            word_addr_high : 'h FFFF_FFFF,
            main           : 1,
            bufferable     : 0,
            cacheable      : 0,
            atomic         : 1},
         // A small region below "dbg" is forbidden to facilitate pma exception testing
         cv32e40x_pkg::pma_region_t'{
            word_addr_low  : ('h 1a11_0800 - 'd 16) >> 2,
            word_addr_high : 'h 1a11_0800 >> 2,
            main           : 0,
            bufferable     : 0,
            cacheable      : 0,
            atomic         : 0}
         };
   `else
      parameter int                        CORE_PARAM_PMA_NUM_REGIONS = 0;
      parameter cv32e40x_pkg::pma_region_t CORE_PARAM_PMA_CFG[-1:0] =  '{default:cv32e40x_pkg::PMA_R_DEFAULT};
   `endif


`endif // __UVMT_CV32E40X_CONSTANTS_SV__

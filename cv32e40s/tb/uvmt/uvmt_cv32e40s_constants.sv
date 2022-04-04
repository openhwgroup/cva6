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

`ifndef __UVMT_CV32E40S_CONSTANTS_SV__
`define __UVMT_CV32E40S_CONSTANTS_SV__

   `ifdef ZBA_ZBB_ZBS
      parameter cv32e40s_pkg::b_ext_e B_EXT = cv32e40s_pkg::ZBA_ZBB_ZBS;
   `elsif ZBA_ZBB_ZBC_ZBS
      parameter cv32e40s_pkg::b_ext_e B_EXT = cv32e40s_pkg::ZBA_ZBB_ZBC_ZBS;
   `else
      parameter cv32e40s_pkg::b_ext_e B_EXT = cv32e40s_pkg::B_NONE;
   `endif

   `ifdef PMP_ENABLE_2
     parameter int CORE_PARAM_PMP_NUM_REGIONS = 2;
   `else
     parameter int CORE_PARAM_PMP_NUM_REGIONS = 0;
   `endif

   `ifdef PMA_CUSTOM_CFG
      const string pma_cfg_name = "pma_custom_cfg";
      parameter int unsigned               CORE_PARAM_PMA_NUM_REGIONS = 3;
      parameter cv32e40s_pkg::pma_region_t CORE_PARAM_PMA_CFG[CORE_PARAM_PMA_NUM_REGIONS-1:0] = '{
         // Overlap "shadow" of main code (.text), for testing overlap priority
         cv32e40s_pkg::pma_region_t'{
            word_addr_low  : '0,
            word_addr_high : ('h 1a11_0800 + 'd 16) >> 2,  // should be identical to the prioritized region below
            main           : 0,  // Would stop all execution, but should be overruled
            bufferable     : 0,
            cacheable      : 0},
         // Main code (.text) is executable up til into dbg region
         cv32e40s_pkg::pma_region_t'{
            word_addr_low  : '0,
            word_addr_high : ('h 1a11_0800 + 'd 16) >> 2,  // "dbg" address plus arbitrary offset to have a known usable area
            main           : 1,
            bufferable     : 1,
            cacheable      : 1},
         // Second portion of dbg up til end is exec
         cv32e40s_pkg::pma_region_t'{
            word_addr_low  : 'h 1A11_1000 >> 2,  // after ".debugger"
            word_addr_high : 'h FFFF_FFFF,
            main           : 1,
            bufferable     : 0,
            cacheable      : 0}
         };
   `elsif PMA_DEBUG_CFG
      const string pma_cfg_name = "pma_debug_cfg";
      parameter int unsigned               CORE_PARAM_PMA_NUM_REGIONS = 2;
      parameter cv32e40s_pkg::pma_region_t CORE_PARAM_PMA_CFG[CORE_PARAM_PMA_NUM_REGIONS-1:0] = '{
         // Everything is initially executable
         cv32e40s_pkg::pma_region_t'{
            word_addr_low  : '0,
            word_addr_high : 'h FFFF_FFFF,
            main           : 1,
            bufferable     : 0,
            cacheable      : 0},
         // A small region below "dbg" is forbidden to facilitate pma exception testing
         cv32e40s_pkg::pma_region_t'{
            word_addr_low  : ('h 1a11_0800 - 'd 16) >> 2,
            word_addr_high : 'h 1a11_0800 >> 2,
            main           : 0,
            bufferable     : 0,
            cacheable      : 0}
         };
   `elsif PMA_TEST_CFG_1
      const string pma_cfg_name = "pma_test_cfg_1";
      parameter int unsigned               CORE_PARAM_PMA_NUM_REGIONS = 1;
      parameter cv32e40s_pkg::pma_region_t CORE_PARAM_PMA_CFG[0:CORE_PARAM_PMA_NUM_REGIONS-1] = '{
        '{word_addr_low : 32'h0000_0000>>2, word_addr_high : 32'h7FFF_FFFF>>2, main : 1'b1, bufferable : 1'b1, cacheable : 1'b1}
      };

   `elsif PMA_TEST_CFG_2
      const string pma_cfg_name = "pma_test_cfg_2";
      parameter int unsigned               CORE_PARAM_PMA_NUM_REGIONS = 7;
      parameter cv32e40s_pkg::pma_region_t CORE_PARAM_PMA_CFG[CORE_PARAM_PMA_NUM_REGIONS-1:0] = '{
        '{word_addr_low : 32'hE010_0000>>2, word_addr_high : 32'hFFFF_FFFF>>2, main : 1'b0, bufferable : 1'b1, cacheable : 1'b0},
        '{word_addr_low : 32'hE000_0000>>2, word_addr_high : 32'hE00F_FFFF>>2, main : 1'b0, bufferable : 1'b0, cacheable : 1'b0},
        '{word_addr_low : 32'hA000_0000>>2, word_addr_high : 32'hDFFF_FFFF>>2, main : 1'b0, bufferable : 1'b1, cacheable : 1'b0},
        '{word_addr_low : 32'h6000_0000>>2, word_addr_high : 32'h9FFF_FFFF>>2, main : 1'b1, bufferable : 1'b0, cacheable : 1'b1},
        '{word_addr_low : 32'h4000_0000>>2, word_addr_high : 32'h5FFF_FFFF>>2, main : 1'b0, bufferable : 1'b1, cacheable : 1'b0},
        '{word_addr_low : 32'h2000_0000>>2, word_addr_high : 32'h3FFF_FFFF>>2, main : 1'b1, bufferable : 1'b1, cacheable : 1'b0},
        '{word_addr_low : 32'h0000_0000>>2, word_addr_high : 32'h1FFF_FFFF>>2, main : 1'b1, bufferable : 1'b1, cacheable : 1'b1}
        };
   `elsif PMA_TEST_CFG_3
      const string pma_cfg_name = "pma_test_cfg_3";
      parameter int unsigned               CORE_PARAM_PMA_NUM_REGIONS = 16;
      parameter cv32e40s_pkg::pma_region_t CORE_PARAM_PMA_CFG[CORE_PARAM_PMA_NUM_REGIONS-1:0] = '{
        '{word_addr_low : 32'h0000_A000>>2, word_addr_high : 32'hFFFE_FFFF>>2, main : 1'b1, bufferable : 1'b1, cacheable : 1'b1},
        '{word_addr_low : 32'h0200_0000>>2, word_addr_high : 32'hEFFF_FFFF>>2, main : 1'b1, bufferable : 1'b0, cacheable : 1'b0},
        '{word_addr_low : 32'h0500_0000>>2, word_addr_high : 32'h8459_FFFF>>2, main : 1'b0, bufferable : 1'b1, cacheable : 1'b0},
        '{word_addr_low : 32'h1000_00F1>>2, word_addr_high : 32'h82FF_FFFF>>2, main : 1'b1, bufferable : 1'b1, cacheable : 1'b0},
        '{word_addr_low : 32'h13AC_AA55>>2, word_addr_high : 32'h7FFF_FFFF>>2, main : 1'b1, bufferable : 1'b0, cacheable : 1'b1},
        '{word_addr_low : 32'h2000_0000>>2, word_addr_high : 32'h63FF_FFFF>>2, main : 1'b0, bufferable : 1'b1, cacheable : 1'b0},
        '{word_addr_low : 32'h2340_000A>>2, word_addr_high : 32'h600F_FFFF>>2, main : 1'b1, bufferable : 1'b0, cacheable : 1'b0},
        '{word_addr_low : 32'h2A00_0000>>2, word_addr_high : 32'h56FF_FFFF>>2, main : 1'b1, bufferable : 1'b1, cacheable : 1'b1},
        '{word_addr_low : 32'h2C5A_3200>>2, word_addr_high : 32'h52FF_FFFF>>2, main : 1'b0, bufferable : 1'b1, cacheable : 1'b0},
        '{word_addr_low : 32'h3000_1353>>2, word_addr_high : 32'h5140_FFFF>>2, main : 1'b0, bufferable : 1'b0, cacheable : 1'b0},
        '{word_addr_low : 32'h3100_FCAB>>2, word_addr_high : 32'h5000_BCCA>>2, main : 1'b1, bufferable : 1'b0, cacheable : 1'b0},
        '{word_addr_low : 32'h3420_C854>>2, word_addr_high : 32'h5000_ABFF>>2, main : 1'b1, bufferable : 1'b1, cacheable : 1'b0},
        '{word_addr_low : 32'h3600_A000>>2, word_addr_high : 32'h4F99_FFFF>>2, main : 1'b1, bufferable : 1'b1, cacheable : 1'b1},
        '{word_addr_low : 32'h3ACE_0000>>2, word_addr_high : 32'h4ABC_FFFF>>2, main : 1'b1, bufferable : 1'b1, cacheable : 1'b0},
        '{word_addr_low : 32'h4400_0000>>2, word_addr_high : 32'h4BFF_FFFF>>2, main : 1'b0, bufferable : 1'b0, cacheable : 1'b0},
        '{word_addr_low : 32'h4800_0000>>2, word_addr_high : 32'h49FF_FFFF>>2, main : 1'b1, bufferable : 1'b0, cacheable : 1'b1}
        };
   `elsif PMA_TEST_CFG_4
      const string pma_cfg_name = "pma_test_cfg_4";
      parameter int unsigned               CORE_PARAM_PMA_NUM_REGIONS = 16;
      parameter cv32e40s_pkg::pma_region_t CORE_PARAM_PMA_CFG[CORE_PARAM_PMA_NUM_REGIONS-1:0] = '{
        '{word_addr_low : 32'hE700_EF00>>2, word_addr_high : 32'hE9FF_FFFF>>2, main : 1'b0, bufferable : 1'b1, cacheable : 1'b0},
        '{word_addr_low : 32'hC000_0000>>2, word_addr_high : 32'hDFFF_FFFF>>2, main : 1'b0, bufferable : 1'b0, cacheable : 1'b0},
        '{word_addr_low : 32'hBC00_0000>>2, word_addr_high : 32'hBCFF_FFFF>>2, main : 1'b1, bufferable : 1'b1, cacheable : 1'b0},
        '{word_addr_low : 32'hA000_0000>>2, word_addr_high : 32'hAFFF_FFFF>>2, main : 1'b1, bufferable : 1'b0, cacheable : 1'b0},
        '{word_addr_low : 32'h6300_0000>>2, word_addr_high : 32'h6700_FFFF>>2, main : 1'b0, bufferable : 1'b1, cacheable : 1'b0},
        '{word_addr_low : 32'h5400_0000>>2, word_addr_high : 32'h5FFF_FFFF>>2, main : 1'b1, bufferable : 1'b1, cacheable : 1'b1},
        '{word_addr_low : 32'h5100_0000>>2, word_addr_high : 32'h52FF_FFFF>>2, main : 1'b0, bufferable : 1'b0, cacheable : 1'b0},
        '{word_addr_low : 32'h4D00_5555>>2, word_addr_high : 32'h4FFF_ABCD>>2, main : 1'b1, bufferable : 1'b0, cacheable : 1'b1},
        '{word_addr_low : 32'h4AAA_F000>>2, word_addr_high : 32'h4C00_FFFF>>2, main : 1'b1, bufferable : 1'b1, cacheable : 1'b0},
        '{word_addr_low : 32'h3440_0000>>2, word_addr_high : 32'h3800_FFFF>>2, main : 1'b1, bufferable : 1'b0, cacheable : 1'b1},
        '{word_addr_low : 32'h3100_A000>>2, word_addr_high : 32'h32FF_FFFF>>2, main : 1'b1, bufferable : 1'b1, cacheable : 1'b1},
        '{word_addr_low : 32'h2020_0010>>2, word_addr_high : 32'h2FFF_0000>>2, main : 1'b0, bufferable : 1'b0, cacheable : 1'b0},
        '{word_addr_low : 32'h1800_1234>>2, word_addr_high : 32'h18FF_AB21>>2, main : 1'b0, bufferable : 1'b0, cacheable : 1'b0},
        '{word_addr_low : 32'h1000_0000>>2, word_addr_high : 32'h1001_0000>>2, main : 1'b0, bufferable : 1'b1, cacheable : 1'b0},
        '{word_addr_low : 32'h0030_0000>>2, word_addr_high : 32'h04FF_FFFF>>2, main : 1'b1, bufferable : 1'b1, cacheable : 1'b1},
        '{word_addr_low : 32'h0001_0000>>2, word_addr_high : 32'h001F_FFFF>>2, main : 1'b1, bufferable : 1'b0, cacheable : 1'b0}
        };
   `elsif PMA_TEST_CFG_5
      const string pma_cfg_name = "pma_test_cfg_5";
      parameter int unsigned               CORE_PARAM_PMA_NUM_REGIONS = 16;
      parameter cv32e40s_pkg::pma_region_t CORE_PARAM_PMA_CFG[CORE_PARAM_PMA_NUM_REGIONS-1:0] = '{
        '{word_addr_low : 32'h0000_0000>>2, word_addr_high : 32'hFFFF_FFFF>>2, main : 1'b1, bufferable : 1'b1, cacheable : 1'b1},
        '{word_addr_low : 32'h1249_2492>>2, word_addr_high : 32'h1249_2492>>2, main : 1'b0, bufferable : 1'b0, cacheable : 1'b0},
        '{word_addr_low : 32'h0000_0000>>2, word_addr_high : 32'h0000_0000>>2, main : 1'b0, bufferable : 1'b0, cacheable : 1'b0},
        '{word_addr_low : 32'hDB6D_B6DB>>2, word_addr_high : 32'hDB6D_B6DB>>2, main : 1'b0, bufferable : 1'b0, cacheable : 1'b0},
        '{word_addr_low : 32'h0000_0000>>2, word_addr_high : 32'h0000_0000>>2, main : 1'b0, bufferable : 1'b0, cacheable : 1'b0},
        '{word_addr_low : 32'h9249_2492>>2, word_addr_high : 32'h9249_2492>>2, main : 1'b0, bufferable : 1'b0, cacheable : 1'b0},
        '{word_addr_low : 32'h0000_0000>>2, word_addr_high : 32'h0000_0000>>2, main : 1'b0, bufferable : 1'b0, cacheable : 1'b0},
        '{word_addr_low : 32'hFFFF_FFFF>>2, word_addr_high : 32'hFFFF_FFFF>>2, main : 1'b0, bufferable : 1'b0, cacheable : 1'b0},
        '{word_addr_low : 32'h0000_0000>>2, word_addr_high : 32'h0000_0000>>2, main : 1'b0, bufferable : 1'b0, cacheable : 1'b0},
        '{word_addr_low : 32'hE38E_E38E>>2, word_addr_high : 32'hE38E_E38E>>2, main : 1'b0, bufferable : 1'b0, cacheable : 1'b0},
        '{word_addr_low : 32'h0000_0000>>2, word_addr_high : 32'h0000_0000>>2, main : 1'b0, bufferable : 1'b0, cacheable : 1'b0},
        '{word_addr_low : 32'hCCCC_CCCC>>2, word_addr_high : 32'hCCCC_CCCC>>2, main : 1'b0, bufferable : 1'b0, cacheable : 1'b0},
        '{word_addr_low : 32'hAAAA_AAAA>>2, word_addr_high : 32'hAAAA_AAAA>>2, main : 1'b0, bufferable : 1'b0, cacheable : 1'b0},
        '{word_addr_low : 32'h0000_0000>>2, word_addr_high : 32'h0000_0000>>2, main : 1'b0, bufferable : 1'b0, cacheable : 1'b0},
        '{word_addr_low : 32'h5555_5555>>2, word_addr_high : 32'h5555_5555>>2, main : 1'b0, bufferable : 1'b0, cacheable : 1'b0},
        '{word_addr_low : 32'h0000_0000>>2, word_addr_high : 32'h0000_0000>>2, main : 1'b0, bufferable : 1'b0, cacheable : 1'b0}
        };
   `elsif PMA_TEST_CFG_X1 // Used for memory layout generator debug
      const string pma_cfg_name = "pma_test_cfg_x1";
      parameter int unsigned               CORE_PARAM_PMA_NUM_REGIONS = 5;
      parameter cv32e40s_pkg::pma_region_t CORE_PARAM_PMA_CFG[CORE_PARAM_PMA_NUM_REGIONS-1:0] = '{
        '{word_addr_low : 32'h00000000>>2, word_addr_high : 32'h20000000>>2, main : 1'b1, bufferable : 1'b0, cacheable : 1'b1},
        '{word_addr_low : 32'h30000000>>2, word_addr_high : 32'h40000000>>2, main : 1'b1, bufferable : 1'b0, cacheable : 1'b1},
        '{word_addr_low : 32'h50000000>>2, word_addr_high : 32'h60000000>>2, main : 1'b1, bufferable : 1'b0, cacheable : 1'b1},
        '{word_addr_low : 32'h70000000>>2, word_addr_high : 32'h80000000>>2, main : 1'b1, bufferable : 1'b0, cacheable : 1'b1},
        '{word_addr_low : 32'h00000000>>2, word_addr_high : 32'hF0000000>>2, main : 1'b1, bufferable : 1'b0, cacheable : 1'b1}
        };
   `else
      const string pma_cfg_name = "pma_noregion";
      parameter int unsigned               CORE_PARAM_PMA_NUM_REGIONS = 0;
      parameter cv32e40s_pkg::pma_region_t CORE_PARAM_PMA_CFG[-1:0] = '{default:cv32e40s_pkg::PMA_R_DEFAULT};
   `endif


`endif // __UVMT_CV32E40S_CONSTANTS_SV__

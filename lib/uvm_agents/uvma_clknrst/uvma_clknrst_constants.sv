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


`ifndef __UVMA_CLKNRST_CONSTANTS_SV__
`define __UVMA_CLKNRST_CONSTANTS_SV__


const realtime      uvma_clknrst_default_clk_period               =    10ns;
const int unsigned  uvma_clknrst_default_rst_deassert_period      = 100_000; // 100 ns
const int unsigned  uvma_clknrst_default_mon_clk_lock_edge_count  =     100;


`endif // __UVMA_CLKNRST_CONSTANTS_SV__

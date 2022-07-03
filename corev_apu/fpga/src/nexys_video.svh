// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Description: Set global FPGA degines
// Author: Florian Zaruba <zarubaf@iis.ee.ethz.ch>

`define NEXYS_VIDEO

`define ARIANE_DATA_WIDTH 64

// Instantiate protocl checker
// `define PROTOCOL_CHECKER

// write-back cache
// `define WB_DCACHE

// write-through cache
`define WT_DCACHE

`define RAMB16


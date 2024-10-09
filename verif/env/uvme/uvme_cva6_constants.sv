// Copyright 2020 OpenHW Group
// Copyright 2020 Datum Technology Corporation
// Copyright 2021 Thales DIS Design Services SAS
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


`ifndef __UVME_CVA6_CONSTANTS_SV__
`define __UVME_CVA6_CONSTANTS_SV__


parameter uvme_cva6_sys_default_clk_period   = 10_000; // 10ns
parameter uvme_cva6_debug_default_clk_period = 10_000; // 10ns

parameter XLEN = 32;
parameter ILEN = 32;


// Control how often to print core scoreboard checked heartbeat messages
parameter PC_CHECKED_HEARTBEAT = 10_000;

// Map the virtual peripheral registers
parameter CV_VP_REGISTER_BASE          = 32'h8080_0000;
parameter CV_VP_REGISTER_SIZE          = 32'h0000_1000;

parameter CV_VP_VIRTUAL_PRINTER_OFFSET = 32'h0000_0000;
parameter CV_VP_RANDOM_NUM_OFFSET      = 32'h0000_0040;
parameter CV_VP_CYCLE_COUNTER_OFFSET   = 32'h0000_0080;
parameter CV_VP_STATUS_FLAGS_OFFSET    = 32'h0000_00c0;
parameter CV_VP_FENCEI_TAMPER_OFFSET   = 32'h0000_0100;
parameter CV_VP_INTR_TIMER_OFFSET      = 32'h0000_0140;
parameter CV_VP_DEBUG_CONTROL_OFFSET   = 32'h0000_0180;
parameter CV_VP_OBI_SLV_RESP_OFFSET    = 32'h0000_01c0;
parameter CV_VP_SIG_WRITER_OFFSET      = 32'h0000_0200;

parameter CV_VP_VIRTUAL_PRINTER_BASE   = CV_VP_REGISTER_BASE + CV_VP_VIRTUAL_PRINTER_OFFSET;
parameter CV_VP_RANDOM_NUM_BASE        = CV_VP_REGISTER_BASE + CV_VP_RANDOM_NUM_OFFSET;
parameter CV_VP_CYCLE_COUNTER_BASE     = CV_VP_REGISTER_BASE + CV_VP_CYCLE_COUNTER_OFFSET;
parameter CV_VP_STATUS_FLAGS_BASE      = CV_VP_REGISTER_BASE + CV_VP_STATUS_FLAGS_OFFSET;
parameter CV_VP_INTR_TIMER_BASE        = CV_VP_REGISTER_BASE + CV_VP_INTR_TIMER_OFFSET;
parameter CV_VP_DEBUG_CONTROL_BASE     = CV_VP_REGISTER_BASE + CV_VP_DEBUG_CONTROL_OFFSET;
parameter CV_VP_OBI_SLV_RESP_BASE      = CV_VP_REGISTER_BASE + CV_VP_OBI_SLV_RESP_OFFSET;
parameter CV_VP_SIG_WRITER_BASE        = CV_VP_REGISTER_BASE + CV_VP_SIG_WRITER_OFFSET;
parameter CV_VP_FENCEI_TAMPER_BASE     = CV_VP_REGISTER_BASE + CV_VP_FENCEI_TAMPER_OFFSET;

`endif // __UVME_CVA6_CONSTANTS_SV__

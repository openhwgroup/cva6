// Copyright 2022 Thales DIS SAS
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
// You may obtain a copy of the License at https://solderpad.org/licenses/
//
// Original Author: Alae Eddine EZ ZEJJARI (alae-eddine.ez-zejjari@external.thalesgroup.com)
// Co-Author: Abdelaali Khardazi

/***** AXI4 slave agent package *****/

`ifndef __UVMA_AXI_PKG_SV__
`define __UVMA_AXI_PKG_SV__

// Pre-processor macros
`include "uvm_macros.svh"
`include "uvma_axi_macros.sv"


// Interfaces / Modules / Checkers
`include "uvma_axi_intf.sv"
`include "uvma_axi_aw_assert.sv"
`include "uvma_axi_w_assert.sv"
`include "uvma_axi_ar_assert.sv"
`include "uvma_axi_r_assert.sv"
`include "uvma_axi_b_assert.sv"

package uvma_axi_pkg;

   import uvm_pkg::*;
   import uvml_mem_pkg  ::*;
   import uvml_trn_pkg  ::*;
   import uvml_logs_pkg ::*;

   import "DPI-C" function read_elf(input string filename);
   import "DPI-C" function byte get_section(output longint address, output longint len);
   import "DPI-C" context function void read_section(input longint address, inout byte buffer[]);

   localparam NrSlaves      = 2; // actually masters, but slaves on the crossbar
   localparam IdWidth       = 4; // 4 is recommended by AXI standard, so lets stick to it, do not change
   localparam IdWidthSlave  = IdWidth + $clog2(NrSlaves);
   parameter AXI_ADDR_WIDTH = `UVMA_AXI_ADDR_MAX_WIDTH;
   parameter AXI_DATA_WIDTH = `UVMA_AXI_DATA_MAX_WIDTH;
   parameter AXI_USER_WIDTH = `UVMA_AXI_USER_MAX_WIDTH;
   parameter AXI_ID_WIDTH   = IdWidthSlave;
   parameter NUM_WORDS      = 2**24;

   `include "uvma_axi_tdefs.sv"

    // Objects
   `include "uvma_axi_cfg.sv"
   `include "uvma_axi_cntxt.sv"

   `include "uvma_axi_base_seq_item.sv"
   `include "uvma_axi_aw_item.sv"
   `include "uvma_axi_w_item.sv"
   `include "uvma_axi_b_item.sv"
   `include "uvma_axi_ar_item.sv"
   `include "uvma_axi_r_item.sv"

   `include "uvma_axi_aw_drv.sv"
   `include "uvma_axi_w_drv.sv"
   `include "uvma_axi_b_drv.sv"
   `include "uvma_axi_ar_drv.sv"
   `include "uvma_axi_r_drv.sv"
   `include "uvma_axi_aw_mon.sv"
   `include "uvma_axi_w_mon.sv"
   `include "uvma_axi_b_mon.sv"
   `include "uvma_axi_ar_mon.sv"
   `include "uvma_axi_r_mon.sv"

   `include "uvma_axi_aw_sqr.sv"
   `include "uvma_axi_w_sqr.sv"
   `include "uvma_axi_b_sqr.sv"
   `include "uvma_axi_ar_sqr.sv"
   `include "uvma_axi_r_sqr.sv"

   `include "uvma_axi_seq_item_logger.sv"

   `include "uvma_axi_aw_agent.sv"
   `include "uvma_axi_w_agent.sv"
   `include "uvma_axi_b_agent.sv"
   `include "uvma_axi_ar_agent.sv"
   `include "uvma_axi_r_agent.sv"

   `include "uvma_axi_vsqr.sv"

   `include "uvma_axi_agent.sv"
    // Sequences
   `include "uvma_axi_seq_lib.sv"

endpackage : uvma_axi_pkg

`endif

// Copyright 2022 Thales DIS SAS
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
// You may obtain a copy of the License at https://solderpad.org/licenses/
//
// Original Author: Alae Eddine EZ ZEJJARI (alae-eddine.ez-zejjari@external.thalesgroup.com)
// Co-Author: Abdelaali Khardazi


`ifndef __UVMA_AXI_CFG_SV__
`define __UVMA_AXI_CFG_SV__

class uvma_axi_cfg_c extends uvm_object;

   rand uvm_active_passive_enum            is_active;
   rand bit                                trn_log_enabled;
   rand uvma_axi_drv_slv_mode_enum         drv_slv_mode;
   rand uvma_axi_drv_slv_err_mode_enum     drv_slv_err_mode;

   rand int unsigned             drv_slv_fixed_latency;
   rand int unsigned             drv_slv_random_latency_min;
   rand int unsigned             drv_slv_random_latency_max;

   rand int unsigned             drv_slv_err_ok;
   rand int unsigned             drv_slv_err_dec;
   rand int unsigned             drv_slv_err_slv;
   rand bit                      drv_slv_err_one_shot_mode;
   rand bit                      drv_slv_err_one_shot_flag;
   bit                           directed_slv_err_valid;
   bit[1:0]                      drv_slv_fixed_resp = 2'b10;

   `uvm_object_utils_begin(uvma_axi_cfg_c)
      `uvm_field_enum(uvm_active_passive_enum, is_active, UVM_DEFAULT);
      `uvm_field_int (directed_slv_err_valid, UVM_DEFAULT)
      `uvm_field_int (drv_slv_fixed_latency, UVM_DEFAULT)
      `uvm_field_int (drv_slv_random_latency_min, UVM_DEFAULT)
      `uvm_field_int (drv_slv_random_latency_max, UVM_DEFAULT)
      `uvm_field_int (drv_slv_err_one_shot_mode, UVM_DEFAULT)
      `uvm_field_int (drv_slv_err_one_shot_flag, UVM_DEFAULT)
      `uvm_field_int (drv_slv_err_ok, UVM_DEFAULT  | UVM_DEC)
      `uvm_field_int (drv_slv_err_dec, UVM_DEFAULT | UVM_DEC)
      `uvm_field_int (drv_slv_err_slv, UVM_DEFAULT | UVM_DEC)
      `uvm_field_int (drv_slv_fixed_resp, UVM_DEFAULT | UVM_DEC)
      `uvm_field_enum(uvma_axi_drv_slv_mode_enum, drv_slv_mode, UVM_DEFAULT)
      `uvm_field_enum(uvma_axi_drv_slv_err_mode_enum, drv_slv_err_mode, UVM_DEFAULT)
   `uvm_object_utils_end

   constraint defaults_config {
      soft is_active                   == UVM_ACTIVE;
      soft drv_slv_err_one_shot_mode   == 0;
      soft drv_slv_mode                == UVMA_AXI_DRV_SLV_MODE_RANDOM_LATENCY;
      soft drv_slv_fixed_latency       == 3;
      soft drv_slv_random_latency_min  == 0;
      soft drv_slv_random_latency_max  == 4;
      soft directed_slv_err_valid      == 0;
      soft drv_slv_err_mode            == UVMA_AXI_DRV_SLV_ERR_MODE_RANDOM;
     }

   constraint err_wgts_cons {
      // Keep the weights for errors within some bounds
      drv_slv_err_ok  inside {[0:1000]};
      drv_slv_err_dec inside {[0:1000]};
      drv_slv_err_slv inside {[0:1000]};
   }

   extern function new(string name = "uvma_axi_cfg");

   extern function int unsigned calc_random_latency();

   extern function bit[1:0] random_err();

endclass : uvma_axi_cfg_c


function uvma_axi_cfg_c::new(string name = "uvma_axi_cfg");

   super.new(name);

endfunction : new

function int unsigned uvma_axi_cfg_c::calc_random_latency();
   int unsigned effective_latency;

   case (drv_slv_mode)
      UVMA_AXI_DRV_SLV_MODE_CONSTANT      : effective_latency = 0;
      UVMA_AXI_DRV_SLV_MODE_FIXED_LATENCY : effective_latency = drv_slv_fixed_latency;
      UVMA_AXI_DRV_SLV_MODE_RANDOM_LATENCY: begin
         effective_latency = $urandom_range(drv_slv_random_latency_min, drv_slv_random_latency_max);
      end
   endcase

   return effective_latency;

endfunction : calc_random_latency

function bit[1:0] uvma_axi_cfg_c::random_err();

   bit[1:0] err;

   // If we are in "one-shot" mode and have already calculated an error,
   // then skip any new errors (until the code resets the flag)
   if (drv_slv_err_one_shot_mode && drv_slv_err_one_shot_flag) begin
      return 0;
   end

   // Check for a directed error reponse first
   if (directed_slv_err_valid) begin

      if (drv_slv_err_one_shot_mode) begin
         drv_slv_err_one_shot_flag = 1;
      end

      return drv_slv_fixed_resp;
   end

   case (drv_slv_err_mode)
      UVMA_AXI_DRV_SLV_ERR_MODE_OK      : err = 2'b00;
      UVMA_AXI_DRV_SLV_ERR_MODE_RANDOM  : begin
         randcase
            drv_slv_err_ok : err = 2'b00;
            drv_slv_err_dec: err = 2'b11;
            drv_slv_err_slv: err = 2'b10;
         endcase
      end
   endcase

   if (err != 0 && drv_slv_err_one_shot_mode) begin
      drv_slv_err_one_shot_flag = 1;
   end

   return err;

endfunction : random_err

`endif //__UVMA_AXI_CFG_SV__

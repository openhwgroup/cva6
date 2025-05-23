`ifndef ARIANE_XLNX_CONFIG_SVH
`define ARIANE_XLNX_CONFIG_SVH

`include "build_config_pkg.sv"

import cva6_config_pkg::*;

// CVA6 Xilinx configuration
function automatic config_pkg::cva6_cfg_t build_fpga_config(
    config_pkg::cva6_user_cfg_t CVA6UserCfg);
  config_pkg::cva6_user_cfg_t cfg = CVA6UserCfg;
  cfg.FpgaEn = bit'(1);
  cfg.NrNonIdempotentRules = unsigned'(1);
  cfg.NonIdempotentAddrBase = 1024'({64'b0});
  cfg.NonIdempotentLength = 1024'({64'h8000_0000});
  cfg.NrExecuteRegionRules = unsigned'(3);
  cfg.ExecuteRegionAddrBase = 1024'({64'h8000_0000, 64'h1_0000, 64'h0});
  cfg.ExecuteRegionLength = 1024'({64'h4000_0000, 64'h1_0000, 64'h1000});
  cfg.NrCachedRegionRules = unsigned'(1);
  cfg.CachedRegionAddrBase = 1024'({64'h8000_0000});
  cfg.CachedRegionLength = 1024'({64'h4000_0000});
  return build_config_pkg::build_config(cfg);
endfunction

localparam config_pkg::cva6_cfg_t CVA6Cfg = build_fpga_config(cva6_config_pkg::cva6_cfg);

`endif

// (C) 2001-2024 Intel Corporation. All rights reserved.
// Your use of Intel Corporation's design tools, logic functions and other 
// software and tools, and its AMPP partner logic functions, and any output 
// files from any of the foregoing (including device programming or simulation 
// files), and any associated documentation or information are expressly subject 
// to the terms and conditions of the Intel Program License Subscription 
// Agreement, Intel FPGA IP License Agreement, or other applicable 
// license agreement, including, without limitation, that your use is for the 
// sole purpose of programming logic devices manufactured by Intel and sold by 
// Intel or its authorized distributors.  Please refer to the applicable 
// agreement for further details.




module altera_emif_arch_fm_hmc_mmr_if #(

   parameter PORT_CTRL_MMR_SLAVE_ADDRESS_WIDTH             = 1,
   parameter PORT_CTRL_MMR_SLAVE_RDATA_WIDTH               = 1,
   parameter PORT_CTRL_MMR_SLAVE_WDATA_WIDTH               = 1,
   parameter PORT_CTRL_MMR_SLAVE_BCOUNT_WIDTH              = 1
) (
   input  logic [33:0]                                        ctl2core_mmr_0,
   output logic [50:0]                                        core2ctl_mmr_0,
   input  logic [33:0]                                        ctl2core_mmr_1,
   output logic [50:0]                                        core2ctl_mmr_1,

   input  logic                                               emif_usr_clk,
   
   output logic                                               mmr_slave_waitrequest_0,
   input  logic                                               mmr_slave_read_0,
   input  logic                                               mmr_slave_write_0,
   input  logic [PORT_CTRL_MMR_SLAVE_ADDRESS_WIDTH-1:0]       mmr_slave_address_0,
   output logic [PORT_CTRL_MMR_SLAVE_RDATA_WIDTH-1:0]         mmr_slave_readdata_0,
   input  logic [PORT_CTRL_MMR_SLAVE_WDATA_WIDTH-1:0]         mmr_slave_writedata_0,
   input  logic [PORT_CTRL_MMR_SLAVE_BCOUNT_WIDTH-1:0]        mmr_slave_burstcount_0,
   input  logic                                               mmr_slave_beginbursttransfer_0,
   output logic                                               mmr_slave_readdatavalid_0,
   
   output logic                                               mmr_slave_waitrequest_1,
   input  logic                                               mmr_slave_read_1,
   input  logic                                               mmr_slave_write_1,
   input  logic [PORT_CTRL_MMR_SLAVE_ADDRESS_WIDTH-1:0]       mmr_slave_address_1,
   output logic [PORT_CTRL_MMR_SLAVE_RDATA_WIDTH-1:0]         mmr_slave_readdata_1,
   input  logic [PORT_CTRL_MMR_SLAVE_WDATA_WIDTH-1:0]         mmr_slave_writedata_1,
   input  logic [PORT_CTRL_MMR_SLAVE_BCOUNT_WIDTH-1:0]        mmr_slave_burstcount_1,
   input  logic                                               mmr_slave_beginbursttransfer_1,
   output logic                                               mmr_slave_readdatavalid_1   
);
   timeunit 1ns;
   timeprecision 1ps;
   
   assign core2ctl_mmr_1[13:10]      = 'b0;
   assign core2ctl_mmr_0[13:10]      = 'b0;

   always_ff @(posedge emif_usr_clk) begin
      core2ctl_mmr_0[9:0]        <= mmr_slave_address_0;
      core2ctl_mmr_0[45:14]      <= mmr_slave_writedata_0;
      core2ctl_mmr_0[46]         <= mmr_slave_write_0;
      core2ctl_mmr_0[47]         <= mmr_slave_read_0;
      core2ctl_mmr_0[49:48]      <= mmr_slave_burstcount_0;
      core2ctl_mmr_0[50]         <= mmr_slave_beginbursttransfer_0;
      
      mmr_slave_readdata_0       <= ctl2core_mmr_0[31:0];
      mmr_slave_readdatavalid_0  <= ctl2core_mmr_0[32];
      mmr_slave_waitrequest_0    <= ctl2core_mmr_0[33];

      core2ctl_mmr_1[9:0]        <= mmr_slave_address_1;
      core2ctl_mmr_1[45:14]      <= mmr_slave_writedata_1;
      core2ctl_mmr_1[46]         <= mmr_slave_write_1;
      core2ctl_mmr_1[47]         <= mmr_slave_read_1;
      core2ctl_mmr_1[49:48]      <= mmr_slave_burstcount_1;
      core2ctl_mmr_1[50]         <= mmr_slave_beginbursttransfer_1;
      
      mmr_slave_readdata_1       <= ctl2core_mmr_1[31:0];
      mmr_slave_readdatavalid_1  <= ctl2core_mmr_1[32];
      mmr_slave_waitrequest_1    <= ctl2core_mmr_1[33];
   end
   
endmodule

`ifdef QUESTA_INTEL_OEM
`pragma questa_oem_00 "EVeqkz9MvDzapiiVw7+udc++m43wu2P9R6Bkf/lfBn9ZttFzW71hzuu9P3yzPlvUUu1GESHEht8oUjkuxH5nYF5m2Y4yEaZOsor1W+qakklkcNM5gczDB8G/zUljAitcohcjlH9xX4F5r3RrLLQB1HrtXmnxKKrsVs2RsxKt4plRYJGUCxRjs6twKgr6lps1q22taZT7+7dZh7dYE0uKJfWB1PYeKR+rbOxvrAyMNm2zTfIUIGJoZH5DYU9hegJoUhSoB9M+V9SheV2Iit6Wtucb91DV9bw4WeqcRbqpf1olkZRBqaRzLIXMWwNC1V4x/fxciUj6QtrpgSNybY7tJyX3ksHuwDdun3hpwxubpi9CHm/Ugg5UVRXK3HlKG04ISwnsLX1dP8836ZwO2vej08xxxb1v6qZBgrdXsNgb1ErxwGFLb6+BLN0zoSUgiX92rJTRiRM1ce7/9fLEMEzXSoTxPLgCaZ8W3E68tQuuJawst0W/nN1gfaAFHOBUeU4DTLiNVcCzSFbMb4+1IVayv0EW0xZuenNGnvO29mPBdjD1hp/dgdKNFGTd9mpBAXH5M9JYPBgPhuaJJIeADvEeW4sfiPGbJeW8gA6l9LixrxstXsuEBGZPJ73HOMvaXDHkVZr0WeFYZtSLiiFX9BRh4/JjxR1eMkS9cH3uVhIf1eZNIRzJinyrXUK0J9/OpKc1am0Ebh7twp9AepnWc/mm05IXmkYVFbmnwSecYhe4GjD6XcV9nCX/hEHBReDULdf1HaYunTUjKslyOKZ+ciAQtxtxXLxWjHluYJYZBGEgisnfYqOEf3KNCAI2H3DSzdIqJu96EtXFtGSbTYrCUxWVx/lcTPXD2i3di+wjjiRoyXk6GdWgHKtqIqt82xBFy6y4wLsPVxXyvyAwnMdZhRaoXyJz2pL0JIRCSxP5GIyA3ZiLI5qVrU53abXPay/x3fRLABePWXxMd00X2I6eNtidXz8Pgiu334BVTsekAAPjz9zOxfrcbW6IYE10X+slbvTC"
`endif
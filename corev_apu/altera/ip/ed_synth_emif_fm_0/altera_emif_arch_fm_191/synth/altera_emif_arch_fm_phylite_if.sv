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


///////////////////////////////////////////////////////////////////////////////
// This module is responsible for exposing the data interfaces through which
// soft logic interacts with the Avalon MM port of the HMC
// 
///////////////////////////////////////////////////////////////////////////////

`define _get_pin_count(_loc) ( _loc[ 9 : 0 ] )
`define _get_pin_index(_loc, _port_i) ( _loc[ (_port_i + 1) * 10 +: 10 ] )

`define _get_tile(_loc, _port_i) (  `_get_pin_index(_loc, _port_i) / (PINS_PER_LANE * LANES_PER_TILE) )
`define _get_lane(_loc, _port_i) ( (`_get_pin_index(_loc, _port_i) / PINS_PER_LANE) % LANES_PER_TILE ) 
`define _get_pin(_loc, _port_i)  (  `_get_pin_index(_loc, _port_i) % PINS_PER_LANE )

`define _core2l_data(_port_i, _phase_i) core2l_data\
   [`_get_tile(WD_PINLOC, _port_i)]\
   [`_get_lane(WD_PINLOC, _port_i)]\
   [(`_get_pin(WD_PINLOC, _port_i) * 8) + _phase_i]

`define _core2l_oe(_port_i, _phase_i) core2l_oe\
   [`_get_tile(WD_PINLOC, _port_i)]\
   [`_get_lane(WD_PINLOC, _port_i)]\
   [(`_get_pin(WD_PINLOC, _port_i) * 4) + _phase_i]

`define _l2core_data(_port_i, _phase_i) l2core_data\
   [`_get_tile(RD_PINLOC, _port_i)]\
   [`_get_lane(RD_PINLOC, _port_i)]\
   [(`_get_pin(RD_PINLOC, _port_i) * 8) + _phase_i]

`define _l2core_rdata_valid(_port_i) l2core_rdata_valid\
   [`_get_tile(WD_PINLOC, _port_i)]\
   [`_get_lane(WD_PINLOC, _port_i)]
   
`define _unused_core2l_data(_pin_i) core2l_data\
   [_pin_i / (PINS_PER_LANE * LANES_PER_TILE)]\
   [(_pin_i / PINS_PER_LANE) % LANES_PER_TILE]\
   [((_pin_i % PINS_PER_LANE) * 8) +: 8]

`define _unused_oe(_pin_i) core2l_oe\
   [_pin_i / (PINS_PER_LANE * LANES_PER_TILE)]\
   [(_pin_i / PINS_PER_LANE) % LANES_PER_TILE]\
   [((_pin_i % PINS_PER_LANE) * 4) +: 4]    

module altera_emif_arch_fm_phylite_if #(
   parameter PINS_PER_LANE                  = 1,
   parameter LANES_PER_TILE                 = 1,
   parameter NUM_OF_RTL_TILES               = 1,
   parameter UFI_LATENCY                    = 2,
  
   // Pin indexes of data signals
   parameter PORT_MEM_D_PINLOC              = 10'b0000000000,
   parameter PORT_MEM_DQ_PINLOC             = 10'b0000000000,
   parameter PORT_MEM_Q_PINLOC              = 10'b0000000000,
   parameter PORT_MEM_DQS_PINLOC            = 10'b0000000000,
   parameter PORT_MEM_DQS_N_PINLOC          = 10'b0000000000,
 
   // Pin indexes of write data mask signals
   parameter PORT_MEM_DM_PINLOC             = 10'b0000000000,
   parameter PORT_MEM_DBI_N_PINLOC          = 10'b0000000000,
   parameter PORT_MEM_BWS_N_PINLOC          = 10'b0000000000,
   
   // Parameter indicating the core-2-lane connection of a pin is actually driven
   parameter PINS_C2L_DRIVEN                = 1'b0,

   // Definition of port widths for "phylite" interface (auto-generated)
   parameter PORT_CTRL_DATA_OUT_WIDTH       = 1,
   parameter PORT_CTRL_DATA_IN_WIDTH        = 1,
   parameter PORT_CTRL_DATA_OE_WIDTH        = 1,
   parameter PORT_CTRL_STROBE_OE_WIDTH      = 1,
   parameter PORT_CTRL_STROBE_WIDTH         = 1,
   parameter PORT_CTRL_RDATA_VALID_WIDTH    = 1,
   parameter PORT_CTRL_RDATA_ENABLE_WIDTH   = 1
) (
   input logic                                                                       pll_locked,
   input logic                                                                       emif_usr_clk,
   input logic                                                                       emif_usr_clk_sec,
   input logic                                                                       ufi_phy_clk,

   // Signals between core and data lanes
   output logic [NUM_OF_RTL_TILES-1:0][LANES_PER_TILE-1:0][PINS_PER_LANE * 8 - 1:0]  core2l_data,
   output logic [NUM_OF_RTL_TILES-1:0][LANES_PER_TILE-1:0][PINS_PER_LANE * 4 - 1:0]  core2l_oe,
   input  logic [NUM_OF_RTL_TILES-1:0][LANES_PER_TILE-1:0][PINS_PER_LANE * 8 - 1:0]  l2core_data,
   input  logic [3:0]                                                                l2core_rdata_valid,
   output logic [NUM_OF_RTL_TILES-1:0][LANES_PER_TILE-1:0][3:0]                      core2l_rdata_en_full,
   input  logic [1:0]                                                                core_clks_locked_cpa_pri,

   // PHYLite interface
   input  logic [PORT_CTRL_STROBE_WIDTH-1:0]                                         phylite_strobe,  
   input  logic [PORT_CTRL_DATA_OE_WIDTH-1:0]                                        phylite_data_oe,
   input  logic [PORT_CTRL_STROBE_OE_WIDTH-1:0]                                      phylite_strobe_oe,   
   input  logic [PORT_CTRL_DATA_OUT_WIDTH-1:0]                                       phylite_data_from_core,  
   output logic [PORT_CTRL_DATA_IN_WIDTH-1:0]                                        phylite_data_to_core,  
   output logic [PORT_CTRL_RDATA_VALID_WIDTH-1:0]                                    phylite_rdata_valid,
   input  logic [PORT_CTRL_RDATA_ENABLE_WIDTH-1:0]                                   phylite_rdata_en,
   output logic                                                                      phylite_interface_locked
);
   timeunit 1ns;
   timeprecision 1ps;

   localparam RD_PINLOC = (`_get_pin_count(PORT_MEM_DQ_PINLOC) != 0 ? PORT_MEM_DQ_PINLOC : PORT_MEM_Q_PINLOC);
   localparam WD_PINLOC = (`_get_pin_count(PORT_MEM_DQ_PINLOC) != 0 ? PORT_MEM_DQ_PINLOC : PORT_MEM_D_PINLOC);
      
   localparam NUM_RD_PINS    = `_get_pin_count(RD_PINLOC);
   localparam NUM_WD_PINS    = `_get_pin_count(WD_PINLOC);
   localparam NUM_DQS_PINS   = `_get_pin_count(PORT_MEM_DQS_PINLOC);
   localparam NUM_DQS_N_PINS = `_get_pin_count(PORT_MEM_DQS_N_PINLOC);

   localparam NUM_OF_RD_PHASES = PORT_CTRL_DATA_OUT_WIDTH / NUM_RD_PINS;
   localparam NUM_OF_WD_PHASES = PORT_CTRL_DATA_IN_WIDTH / NUM_WD_PINS;
   localparam NUM_OF_OE_PHASES = NUM_OF_WD_PHASES / 2;
  

   logic [NUM_WD_PINS-1:0][NUM_OF_OE_PHASES-1:0] ufi_core2l_oe;
   logic [NUM_OF_RTL_TILES-1:0][LANES_PER_TILE-1:0][3:0] ufi_core2l_rdata_en_full;
   localparam UFI_MODE = (UFI_LATENCY == 2) ? "pin_ufi_use_delay_fifo_out_reg" :
                         (UFI_LATENCY == 1) ? "pin_ufi_use_in_direct_out_reg"  : "pin_ufi_use_in_direct_out_direct";
   localparam P2C_UFI_MODE = (UFI_LATENCY == 2) ? "pin_ufi_use_fast_fifo_out_reg" :
                             (UFI_LATENCY == 1) ? "pin_ufi_use_in_direct_out_reg"  : "pin_ufi_use_in_direct_out_direct";
   generate
      genvar port_i, data_i, oe_i, phase_i, pin_i;
      genvar tile_i, lane_i, sig_i;
     

      // phylite_interface locked signal 
      assign phylite_interface_locked= pll_locked ;
   
      // phylite_data_from_core  to lanes' write data bus
      for (port_i = 0; port_i < NUM_WD_PINS; ++port_i) begin : wd_port
      
         for (data_i = 0; data_i < 8; ++data_i)
         begin : data_phase
               if (data_i < NUM_OF_WD_PHASES) begin
                  assign `_core2l_data(port_i, data_i) = phylite_data_from_core[data_i * NUM_WD_PINS + port_i];
               end else begin 
                  assign `_core2l_data(port_i, data_i) = 1'b0;
               end
         end

         for (oe_i = 0; oe_i < 4; ++oe_i)
         begin : oe_phase
               if (oe_i < NUM_OF_OE_PHASES) begin
                  (* altera_attribute = {"-name FORCE_HYPER_REGISTER_FOR_CORE_PERIPHERY_TRANSFER ON; -name HYPER_REGISTER_DELAY_CHAIN 225"} *)
                  tennm_ufi # (
                   .mode    (UFI_MODE),
                   .datapath("c2p")) ufi_inst (
                     .srcclk (emif_usr_clk),
                     .destclk(ufi_phy_clk),
                     .d      (phylite_data_oe[oe_i]),
                     .dout   (ufi_core2l_oe[port_i][oe_i])
                  );
                  assign `_core2l_oe(port_i, oe_i) = ufi_core2l_oe[port_i][oe_i];
               end else begin 
                  assign `_core2l_oe(port_i, oe_i) = 1'b0;
               end
         end
      end

      // Map lanes' read data bus to phylite_data_to_core  
      for (port_i = 0; port_i < NUM_RD_PINS; ++port_i)
      begin : rd_port
         for (phase_i = 0; phase_i < NUM_OF_RD_PHASES; ++phase_i)
         begin : phase
               assign phylite_data_to_core[phase_i * NUM_RD_PINS + port_i] = `_l2core_data(port_i, phase_i);
         end
      end

      // Map lanes' read_valid to phylite_rdata_valid 
      (* altera_attribute = {"-name FORCE_HYPER_REGISTER_FOR_CORE_PERIPHERY_TRANSFER ON; -name HYPER_REGISTER_DELAY_CHAIN 225"} *)
      tennm_ufi # (
       .mode    (P2C_UFI_MODE),
       .datapath("p2c")) rdata_valid_ufi_inst [PORT_CTRL_RDATA_VALID_WIDTH - 1:0] (
         .srcclk (ufi_phy_clk),
         .destclk(emif_usr_clk),
         .d      (l2core_rdata_valid[PORT_CTRL_RDATA_VALID_WIDTH - 1:0]),
         .dout   (phylite_rdata_valid[PORT_CTRL_RDATA_VALID_WIDTH - 1:0])
      );

      // Map lanes' rdata_en
      for (tile_i = 0; tile_i < NUM_OF_RTL_TILES; ++tile_i) begin : tile_loop
         for (lane_i = 0; lane_i < LANES_PER_TILE; ++lane_i) begin : lane_loop
             for (sig_i = 0; sig_i < 4; ++sig_i) begin : sig_loop
                 (* altera_attribute = {"-name FORCE_HYPER_REGISTER_FOR_CORE_PERIPHERY_TRANSFER ON; -name HYPER_REGISTER_DELAY_CHAIN 225"} *)
                 tennm_ufi # (
                  .mode    (UFI_MODE),
                  .datapath("c2p")) ufi_inst (
                    .srcclk (emif_usr_clk),
                    .destclk(ufi_phy_clk),
                    .d      (phylite_rdata_en[sig_i]),
                    .dout   (ufi_core2l_rdata_en_full[tile_i][lane_i][sig_i])
                 );
             end 
             assign core2l_rdata_en_full[tile_i][lane_i] = {{(4 - PORT_CTRL_RDATA_ENABLE_WIDTH){1'b0}}, ufi_core2l_rdata_en_full[tile_i][lane_i]};
         end 
      end 

      // Tie off core2l_data for unused connections
      for (pin_i = 0; pin_i < (NUM_OF_RTL_TILES * LANES_PER_TILE * PINS_PER_LANE); ++pin_i)
      begin : non_c2l_pin
         if (PINS_C2L_DRIVEN[pin_i] == 1'b0) begin
            assign `_unused_core2l_data(pin_i) = '0;
         end 
      end
      
   endgenerate
endmodule

`ifdef QUESTA_INTEL_OEM
`pragma questa_oem_00 "EVeqkz9MvDzapiiVw7+udc++m43wu2P9R6Bkf/lfBn9ZttFzW71hzuu9P3yzPlvUUu1GESHEht8oUjkuxH5nYF5m2Y4yEaZOsor1W+qakklkcNM5gczDB8G/zUljAitcohcjlH9xX4F5r3RrLLQB1HrtXmnxKKrsVs2RsxKt4plRYJGUCxRjs6twKgr6lps1q22taZT7+7dZh7dYE0uKJfWB1PYeKR+rbOxvrAyMNm17yDrEN5tN07/Ds5pM+c3mBk5k3/Lfm7OY8/PIK6tH8hCR1xx1LkZA5p5wr8GzWkhPjRqvFihOZsLCY2SSYu6dfDGX+NXNCvLPPzpk+UL/uyf0ZIhnc3u+v8Crd6t6w3bZWD7Lrt6E3meMlk8hPaaVS3NmzUOeKSnl8WhrTC0fFZ5L2rIXo3+VJSGckDSSuP+DHLQPfw9wz9LInvjy2bc4sjPMW3fo5/0Z1AKvV8SFi6hQgrXoxgyoq3EswUDaBqT8M9dcYzMPzpigsnGjayLg1R/L/ICLWoeLBl85aSP2o9LIx4iaZj0yXP4OJNgI05WgCi8jJ4JADLsD9pei8sVjuiRI8TSXomklraO35J0ZsPqq2YrBgWwTv2hfcGB4Y3GkjteBkw3hdBzvr8DPkZCF/aA1Rm/3Hgs4NWD2dmNOzCn+A+31PVMiIV2pQw3ohHwPzNSEmKlsTba02DpNPkJYrg46ysmllSTBLycV6RQjPfMQkQ3e68wieu4S6dmG031mZBy1ksFLu4nZzJ7NOglMtWtXOUHsurL1Nc/qqVnaTrBUQ1PIbpIT/ND7jI2sdIPEZT3Xgq0RC1EX66AMluedfLwa2kVXV3/TnrRRXbVAEhp3z5nts2RzwVCAPNtFctAenf5tN6QnNbfu3+pFz9LvIy6vowx2Q64tbv5qIm0aHzDAh5BZBfhQ3aI2ImqlG8eovH/ByB4xqjmcAgMPIScVBaZUCjr4MEdYoYH9c/MR9Sd1dmjpSo6RrTiki0GF709rkn+6aoKYRYRbenZkvit+"
`endif
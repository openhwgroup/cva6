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
// soft logic interacts with the Avalon ST port of the HMC
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

`define _core2l_datamask(_port_i, _phase_i) core2l_data\
   [`_get_tile(WM_PINLOC, _port_i)]\
   [`_get_lane(WM_PINLOC, _port_i)]\
   [(`_get_pin(WM_PINLOC, _port_i) * 8) + _phase_i]
      
`define _l2core_data(_port_i, _phase_i) l2core_data\
   [`_get_tile(RD_PINLOC, _port_i)]\
   [`_get_lane(RD_PINLOC, _port_i)]\
   [(`_get_pin(RD_PINLOC, _port_i) * 8) + _phase_i]
   
`define _unused_core2l_data(_pin_i) core2l_data\
   [_pin_i / (PINS_PER_LANE * LANES_PER_TILE)]\
   [(_pin_i / PINS_PER_LANE) % LANES_PER_TILE]\
   [((_pin_i % PINS_PER_LANE) * 8) +: 8]
   
module altera_emif_arch_fm_hmc_ast_data_if #(
   parameter PINS_PER_LANE                  = 1,
   parameter LANES_PER_TILE                 = 1,
   parameter NUM_OF_RTL_TILES               = 1,
   
   // Parameters describing HMC front-end ports
   parameter NUM_OF_HMC_PORTS               = 1,
   
   // Definition of port widths for "ctrl_ast_wr" interface (auto-generated)
   parameter PORT_CTRL_AST_WR_DATA_WIDTH    = 1,   

   // Definition of port widths for "ctrl_ast_rd" interface (auto-generated)
   parameter PORT_CTRL_AST_RD_DATA_WIDTH    = 1,

   // Pin indexes of data signals
   parameter PORT_MEM_D_PINLOC              = 10'b0000000000,
   parameter PORT_MEM_DQ_PINLOC             = 10'b0000000000,
   parameter PORT_MEM_Q_PINLOC              = 10'b0000000000,
   
   // Pin indexes of write data mask signals
   parameter PORT_MEM_DM_PINLOC             = 10'b0000000000,
   parameter PORT_MEM_DBI_N_PINLOC          = 10'b0000000000,
   parameter PORT_MEM_BWS_N_PINLOC          = 10'b0000000000,
   
   // Parameter indicating the core-2-lane connection of a pin is actually driven
   parameter PINS_C2L_DRIVEN                = 1'b0
) (
   // Signals between core and data lanes
   output logic [NUM_OF_RTL_TILES-1:0][LANES_PER_TILE-1:0][PINS_PER_LANE * 8 - 1:0]  core2l_data,
   input  logic [NUM_OF_RTL_TILES-1:0][LANES_PER_TILE-1:0][PINS_PER_LANE * 8 - 1:0]  l2core_data,

   // FM IOSS C2P restrictions requires C2P OEs to be 8 bits per lane
   output logic [NUM_OF_RTL_TILES-1:0][LANES_PER_TILE-1:0][47:0]                     core2l_oe,
   
   // AST data signals between core and data lanes when HMC is used
   input  logic [PORT_CTRL_AST_WR_DATA_WIDTH-1:0]                                    ast_wr_data_0,
   output logic [PORT_CTRL_AST_RD_DATA_WIDTH-1:0]                                    ast_rd_data_0,
   
   input  logic [PORT_CTRL_AST_WR_DATA_WIDTH-1:0]                                    ast_wr_data_1,
   output logic [PORT_CTRL_AST_RD_DATA_WIDTH-1:0]                                    ast_rd_data_1
);
   timeunit 1ns;
   timeprecision 1ps;

   localparam RD_PINLOC = (`_get_pin_count(PORT_MEM_DQ_PINLOC) != 0 ? PORT_MEM_DQ_PINLOC : PORT_MEM_Q_PINLOC);
   localparam WD_PINLOC = (`_get_pin_count(PORT_MEM_DQ_PINLOC) != 0 ? PORT_MEM_DQ_PINLOC : PORT_MEM_D_PINLOC);
   localparam WM_PINLOC = (`_get_pin_count(PORT_MEM_DM_PINLOC) != 0 ? PORT_MEM_DM_PINLOC : (`_get_pin_count(PORT_MEM_DBI_N_PINLOC) != 0 ? PORT_MEM_DBI_N_PINLOC : PORT_MEM_BWS_N_PINLOC));
   
   localparam NUM_RD_PINS = `_get_pin_count(RD_PINLOC);
   localparam NUM_WD_PINS = `_get_pin_count(WD_PINLOC);
   localparam NUM_WM_PINS = `_get_pin_count(WM_PINLOC);

   // The write data bus includes both data (LSBs) and data mask (MSBs). Here we calculate the width of both.
   localparam NUM_OF_AST_REAL_WR_DATA_WIDTH = PORT_CTRL_AST_RD_DATA_WIDTH;
   localparam NUM_OF_AST_BYTE_EN_WIDTH = PORT_CTRL_AST_WR_DATA_WIDTH - NUM_OF_AST_REAL_WR_DATA_WIDTH;
   
   localparam NUM_RD_PINS_PER_HMC_PORT = (NUM_OF_HMC_PORTS > 0) ? (NUM_RD_PINS / NUM_OF_HMC_PORTS) : 0;
   localparam NUM_WD_PINS_PER_HMC_PORT = (NUM_OF_HMC_PORTS > 0) ? (NUM_WD_PINS / NUM_OF_HMC_PORTS) : 0;
   localparam NUM_WM_PINS_PER_HMC_PORT = (NUM_OF_HMC_PORTS > 0) ? (NUM_WM_PINS / NUM_OF_HMC_PORTS) : 0;
   
   localparam NUM_OF_RD_PHASES_PER_HMC_PORT = PORT_CTRL_AST_RD_DATA_WIDTH / NUM_RD_PINS_PER_HMC_PORT;
   localparam NUM_OF_WD_PHASES_PER_HMC_PORT = NUM_OF_AST_REAL_WR_DATA_WIDTH / NUM_WD_PINS_PER_HMC_PORT;
   localparam NUM_OF_WM_PHASES_PER_HMC_PORT = (NUM_WM_PINS == 0) ? 0 : (NUM_OF_AST_BYTE_EN_WIDTH / NUM_WM_PINS_PER_HMC_PORT);
   
   assign core2l_oe = '1;
  
   generate
      genvar port_i;
      genvar phase_i;
      genvar pin_i;

      // Map Avalon-ST writedata signal to lanes' write data bus
      for (port_i = 0; port_i < NUM_WD_PINS; ++port_i)
      begin : wd_port
         for (phase_i = 0; phase_i < NUM_OF_WD_PHASES_PER_HMC_PORT; ++phase_i)
         begin : phase
            if (port_i < NUM_WD_PINS_PER_HMC_PORT) begin
               assign `_core2l_data(port_i, phase_i) = ast_wr_data_0[phase_i * NUM_WD_PINS_PER_HMC_PORT + port_i];
            end else begin
               assign `_core2l_data(port_i, phase_i) = ast_wr_data_1[phase_i * NUM_WD_PINS_PER_HMC_PORT + port_i - NUM_WD_PINS_PER_HMC_PORT];
            end
         end
      end

      // Map Avalon-ST byte-enable signal to lanes' write data bus
      for (port_i = 0; port_i < NUM_WM_PINS; ++port_i)
      begin : wm_port
         for (phase_i = 0; phase_i < NUM_OF_WM_PHASES_PER_HMC_PORT; ++phase_i)
         begin : phase
            if (port_i < NUM_WM_PINS_PER_HMC_PORT) begin
               assign `_core2l_datamask(port_i, phase_i) = ast_wr_data_0[(NUM_OF_WD_PHASES_PER_HMC_PORT * NUM_WD_PINS_PER_HMC_PORT) + (phase_i * NUM_WM_PINS_PER_HMC_PORT + port_i)];
            end else begin
               assign `_core2l_datamask(port_i, phase_i) = ast_wr_data_1[(NUM_OF_WD_PHASES_PER_HMC_PORT * NUM_WD_PINS_PER_HMC_PORT) + (phase_i * NUM_WM_PINS_PER_HMC_PORT + port_i - NUM_WM_PINS_PER_HMC_PORT)];
            end
         end
      end
      
      // Map lanes' read data bus to Avalon-ST readdata signal
      for (port_i = 0; port_i < NUM_RD_PINS; ++port_i)
      begin : rd_port
         for (phase_i = 0; phase_i < NUM_OF_RD_PHASES_PER_HMC_PORT; ++phase_i)
         begin : phase
            if (port_i < NUM_RD_PINS_PER_HMC_PORT) begin
               assign ast_rd_data_0[phase_i * NUM_RD_PINS_PER_HMC_PORT + port_i] = `_l2core_data(port_i, phase_i);
            end else begin
               assign ast_rd_data_1[phase_i * NUM_RD_PINS_PER_HMC_PORT + port_i - NUM_RD_PINS_PER_HMC_PORT] = `_l2core_data(port_i, phase_i);
            end
         end
      end

      // Tie off unused phases for core2l_data for the write data pins
      for (port_i = 0; port_i < NUM_WD_PINS; ++port_i)
      begin : wd_port_unused
         for (phase_i = NUM_OF_WD_PHASES_PER_HMC_PORT; phase_i < 8; ++phase_i)
         begin : unused_phase
            assign `_core2l_data(port_i, phase_i) = 1'b0;
         end
      end

      // Tie off unused phases for core2l_data for the write data mask pins
      for (port_i = 0; port_i < NUM_WM_PINS; ++port_i)
      begin : wm_port_unused
         for (phase_i = NUM_OF_WM_PHASES_PER_HMC_PORT; phase_i < 8; ++phase_i)
         begin : unused_phase
            assign `_core2l_datamask(port_i, phase_i) = 1'b0;
         end
      end
      
      // Tie off core2l_data for unused connections
      for (pin_i = 0; pin_i < (NUM_OF_RTL_TILES * LANES_PER_TILE * PINS_PER_LANE); ++pin_i)
      begin : non_c2l_pin
         if (PINS_C2L_DRIVEN[pin_i] == 1'b0) 
            assign `_unused_core2l_data(pin_i) = '0;
      end
      
      // Tie off the read data ports if they're not used
      if (NUM_OF_HMC_PORTS < 1) begin
         assign ast_rd_data_0 = '0;
      end
      
      if (NUM_OF_HMC_PORTS < 2) begin
         assign ast_rd_data_1 = '0;
      end
   endgenerate
endmodule


`ifdef QUESTA_INTEL_OEM
`pragma questa_oem_00 "EVeqkz9MvDzapiiVw7+udc++m43wu2P9R6Bkf/lfBn9ZttFzW71hzuu9P3yzPlvUUu1GESHEht8oUjkuxH5nYF5m2Y4yEaZOsor1W+qakklkcNM5gczDB8G/zUljAitcohcjlH9xX4F5r3RrLLQB1HrtXmnxKKrsVs2RsxKt4plRYJGUCxRjs6twKgr6lps1q22taZT7+7dZh7dYE0uKJfWB1PYeKR+rbOxvrAyMNm0XkvqozUSoPu/dpPG/oqhMfpedxct7ldg1ZwJbEixblVCvcTEk9ES/Mr6twVic02FgL0h0P37Lb2dfmLe7DKNXtqavYPEm4QhXOMpBmcwl6idM43mzhKs7q1dGozpIslSQ1F5IxpMiiqfXv2mvaYcWtvC6GFlRELjOeiiGnQq2BnPp7ebAyYUGPX9vW6WE2SH7c5UgmpyUqKFIh5Ye1rTK6HVjzPgQjEY2Oxu/ykp43PbYbDri2XWC41b5rcUMpJ/eqPBBNKnEdvfP2UB9q6LvSZ3laA0SNC4ApWDZIGp9kFN3eQiuKvTHJRf74H/YRT9tV5kI6X40dwqG7KEjVFSuLd5rRE7k5mp/26W3vf9sboe7KbLdy78bC5A9y55rxnEROw63ZiB+4Wx6w/x0W2mxk1MHV+0c9S+Dxa3m+iPw2oFSY7M4dw3muCyFk7IFblA9o7bNaKw9OIbbAkcatHhfdVoHSHtI29o+nxVdi+3FKKPKCBSDh7ZYQys4WqV6zJNX8RMRyetESuA6PqXWwY9EcCHMzRCDq3f1lnY8u866EIGM1f0jOF/zGu2wD0xOTSUNjDHlutW8Cfv5e4goieOBH65/V9439QQPXBojL6G9A+SqiWKEJ3PhaEaPf5oLz3WjVE+kSU0l9ippoJv/dIqlAI4eZnHJg99lLPDB3PGflg0j3lYnjOiCY8BHO4O8ohYPL2CPg4tyKoiFxHLYTEp/9C7b5yGQSq/s5gCZM26rXelBTup99IuNLrn34Rt6dq2FV7XSFmJ++8fYJSoRqeGZ"
`endif
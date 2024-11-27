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
// This module implements the gearbox logic to compress the number of wire
// connections to the IOSSM debug port.
//
///////////////////////////////////////////////////////////////////////////////

module altera_emif_f2c_gearbox #(
   // Port widths for core debug access
   parameter PORT_CAL_DEBUG_ADDRESS_WIDTH              = 1,
   parameter PORT_CAL_DEBUG_BYTEEN_WIDTH               = 1,
   parameter PORT_CAL_DEBUG_RDATA_WIDTH                = 1,
   parameter PORT_CAL_DEBUG_WDATA_WIDTH                = 1
) (
   input  logic                                       clk,
   input  logic                                       reset_n,

   input  logic [PORT_CAL_DEBUG_ADDRESS_WIDTH-1:0]    cal_debug_addr,
   input  logic [PORT_CAL_DEBUG_BYTEEN_WIDTH-1:0]     cal_debug_byteenable,
   input  logic                                       cal_debug_read,
   input  logic                                       cal_debug_write,
   input  logic [PORT_CAL_DEBUG_WDATA_WIDTH-1:0]      cal_debug_write_data,

   output logic [PORT_CAL_DEBUG_RDATA_WIDTH-1:0]      cal_debug_read_data,
   output logic                                       cal_debug_read_data_valid,
   output logic                                       cal_debug_waitrequest,

   input logic  [7:0]                                 soft_nios_read_data,
   input logic                                        soft_nios_rdata_valid_n,
   input logic                                        soft_nios_waitrequest_n,

   output logic                                       soft_nios_read,
   output logic                                       soft_nios_write,
   output logic                                       soft_nios_byteenable,
   output logic [7:0]                                 soft_nios_write_data,
   output logic [6:0]                                 soft_nios_address
);
   timeunit 1ps;
   timeprecision 1ps;

   typedef enum logic [2:0] {
      F2C_IDLE = 3'b000,
      F2C_WAIT = 3'b001,
      F2C_CMD  = 3'b010,
      F2C_RDATA= 3'b100
   } f2c_state_t;

   localparam F2C_RDATA_SHIFT_CNT = PORT_CAL_DEBUG_RDATA_WIDTH / 8;
   localparam F2C_CMD_SHIFT_CNT   = PORT_CAL_DEBUG_BYTEEN_WIDTH;

   logic                                              f2c_cmd_valid;
   logic                                              f2c_cmd_rnw;
   logic [PORT_CAL_DEBUG_ADDRESS_WIDTH-1:0]           f2c_cmd_addr;
   logic [PORT_CAL_DEBUG_BYTEEN_WIDTH-1:0]            f2c_byteenable;
   logic [PORT_CAL_DEBUG_WDATA_WIDTH-1:0]             f2c_write_data;
   logic [PORT_CAL_DEBUG_RDATA_WIDTH-1:0]             f2c_read_data;

   logic [3:0]                                        f2c_cmd_shift;
   logic [3:0]                                        f2c_data_shift;

   logic                                              f2c_cmd_done;
   logic                                              f2c_rdata_done;
   logic                                              f2c_cmd_carry_out;
   logic                                              f2c_data_carry_out;

   f2c_state_t                                        f2c_state /* synthesis ignore_power_up */;

   always_ff @(posedge clk, negedge reset_n) begin
      if (!reset_n)
         f2c_state <= F2C_IDLE;
      else begin
         case (f2c_state)
            F2C_IDLE:
               if (cal_debug_read | cal_debug_write)
                  f2c_state <= F2C_WAIT;
            F2C_WAIT:
               if (~soft_nios_waitrequest_n)
                  f2c_state <= F2C_CMD;
            F2C_CMD:
               if (f2c_cmd_done)
                  f2c_state <= f2c_cmd_rnw ? F2C_RDATA : F2C_IDLE;
            F2C_RDATA:
               if (f2c_rdata_done)
                  f2c_state <= F2C_IDLE;
            default:
               f2c_state <= F2C_IDLE;
         endcase
      end
   end

   always_ff @(posedge clk, negedge reset_n) begin
      if (!reset_n) begin
         f2c_cmd_rnw     <= 1'b0;
         f2c_cmd_addr    <=  'b0;
         f2c_byteenable  <=  'b0;
         f2c_write_data  <=  'b0;
         f2c_cmd_shift   <=  'b0;
         f2c_data_shift  <=  'b0;
      end else if (f2c_state == F2C_IDLE) begin
         f2c_cmd_rnw     <=   cal_debug_read;
         f2c_cmd_addr    <=   cal_debug_addr;
         f2c_byteenable  <=   cal_debug_byteenable;
         f2c_write_data  <=   cal_debug_write_data;
         f2c_cmd_shift   <=  'b0;
         f2c_data_shift  <=  'b0;
      end else if (f2c_state == F2C_CMD) begin
         {f2c_cmd_carry_out, f2c_cmd_shift} <=  f2c_cmd_shift + 1;
         f2c_cmd_addr    <=  {7'b0,f2c_cmd_addr   [PORT_CAL_DEBUG_ADDRESS_WIDTH - 1 : 7]};
         f2c_byteenable  <=  {1'b0,f2c_byteenable [PORT_CAL_DEBUG_BYTEEN_WIDTH  - 1 : 1]};
         f2c_write_data  <=  {8'b0,f2c_write_data [PORT_CAL_DEBUG_WDATA_WIDTH   - 1 : 8]};
      end else if (f2c_state == F2C_RDATA && ~soft_nios_rdata_valid_n) begin
         {f2c_data_carry_out, f2c_data_shift} <=  f2c_data_shift + 1;
         f2c_read_data   <=  {soft_nios_read_data, f2c_read_data[PORT_CAL_DEBUG_RDATA_WIDTH - 1 : 8]};
      end
   end

   always_ff @(posedge clk, negedge reset_n) begin
      if (!reset_n)
         cal_debug_read_data_valid <= 1'b0;
      else
         cal_debug_read_data_valid <= f2c_rdata_done;
   end

   assign f2c_cmd_valid            = f2c_state == F2C_CMD;
   assign f2c_cmd_done             = f2c_cmd_shift  == (F2C_CMD_SHIFT_CNT   - 1);
   assign f2c_rdata_done           = f2c_data_shift == (F2C_RDATA_SHIFT_CNT - 1);

   assign soft_nios_read           = f2c_cmd_valid  &  f2c_cmd_rnw;
   assign soft_nios_write          = f2c_cmd_valid  & ~f2c_cmd_rnw;
   assign soft_nios_byteenable     = f2c_byteenable [0];
   assign soft_nios_write_data     = f2c_write_data [7:0];
   assign soft_nios_address        = f2c_cmd_addr   [6:0];

   assign cal_debug_waitrequest    = f2c_state != F2C_IDLE;
   assign cal_debug_read_data      = f2c_read_data;

endmodule
`ifdef QUESTA_INTEL_OEM
`pragma questa_oem_00 "sfv4CgBD2gRw66FfSic/D/DxyUF4ju6abSGjNZTz+XJ5wNcp1RmzgamT61rscvjMkkNKCYCGE4Hkry++3eL2fSJkmOtrYLQextJ2AFr2kX/6sa63SwNG1Dg8CndZgqHpcPsbI8J/52/6EA/5eQJiUNmwpEDzzugi2WpUBRBy4gGrSJ7A8zUzUrkHlWNSHE1mVOTkuXrL/BUqA6hBwwkS7qZD/J3TRyAu6L9p+9tB0EBIioGIcwebGLngzwkT26A7K1SYyh9Dtiac9CerfvFZcK7Sg5dxGmob6a6YHlOjHgxgTAJfWGmg9lJmaH2CWRDnu0TGIto6A0JDLdyo1DDH4xDr12EuwtDrBAjsPgqUebpmVU1ybjm4TYcJj/AMqFqoU5LxerYQ2a99pjJ/ssQDQLWyooHVX74eCxsTnmMuPm/aoYF2IrWT+TN8zan+zKrydptRlQ7eRZZkOvOIadDHLBkEYfQFijyq0W8punO2tFyECjnB3RTgfEeHEXC3apKnn7ek5S5rKJ6RT9hyYVDxJC85a/LaLIrobdZQHtV+QGL0ZS28XJ4yVZ9OLSc5QHLUG1djNtoEbZ7GFeGXurxO4efq+Dg5T9s/FTdouXm/oo5a2hGYAJQE0W3a73xlwhdsszCM3Ml+7+xjCpdcUl2bLcfM+tvIvIeTH+cijMGf6OZL47JY2IogcSd8deavB6h+4WNun4kDom0YSBWepSH/kEWP7/Gz7uI9hxyO3N8gh/PIyO8tvg1ALVEgiTwIeergUGRwuDC9o9m4otU97aiHGDeyBMwTGZ2Jm2DOTBTLvTf5jFnsznVrPoqJWTFqWtvTr3+e3eW+Y+V6CyFzP1Zwj/QIuH5wXJ6RVZSmfuZKgyUwMkjYrlQzjtTYmDjthbxv+sJ+LFLW18jyTpt96JNjn9JKmIlFFt/sTVgRsLqU5sOAHSQuZiHxIkAjRccPG8dHmpXKS9G3jDSAa9fju7CtRnXvXJrjUWjEfqG6FF1Rz5c5PrQyCiLTiTyMkodlMzKQ"
`endif
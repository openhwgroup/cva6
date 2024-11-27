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



module altera_emif_cal_iossm #(
   // IOSSM parameters
   parameter IOSSM_CODE_HEX_FILENAME         = "",
   parameter IOSSM_USE_MODEL                 = 1,

   parameter IOSSM_SIM_GPT_HEX_FILENAME          = "",
   parameter IOSSM_SYNTH_GPT_HEX_FILENAME        = "",
   parameter IOSSM_SIM_NIOS_PERIOD_PS            = 0,
   
   // Debug Parameters
   parameter USE_SYNTH_FOR_SIM                      = 0,
   parameter DIAG_EXPORT_VJI                        = 0,

   // Port widths for core debug access
   parameter PORT_CAL_DEBUG_ADDRESS_WIDTH            = 1,
   parameter PORT_CAL_DEBUG_BYTEEN_WIDTH             = 1,
   parameter PORT_CAL_DEBUG_RDATA_WIDTH              = 1,
   parameter PORT_CAL_DEBUG_WDATA_WIDTH              = 1,

    // Port widths for core debug access
   parameter PORT_CALBUS_ADDRESS_WIDTH               = 1,
   parameter PORT_CALBUS_WDATA_WIDTH                 = 1,
   parameter PORT_CALBUS_RDATA_WIDTH                 = 1,
   parameter PORT_CALBUS_SEQ_PARAM_TBL_WIDTH         = 1,
   

   // Global param table data
   parameter SEQ_GPT_GLOBAL_PAR_VER          = 0,
   parameter SEQ_GPT_NIOS_C_VER              = 0,
   parameter SEQ_GPT_COLUMN_ID               = 0,
   parameter SEQ_GPT_NUM_IOPACKS             = 0,
   parameter SEQ_GPT_NIOS_CLK_FREQ_KHZ       = 0,
   parameter SEQ_GPT_PARAM_TABLE_SIZE        = 0,
   parameter SEQ_GPT_GLOBAL_SKIP_STEPS       = 0,
   parameter SEQ_GPT_GLOBAL_CAL_CONFIG       = 0,
   parameter SEQ_GPT_SLAVE_CLK_DIVIDER       = 0,

   parameter SEQ_USE_SIM_PARAMS = "",
   parameter SIM_SEQ_GPT_NIOS_CLK_FREQ_KHZ   = 0,
   parameter SIM_SEQ_GPT_GLOBAL_SKIP_STEPS   = 0,

   // Hard-Nios debug ports
   parameter PORT_VJI_IR_IN_WIDTH                    = 1,
   parameter PORT_VJI_IR_OUT_WIDTH                   = 1,

   // Enable/disable Abstract PHY
   parameter NUM_CALBUS_USED                         = 1,
   parameter USE_SOFT_NIOS                           = 0
) (

   // EMIF calibration bus interfaces  
   output logic                                          calbus_clk,

   output logic                                          calbus_read_0,
   output logic                                          calbus_write_0,
   output logic [PORT_CALBUS_ADDRESS_WIDTH-1:0]          calbus_address_0,
   input  logic [PORT_CALBUS_RDATA_WIDTH-1:0]            calbus_rdata_0,
   output logic [PORT_CALBUS_WDATA_WIDTH-1:0]            calbus_wdata_0,
   input  logic [PORT_CALBUS_SEQ_PARAM_TBL_WIDTH-1:0]    calbus_seq_param_tbl_0,

   output logic                                          calbus_read_1,
   output logic                                          calbus_write_1,
   output logic [PORT_CALBUS_ADDRESS_WIDTH-1:0]          calbus_address_1,
   input  logic [PORT_CALBUS_RDATA_WIDTH-1:0]            calbus_rdata_1,
   output logic [PORT_CALBUS_WDATA_WIDTH-1:0]            calbus_wdata_1,
   input  logic [PORT_CALBUS_SEQ_PARAM_TBL_WIDTH-1:0]    calbus_seq_param_tbl_1,

   output logic                                          calbus_read_2,
   output logic                                          calbus_write_2,
   output logic [PORT_CALBUS_ADDRESS_WIDTH-1:0]          calbus_address_2,
   input  logic [PORT_CALBUS_RDATA_WIDTH-1:0]            calbus_rdata_2,
   output logic [PORT_CALBUS_WDATA_WIDTH-1:0]            calbus_wdata_2,
   input  logic [PORT_CALBUS_SEQ_PARAM_TBL_WIDTH-1:0]    calbus_seq_param_tbl_2,

   output logic                                          calbus_read_3,
   output logic                                          calbus_write_3,
   output logic [PORT_CALBUS_ADDRESS_WIDTH-1:0]          calbus_address_3,
   input  logic [PORT_CALBUS_RDATA_WIDTH-1:0]            calbus_rdata_3,
   output logic [PORT_CALBUS_WDATA_WIDTH-1:0]            calbus_wdata_3,
   input  logic [PORT_CALBUS_SEQ_PARAM_TBL_WIDTH-1:0]    calbus_seq_param_tbl_3,

   output logic                                          calbus_read_4,
   output logic                                          calbus_write_4,
   output logic [PORT_CALBUS_ADDRESS_WIDTH-1:0]          calbus_address_4,
   input  logic [PORT_CALBUS_RDATA_WIDTH-1:0]            calbus_rdata_4,
   output logic [PORT_CALBUS_WDATA_WIDTH-1:0]            calbus_wdata_4,
   input  logic [PORT_CALBUS_SEQ_PARAM_TBL_WIDTH-1:0]    calbus_seq_param_tbl_4,

   output logic                                          calbus_read_5,
   output logic                                          calbus_write_5,
   output logic [PORT_CALBUS_ADDRESS_WIDTH-1:0]          calbus_address_5,
   input  logic [PORT_CALBUS_RDATA_WIDTH-1:0]            calbus_rdata_5,
   output logic [PORT_CALBUS_WDATA_WIDTH-1:0]            calbus_wdata_5,
   input  logic [PORT_CALBUS_SEQ_PARAM_TBL_WIDTH-1:0]    calbus_seq_param_tbl_5,

   output logic                                          calbus_read_6,
   output logic                                          calbus_write_6,
   output logic [PORT_CALBUS_ADDRESS_WIDTH-1:0]          calbus_address_6,
   input  logic [PORT_CALBUS_RDATA_WIDTH-1:0]            calbus_rdata_6,
   output logic [PORT_CALBUS_WDATA_WIDTH-1:0]            calbus_wdata_6,
   input  logic [PORT_CALBUS_SEQ_PARAM_TBL_WIDTH-1:0]    calbus_seq_param_tbl_6,

   output logic                                          calbus_read_7,
   output logic                                          calbus_write_7,
   output logic [PORT_CALBUS_ADDRESS_WIDTH-1:0]          calbus_address_7,
   input  logic [PORT_CALBUS_RDATA_WIDTH-1:0]            calbus_rdata_7,
   output logic [PORT_CALBUS_WDATA_WIDTH-1:0]            calbus_wdata_7,
   input  logic [PORT_CALBUS_SEQ_PARAM_TBL_WIDTH-1:0]    calbus_seq_param_tbl_7,

   output logic                                          calbus_read_8,
   output logic                                          calbus_write_8,
   output logic [PORT_CALBUS_ADDRESS_WIDTH-1:0]          calbus_address_8,
   input  logic [PORT_CALBUS_RDATA_WIDTH-1:0]            calbus_rdata_8,
   output logic [PORT_CALBUS_WDATA_WIDTH-1:0]            calbus_wdata_8,
   input  logic [PORT_CALBUS_SEQ_PARAM_TBL_WIDTH-1:0]    calbus_seq_param_tbl_8,

   output logic                                          calbus_read_9,
   output logic                                          calbus_write_9,
   output logic [PORT_CALBUS_ADDRESS_WIDTH-1:0]          calbus_address_9,
   input  logic [PORT_CALBUS_RDATA_WIDTH-1:0]            calbus_rdata_9,
   output logic [PORT_CALBUS_WDATA_WIDTH-1:0]            calbus_wdata_9,
   input  logic [PORT_CALBUS_SEQ_PARAM_TBL_WIDTH-1:0]    calbus_seq_param_tbl_9,

   output logic                                          calbus_read_10,
   output logic                                          calbus_write_10,
   output logic [PORT_CALBUS_ADDRESS_WIDTH-1:0]          calbus_address_10,
   input  logic [PORT_CALBUS_RDATA_WIDTH-1:0]            calbus_rdata_10,
   output logic [PORT_CALBUS_WDATA_WIDTH-1:0]            calbus_wdata_10,
   input  logic [PORT_CALBUS_SEQ_PARAM_TBL_WIDTH-1:0]    calbus_seq_param_tbl_10,

   output logic                                          calbus_read_11,
   output logic                                          calbus_write_11,
   output logic [PORT_CALBUS_ADDRESS_WIDTH-1:0]          calbus_address_11,
   input  logic [PORT_CALBUS_RDATA_WIDTH-1:0]            calbus_rdata_11,
   output logic [PORT_CALBUS_WDATA_WIDTH-1:0]            calbus_wdata_11,
   input  logic [PORT_CALBUS_SEQ_PARAM_TBL_WIDTH-1:0]    calbus_seq_param_tbl_11,

   output logic                                          calbus_read_12,
   output logic                                          calbus_write_12,
   output logic [PORT_CALBUS_ADDRESS_WIDTH-1:0]          calbus_address_12,
   input  logic [PORT_CALBUS_RDATA_WIDTH-1:0]            calbus_rdata_12,
   output logic [PORT_CALBUS_WDATA_WIDTH-1:0]            calbus_wdata_12,
   input  logic [PORT_CALBUS_SEQ_PARAM_TBL_WIDTH-1:0]    calbus_seq_param_tbl_12,

   output logic                                          calbus_read_13,
   output logic                                          calbus_write_13,
   output logic [PORT_CALBUS_ADDRESS_WIDTH-1:0]          calbus_address_13,
   input  logic [PORT_CALBUS_RDATA_WIDTH-1:0]            calbus_rdata_13,
   output logic [PORT_CALBUS_WDATA_WIDTH-1:0]            calbus_wdata_13,
   input  logic [PORT_CALBUS_SEQ_PARAM_TBL_WIDTH-1:0]    calbus_seq_param_tbl_13,

   output logic                                          calbus_read_14,
   output logic                                          calbus_write_14,
   output logic [PORT_CALBUS_ADDRESS_WIDTH-1:0]          calbus_address_14,
   input  logic [PORT_CALBUS_RDATA_WIDTH-1:0]            calbus_rdata_14,
   output logic [PORT_CALBUS_WDATA_WIDTH-1:0]            calbus_wdata_14,
   input  logic [PORT_CALBUS_SEQ_PARAM_TBL_WIDTH-1:0]    calbus_seq_param_tbl_14,

   output logic                                          calbus_read_15,
   output logic                                          calbus_write_15,
   output logic [PORT_CALBUS_ADDRESS_WIDTH-1:0]          calbus_address_15,
   input  logic [PORT_CALBUS_RDATA_WIDTH-1:0]            calbus_rdata_15,
   output logic [PORT_CALBUS_WDATA_WIDTH-1:0]            calbus_wdata_15,
   input  logic [PORT_CALBUS_SEQ_PARAM_TBL_WIDTH-1:0]    calbus_seq_param_tbl_15,

   // Input clock/reset intended for core logic connected to the Avalon slave port of the sequencer CPU.
   // The "out" clock/reset is intended for daisy-chaining logic from multiple interfaces.
   // Ports for "cal_debug" interface
   input  logic                                          cal_debug_clk,
   input  logic                                          cal_debug_reset_n,
   input  logic [PORT_CAL_DEBUG_ADDRESS_WIDTH-1:0]       cal_debug_addr,
   input  logic [PORT_CAL_DEBUG_BYTEEN_WIDTH-1:0]        cal_debug_byteenable,
   input  logic                                          cal_debug_read,
   input  logic                                          cal_debug_write,
   input  logic [PORT_CAL_DEBUG_WDATA_WIDTH-1:0]         cal_debug_write_data,
   output logic [PORT_CAL_DEBUG_RDATA_WIDTH-1:0]         cal_debug_read_data,
   output logic                                          cal_debug_read_data_valid,
   output logic                                          cal_debug_waitrequest,

   // Hard-Nios debug port
   input  logic [1:0] vji_ir_in,
   output logic [1:0] vji_ir_out,
   input  logic       vji_jtag_state_rti,
   input  logic       vji_tck,
   input  logic       vji_tdi,
   output logic       vji_tdo,
   input  logic       vji_virtual_state_cdr,
   input  logic       vji_virtual_state_sdr,
   input  logic       vji_virtual_state_udr,
   input  logic       vji_virtual_state_uir
);
   timeunit 1ns;
   timeprecision 1ps;
   
   // Derive localparam values

   // Typically we synthesize full-calibration behavior for hardware,
   // except when USE_SYNTH_FOR_SIM is set, which allows flows such
   // as post-fit simulation to adopt RTL simulation behavior.
   localparam REMAP_IOSSM_GPT_HEX_FILENAME    = (SEQ_USE_SIM_PARAMS == "on") ? IOSSM_SIM_GPT_HEX_FILENAME : (
                                                (USE_SYNTH_FOR_SIM) ? IOSSM_SIM_GPT_HEX_FILENAME : IOSSM_SYNTH_GPT_HEX_FILENAME );
   localparam REMAP_SEQ_GPT_NIOS_CLK_FREQ_KHZ = (SEQ_USE_SIM_PARAMS == "on") ? SIM_SEQ_GPT_NIOS_CLK_FREQ_KHZ : (
                                                (USE_SYNTH_FOR_SIM) ? SIM_SEQ_GPT_NIOS_CLK_FREQ_KHZ : SEQ_GPT_NIOS_CLK_FREQ_KHZ );
   localparam REMAP_SEQ_GPT_GLOBAL_SKIP_STEPS = (SEQ_USE_SIM_PARAMS == "on") ? SIM_SEQ_GPT_GLOBAL_SKIP_STEPS : (
                                                (USE_SYNTH_FOR_SIM) ? SIM_SEQ_GPT_GLOBAL_SKIP_STEPS : SEQ_GPT_GLOBAL_SKIP_STEPS );
 
   wire           w_vji_cdr_to_the_hard_nios;
   wire  [ 1: 0]  w_vji_ir_in_to_the_hard_nios;
   wire           w_vji_rti_to_the_hard_nios;
   wire           w_vji_sdr_to_the_hard_nios;
   wire           w_vji_tck_to_the_hard_nios;
   wire           w_vji_tdi_to_the_hard_nios;
   wire           w_vji_udr_to_the_hard_nios;
   wire           w_vji_uir_to_the_hard_nios;

   wire  [ 1: 0]  w_sld_vji_ir_out_from_the_hard_nios;
   wire           w_sld_vji_tdo_from_the_hard_nios;
   wire  [ 1: 0]  w_vji_ir_out_from_the_hard_nios;
   wire           w_vji_tdo_from_the_hard_nios;
   
   wire [15:0][PORT_CALBUS_WDATA_WIDTH-1:0]            calbus_rdata_i;
   wire [15:0][PORT_CALBUS_SEQ_PARAM_TBL_WIDTH-1:0]    calbus_seq_param_tbl_i;

   logic  [7:0]                                        soft_nios_read_data;
   logic                                               soft_nios_rdata_valid_n;
   logic                                               soft_nios_waitrequest_n;

   logic                                               soft_nios_read;
   logic                                               soft_nios_write;
   logic                                               soft_nios_byteenable;
   logic [7:0]                                         soft_nios_write_data;
   logic [6:0]                                         soft_nios_address;


   generate if (USE_SOFT_NIOS != 0) begin
       altera_emif_f2c_gearbox #(
           .PORT_CAL_DEBUG_ADDRESS_WIDTH (PORT_CAL_DEBUG_ADDRESS_WIDTH),
           .PORT_CAL_DEBUG_BYTEEN_WIDTH  (PORT_CAL_DEBUG_BYTEEN_WIDTH),
           .PORT_CAL_DEBUG_RDATA_WIDTH   (PORT_CAL_DEBUG_RDATA_WIDTH),
           .PORT_CAL_DEBUG_WDATA_WIDTH   (PORT_CAL_DEBUG_WDATA_WIDTH)
       ) f2c_gearbox_inst (
           .clk                      (cal_debug_clk),
           .reset_n                  (cal_debug_reset_n),

           .cal_debug_addr           (cal_debug_addr),
           .cal_debug_byteenable     (cal_debug_byteenable),
           .cal_debug_read           (cal_debug_read),
           .cal_debug_write          (cal_debug_write),
           .cal_debug_write_data     (cal_debug_write_data),

           .cal_debug_read_data      (cal_debug_read_data),
           .cal_debug_read_data_valid(cal_debug_read_data_valid),
           .cal_debug_waitrequest    (cal_debug_waitrequest),

           .soft_nios_read_data      (soft_nios_read_data),
           .soft_nios_rdata_valid_n  (soft_nios_rdata_valid_n),
           .soft_nios_waitrequest_n  (soft_nios_waitrequest_n),

           .soft_nios_read           (soft_nios_read),
           .soft_nios_write          (soft_nios_write),
           .soft_nios_byteenable     (soft_nios_byteenable),
           .soft_nios_write_data     (soft_nios_write_data),
           .soft_nios_address        (soft_nios_address)
       );
   end else begin
       assign soft_nios_address         = 7'd0;
       assign soft_nios_byteenable      = 1'b0;
       assign soft_nios_write_data      = 8'd0;
       assign soft_nios_read            = 1'b0;
       assign soft_nios_write           = 1'b0;
       assign cal_debug_read_data       = '0;
       assign cal_debug_read_data_valid = '0;
       assign cal_debug_waitrequest     = '0;
   end
   endgenerate

   assign calbus_rdata_i[0] = (NUM_CALBUS_USED > 0) ?  calbus_rdata_0 : 'd0;
   assign calbus_seq_param_tbl_i[0]  = (NUM_CALBUS_USED > 0) ?  calbus_seq_param_tbl_0 : 'd0;
   assign calbus_rdata_i[1] = (NUM_CALBUS_USED > 1) ?  calbus_rdata_1 : 'd0;
   assign calbus_seq_param_tbl_i[1]  = (NUM_CALBUS_USED > 1) ?  calbus_seq_param_tbl_1 : 'd0;
   assign calbus_rdata_i[2] = (NUM_CALBUS_USED > 2) ?  calbus_rdata_2 : 'd0;
   assign calbus_seq_param_tbl_i[2]  = (NUM_CALBUS_USED > 2) ?  calbus_seq_param_tbl_2 : 'd0;
   assign calbus_rdata_i[3] = (NUM_CALBUS_USED > 3) ?  calbus_rdata_3 : 'd0;
   assign calbus_seq_param_tbl_i[3]  = (NUM_CALBUS_USED > 3) ?  calbus_seq_param_tbl_3 : 'd0;
   assign calbus_rdata_i[4] = (NUM_CALBUS_USED > 4) ?  calbus_rdata_4 : 'd0;
   assign calbus_seq_param_tbl_i[4]  = (NUM_CALBUS_USED > 4) ?  calbus_seq_param_tbl_4 : 'd0;
   assign calbus_rdata_i[5] = (NUM_CALBUS_USED > 5) ?  calbus_rdata_5 : 'd0;
   assign calbus_seq_param_tbl_i[5]  = (NUM_CALBUS_USED > 5) ?  calbus_seq_param_tbl_5 : 'd0;
   assign calbus_rdata_i[6] = (NUM_CALBUS_USED > 6) ?  calbus_rdata_6 : 'd0;
   assign calbus_seq_param_tbl_i[6]  = (NUM_CALBUS_USED > 6) ?  calbus_seq_param_tbl_6 : 'd0;
   assign calbus_rdata_i[7] = (NUM_CALBUS_USED > 7) ?  calbus_rdata_7 : 'd0;
   assign calbus_seq_param_tbl_i[7]  = (NUM_CALBUS_USED > 7) ?  calbus_seq_param_tbl_7 : 'd0;
   assign calbus_rdata_i[8] = (NUM_CALBUS_USED > 8) ?  calbus_rdata_8 : 'd0;
   assign calbus_seq_param_tbl_i[8]  = (NUM_CALBUS_USED > 8) ?  calbus_seq_param_tbl_8 : 'd0;
   assign calbus_rdata_i[9] = (NUM_CALBUS_USED > 9) ?  calbus_rdata_9 : 'd0;
   assign calbus_seq_param_tbl_i[9]  = (NUM_CALBUS_USED > 9) ?  calbus_seq_param_tbl_9 : 'd0;
   assign calbus_rdata_i[10] = (NUM_CALBUS_USED > 10) ? calbus_rdata_10 : 'd0;
   assign calbus_seq_param_tbl_i[10] = (NUM_CALBUS_USED > 10) ? calbus_seq_param_tbl_10 : 'd0;
   assign calbus_rdata_i[11] = (NUM_CALBUS_USED > 11) ? calbus_rdata_11 : 'd0;
   assign calbus_seq_param_tbl_i[11] = (NUM_CALBUS_USED > 11) ? calbus_seq_param_tbl_11 : 'd0;
   assign calbus_rdata_i[12] = (NUM_CALBUS_USED > 12) ? calbus_rdata_12 : 'd0;
   assign calbus_seq_param_tbl_i[12] = (NUM_CALBUS_USED > 12) ? calbus_seq_param_tbl_12 : 'd0;
   assign calbus_rdata_i[13] = (NUM_CALBUS_USED > 13) ? calbus_rdata_13 : 'd0;
   assign calbus_seq_param_tbl_i[13] = (NUM_CALBUS_USED > 13) ? calbus_seq_param_tbl_13 : 'd0;
   assign calbus_rdata_i[14] = (NUM_CALBUS_USED > 14) ? calbus_rdata_14 : 'd0;
   assign calbus_seq_param_tbl_i[14] = (NUM_CALBUS_USED > 14) ? calbus_seq_param_tbl_14 : 'd0;
   assign calbus_rdata_i[15] = (NUM_CALBUS_USED > 15) ? calbus_rdata_15 : 'd0;
   assign calbus_seq_param_tbl_i[15] = (NUM_CALBUS_USED > 15) ? calbus_seq_param_tbl_15 : 'd0;

   tennm_iossm # (
      .gpt_ver                       (SEQ_GPT_GLOBAL_PAR_VER),
      .nios_ver                      (SEQ_GPT_NIOS_C_VER),
      .col_id                        (SEQ_GPT_COLUMN_ID),
      .num_iopacks                   (SEQ_GPT_NUM_IOPACKS),
      .pt_size                       (SEQ_GPT_PARAM_TABLE_SIZE),
      .cal_config                    (SEQ_GPT_GLOBAL_CAL_CONFIG),
      .slave_clk_divider             (SEQ_GPT_SLAVE_CLK_DIVIDER),
      .nios_clk_freq                 (REMAP_SEQ_GPT_NIOS_CLK_FREQ_KHZ),
      .skip_steps                    (REMAP_SEQ_GPT_GLOBAL_SKIP_STEPS),
      .parameter_table_hex_file      (REMAP_IOSSM_GPT_HEX_FILENAME),

      .abstract_phy                  ("false"),
      .iossm_sim_clk_period_ps       (IOSSM_SIM_NIOS_PERIOD_PS),
      .nios_calibration_code_hex_file(IOSSM_CODE_HEX_FILENAME),
      .iossm_use_model               (IOSSM_USE_MODEL)
   ) io_ssm (
      .soft_nios_irq                 (4'b0),
      .soft_nios_address             (soft_nios_address),
      .soft_nios_byteenable          (soft_nios_byteenable),
      .soft_nios_clk                 (cal_debug_clk),
      .soft_nios_read                (soft_nios_read),
      .soft_nios_write               (soft_nios_write),
      .soft_nios_write_data          (soft_nios_write_data),
      .soft_nios_read_data           (soft_nios_read_data),
      .soft_nios_rdata_valid         (soft_nios_rdata_valid_n),        
      .soft_nios_waitrequest         (soft_nios_waitrequest_n),

       // IO Subsystem Calibration Bus
      .calbus_clock                  (calbus_clk),

      .calbus_read_0                 (calbus_read_0),
      .calbus_write_0                (calbus_write_0),
      .calbus_address_0              (calbus_address_0),
      .calbus_wdata_0                (calbus_wdata_0),
      .calbus_rdata_0                (calbus_rdata_i[0]),
      .calbus_param_tbl_0            (calbus_seq_param_tbl_i[0]),

      .calbus_read_1                 (calbus_read_1),
      .calbus_write_1                (calbus_write_1),
      .calbus_address_1              (calbus_address_1),
      .calbus_wdata_1                (calbus_wdata_1),
      .calbus_rdata_1                (calbus_rdata_i[1]),
      .calbus_param_tbl_1            (calbus_seq_param_tbl_i[1]),

      .calbus_read_2                 (calbus_read_2),
      .calbus_write_2                (calbus_write_2),
      .calbus_address_2              (calbus_address_2),
      .calbus_wdata_2                (calbus_wdata_2),
      .calbus_rdata_2                (calbus_rdata_i[2]),
      .calbus_param_tbl_2            (calbus_seq_param_tbl_i[2]),

      .calbus_read_3                 (calbus_read_3),
      .calbus_write_3                (calbus_write_3),
      .calbus_address_3              (calbus_address_3),
      .calbus_wdata_3                (calbus_wdata_3),
      .calbus_rdata_3                (calbus_rdata_i[3]),
      .calbus_param_tbl_3            (calbus_seq_param_tbl_i[3]),

      .calbus_read_4                 (calbus_read_4),
      .calbus_write_4                (calbus_write_4),
      .calbus_address_4              (calbus_address_4),
      .calbus_wdata_4                (calbus_wdata_4),
      .calbus_rdata_4                (calbus_rdata_i[4]),
      .calbus_param_tbl_4            (calbus_seq_param_tbl_i[4]),

      .calbus_read_5                 (calbus_read_5),
      .calbus_write_5                (calbus_write_5),
      .calbus_address_5              (calbus_address_5),
      .calbus_wdata_5                (calbus_wdata_5),
      .calbus_rdata_5                (calbus_rdata_i[5]),
      .calbus_param_tbl_5            (calbus_seq_param_tbl_i[5]),

      .calbus_read_6                 (calbus_read_6),
      .calbus_write_6                (calbus_write_6),
      .calbus_address_6              (calbus_address_6),
      .calbus_wdata_6                (calbus_wdata_6),
      .calbus_rdata_6                (calbus_rdata_i[6]),
      .calbus_param_tbl_6            (calbus_seq_param_tbl_i[6]),

      .calbus_read_7                 (calbus_read_7),
      .calbus_write_7                (calbus_write_7),
      .calbus_address_7              (calbus_address_7),
      .calbus_wdata_7                (calbus_wdata_7),
      .calbus_rdata_7                (calbus_rdata_i[7]),
      .calbus_param_tbl_7            (calbus_seq_param_tbl_i[7]),

      .calbus_read_8                 (calbus_read_8),
      .calbus_write_8                (calbus_write_8),
      .calbus_address_8              (calbus_address_8),
      .calbus_wdata_8                (calbus_wdata_8),
      .calbus_rdata_8                (calbus_rdata_i[8]),
      .calbus_param_tbl_8            (calbus_seq_param_tbl_i[8]),

      .calbus_read_9                 (calbus_read_9),
      .calbus_write_9                (calbus_write_9),
      .calbus_address_9              (calbus_address_9),
      .calbus_wdata_9                (calbus_wdata_9),
      .calbus_rdata_9                (calbus_rdata_i[9]),
      .calbus_param_tbl_9            (calbus_seq_param_tbl_i[9]),

      .calbus_read_10                 (calbus_read_10),
      .calbus_write_10                (calbus_write_10),
      .calbus_address_10              (calbus_address_10),
      .calbus_wdata_10                (calbus_wdata_10),
      .calbus_rdata_10                (calbus_rdata_i[10]),
      .calbus_param_tbl_10            (calbus_seq_param_tbl_i[10]),

      .calbus_read_11                 (calbus_read_11),
      .calbus_write_11                (calbus_write_11),
      .calbus_address_11              (calbus_address_11),
      .calbus_wdata_11                (calbus_wdata_11),
      .calbus_rdata_11                (calbus_rdata_i[11]),
      .calbus_param_tbl_11            (calbus_seq_param_tbl_i[11]),

      .calbus_read_12                 (calbus_read_12),
      .calbus_write_12                (calbus_write_12),
      .calbus_address_12              (calbus_address_12),
      .calbus_wdata_12                (calbus_wdata_12),
      .calbus_rdata_12                (calbus_rdata_i[12]),
      .calbus_param_tbl_12            (calbus_seq_param_tbl_i[12]),

      .calbus_read_13                 (calbus_read_13),
      .calbus_write_13                (calbus_write_13),
      .calbus_address_13              (calbus_address_13),
      .calbus_wdata_13                (calbus_wdata_13),
      .calbus_rdata_13                (calbus_rdata_i[13]),
      .calbus_param_tbl_13            (calbus_seq_param_tbl_i[13]),

      .calbus_read_14                 (calbus_read_14),
      .calbus_write_14                (calbus_write_14),
      .calbus_address_14              (calbus_address_14),
      .calbus_wdata_14                (calbus_wdata_14),
      .calbus_rdata_14                (calbus_rdata_i[14]),
      .calbus_param_tbl_14            (calbus_seq_param_tbl_i[14]),

      .calbus_read_15                 (calbus_read_15),
      .calbus_write_15                (calbus_write_15),
      .calbus_address_15              (calbus_address_15),
      .calbus_wdata_15                (calbus_wdata_15),
      .calbus_rdata_15                (calbus_rdata_i[15]),
      .calbus_param_tbl_15            (calbus_seq_param_tbl_i[15]),

      // IO Subsystem Calibration Bus
      .vji_cdr_to_the_hard_nios      (w_vji_cdr_to_the_hard_nios),
      .vji_ir_in_to_the_hard_nios    (w_vji_ir_in_to_the_hard_nios),
      .vji_rti_to_the_hard_nios      (w_vji_rti_to_the_hard_nios),
      .vji_sdr_to_the_hard_nios      (w_vji_sdr_to_the_hard_nios),
      .vji_tck_to_the_hard_nios      (w_vji_tck_to_the_hard_nios),
      .vji_tdi_to_the_hard_nios      (w_vji_tdi_to_the_hard_nios),
      .vji_udr_to_the_hard_nios      (w_vji_udr_to_the_hard_nios),
      .vji_uir_to_the_hard_nios      (w_vji_uir_to_the_hard_nios),
      .vji_ir_out_from_the_hard_nios (w_vji_ir_out_from_the_hard_nios),
      .vji_tdo_from_the_hard_nios    (w_vji_tdo_from_the_hard_nios)
   );

   assign w_vji_cdr_to_the_hard_nios   = DIAG_EXPORT_VJI ? vji_virtual_state_cdr : 1'b0;
   assign w_vji_ir_in_to_the_hard_nios = DIAG_EXPORT_VJI ? vji_ir_in : 2'b00;
   assign w_vji_rti_to_the_hard_nios   = DIAG_EXPORT_VJI ? vji_jtag_state_rti : 1'b0;
   assign w_vji_sdr_to_the_hard_nios   = DIAG_EXPORT_VJI ? vji_virtual_state_sdr : 1'b0;
   assign w_vji_tck_to_the_hard_nios   = DIAG_EXPORT_VJI ? vji_tck : 1'b0;
   assign w_vji_tdi_to_the_hard_nios   = DIAG_EXPORT_VJI ? vji_tdi : 1'b0;
   assign w_vji_udr_to_the_hard_nios   = DIAG_EXPORT_VJI ? vji_virtual_state_udr : 1'b0;
   assign w_vji_uir_to_the_hard_nios   = DIAG_EXPORT_VJI ? vji_virtual_state_uir : 1'b0;
   assign vji_ir_out                   = DIAG_EXPORT_VJI ? w_vji_ir_out_from_the_hard_nios : 2'b0;
   assign vji_tdo                      = DIAG_EXPORT_VJI ? w_vji_tdo_from_the_hard_nios : 1'b0;

endmodule
`ifdef QUESTA_INTEL_OEM
`pragma questa_oem_00 "sfv4CgBD2gRw66FfSic/D/DxyUF4ju6abSGjNZTz+XJ5wNcp1RmzgamT61rscvjMkkNKCYCGE4Hkry++3eL2fSJkmOtrYLQextJ2AFr2kX/6sa63SwNG1Dg8CndZgqHpcPsbI8J/52/6EA/5eQJiUNmwpEDzzugi2WpUBRBy4gGrSJ7A8zUzUrkHlWNSHE1mVOTkuXrL/BUqA6hBwwkS7qZD/J3TRyAu6L9p+9tB0ECj3HSUaZMQdsHOEoejOcwJ2RhJ9P4QDVEXGenDAmBQiJAPz6SAV4DqS0an68FB0ZOw3u6Fz9ZnsNCxHESqqKIhmHXeOOJqT0TMS7OxARNfiGSYsGZkXP2aOsQbPMyMl9Na0FpG3tX2nCq+YzVLsQyswtPgjPY/GO4ZMgPdYdp5JKSfreaxYuiLxTeDp4puFh9fP23Bzc62FleY5N14rrOPKFwR+NKcP0ZnDKesfQUGVQgHNDWd+yn8MPE4yKAFnC5UhP6/1eV6IVnPI3KCE7+1uvsrcyVo72I9ZjECteGSwb7zUBuIknMGGJLamSDccEEzp3d9zoNmEWwYEsAQ6sfJVbzrvs9dqrDzmsgVd7rsFQsAaIXZPlOjRlQJBcoDI69G4leYK9upuWONmbxZPwESZDMmSech7WRSR+Pfg8IhH2pcuaqwx+Flyt8/fEZd1nHHn/r7IbrV7vPwpWv6bwfQE4+LOlUxGkicqW/zIbwPWua1Y1pF8kRl1B24DA9A2PuASSdsPDi8qf8524t2r4XrzPEfPSuA4z8fLDKNUZ6WPPatW6xFtOpQrgjniprbGZ5Cdzlihkh1KGZUQFWqGWG9vSMwb1XceNsZWsR1lhRieIwEpGXGARM7U6MnIf+7MlzH137TXgbWLPIOwNuFNQ1W5TQen1Ntb084V6b8dzDtE07gYYf8X3PH/73It0UuW5x0UXD6aSiIv+qp+H4rdL0sTo4SHIb8muoxzrwI7lCZtReafd6NvK5+I9wtZd+IdKqB6WabzhHQoHFJnu4BF4Z7"
`endif
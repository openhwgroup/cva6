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


`timescale 1 ps / 1 ps

module altera_emif_ecc_core #
( 
   parameter USER_CLK_RATIO                             = 1,
   parameter C2P_P2C_CLK_RATIO                          = 1,
   parameter PHY_HMC_CLK_RATIO                          = 1,
   parameter PHY_PING_PONG_EN                           = 0,
   parameter DIAG_USE_ABSTRACT_PHY                      = 0,
   parameter DIAG_SIM_MEMORY_PRELOAD                    = 0,
   parameter DIAG_SIM_MEMORY_PRELOAD_PRI_ECC_FILE       = "",
   parameter DIAG_SIM_MEMORY_PRELOAD_PRI_MEM_FILE       = "",
   parameter DIAG_SIM_MEMORY_PRELOAD_PRI_ABPHY_FILE     = "",
   parameter DIAG_SIM_MEMORY_PRELOAD_SEC_ECC_FILE       = "",
   parameter DIAG_SIM_MEMORY_PRELOAD_SEC_MEM_FILE       = "",
   parameter DIAG_SIM_MEMORY_PRELOAD_SEC_ABPHY_FILE     = "",
   parameter REGISTER_RDATA_PATH_NUM                    = 2,
   parameter REGISTER_UFI_RDATA_PATH_NUM                = 2,
   parameter REGISTER_WDATA_PATH_NUM                    = 2,
   parameter REGISTER_ST_WDATA_RDY_LAT_PATH             = 0,
   parameter REGISTER_ST_RDATA_RDY_LAT_PATH             = 0,
   parameter REGISTER_ST_CMD_RDY_LAT_PATH               = 0,
   parameter REGISTER_CORE_CMD_PIPELINE_WDATA           = 1,
   parameter USE_AVL_BYTEEN                             = 1,
   parameter ENABLE_ECC                                 = 1,
   parameter ENABLE_ECC_AUTO_CORRECTION                 = 1,
   parameter MEM_DQ_WIDTH                               = 1,
   parameter CTRL_MMR_EN                                = 0,
   parameter ECC_MMR_READ_LATENCY                       = 2,

   parameter PORT_CTRL_ECC_WRITE_INFO_WIDTH             = 1,
   parameter PORT_CTRL_ECC_RDATA_ID_WIDTH               = 1,
   parameter PORT_CTRL_ECC_READ_INFO_WIDTH              = 1,
   parameter PORT_CTRL_ECC_CMD_INFO_WIDTH               = 1,
   parameter PORT_CTRL_ECC_WB_POINTER_WIDTH             = 1,
   parameter PORT_CTRL_AST_CMD_DATA_WIDTH               = 1,
   parameter PORT_CTRL_AST_WR_DATA_WIDTH                = 1,
   parameter PORT_CTRL_AST_RD_DATA_WIDTH                = 1,
   parameter PORT_CTRL_AMM_ADDRESS_WIDTH                = 1,
   parameter PORT_CTRL_AMM_RDATA_WIDTH                  = 1,
   parameter PORT_CTRL_AMM_WDATA_WIDTH                  = 1,
   parameter PORT_CTRL_AMM_BCOUNT_WIDTH                 = 1,
   parameter PORT_CTRL_AMM_BYTEEN_WIDTH                 = 1,
   parameter PORT_CTRL_MMR_MASTER_ADDRESS_WIDTH         = 1,
   parameter PORT_CTRL_MMR_MASTER_RDATA_WIDTH           = 1,
   parameter PORT_CTRL_MMR_MASTER_WDATA_WIDTH           = 1,
   parameter PORT_CTRL_MMR_MASTER_BCOUNT_WIDTH          = 1,
   parameter PORT_CTRL_MMR_SLAVE_ADDRESS_WIDTH          = 1,
   parameter PORT_CTRL_MMR_SLAVE_RDATA_WIDTH            = 1,
   parameter PORT_CTRL_MMR_SLAVE_WDATA_WIDTH            = 1,
   parameter PORT_CTRL_MMR_SLAVE_BCOUNT_WIDTH           = 1,

   parameter PORT_CTRL_ECC_STS_INTR_WIDTH               = 1,
   parameter PORT_CTRL_ECC_STS_SBE_ERROR_WIDTH          = 1,
   parameter PORT_CTRL_ECC_STS_DBE_ERROR_WIDTH          = 1,
   parameter PORT_CTRL_ECC_STS_CORR_DROPPED_WIDTH       = 1,
   parameter PORT_CTRL_ECC_STS_SBE_COUNT_WIDTH          = 4,
   parameter PORT_CTRL_ECC_STS_DBE_COUNT_WIDTH          = 4,
   parameter PORT_CTRL_ECC_STS_CORR_DROPPED_COUNT_WIDTH = 4,
   parameter PORT_CTRL_ECC_STS_ERR_ADDR_WIDTH           = 35,
   parameter PORT_CTRL_ECC_STS_CORR_DROPPED_ADDR_WIDTH  = 35
)
(
   emif_usr_reset_n,
   emif_usr_clk,
   emif_usr_reset_n_in,
   emif_usr_clk_in,
   
   emif_usr_reset_n_sec,
   emif_usr_clk_sec,
   emif_usr_reset_n_sec_in,
   emif_usr_clk_sec_in,
     
   amm_ready_0,
   amm_read_0,
   amm_write_0,
   amm_address_0,
   amm_readdata_0,
   amm_writedata_0,
   amm_burstcount_0,
   amm_byteenable_0,
   amm_readdatavalid_0,
   amm_beginbursttransfer_0,
   
   amm_ready_1,
   amm_read_1,
   amm_write_1,
   amm_address_1,
   amm_readdata_1,
   amm_writedata_1,
   amm_burstcount_1,
   amm_byteenable_1,
   amm_readdatavalid_1,
   amm_beginbursttransfer_1,
    
   mmr_slave_waitrequest_0,
   mmr_slave_address_0,
   mmr_slave_write_0,
   mmr_slave_read_0,
   mmr_slave_burstcount_0,
   mmr_slave_beginbursttransfer_0,
   mmr_slave_writedata_0,
   mmr_slave_readdata_0,
   mmr_slave_readdatavalid_0,
   
   mmr_slave_waitrequest_1,
   mmr_slave_address_1,
   mmr_slave_write_1,
   mmr_slave_read_1,
   mmr_slave_burstcount_1,
   mmr_slave_beginbursttransfer_1,
   mmr_slave_writedata_1,
   mmr_slave_readdata_1,
   mmr_slave_readdatavalid_1,
        
   mmr_master_waitrequest_0,
   mmr_master_address_0,
   mmr_master_write_0,
   mmr_master_read_0,
   mmr_master_burstcount_0,
   mmr_master_beginbursttransfer_0,
   mmr_master_writedata_0,
   mmr_master_readdata_0,
   mmr_master_readdatavalid_0,
   
   mmr_master_waitrequest_1,
   mmr_master_address_1,
   mmr_master_write_1,
   mmr_master_read_1,
   mmr_master_burstcount_1,
   mmr_master_beginbursttransfer_1,
   mmr_master_writedata_1,
   mmr_master_readdata_1,
   mmr_master_readdatavalid_1,

   ctrl_user_priority_hi_0,
   ctrl_auto_precharge_req_0,
   
   ctrl_user_priority_hi_1,
   ctrl_auto_precharge_req_1,

   ast_cmd_ready_0,
   ast_cmd_valid_0,
   ast_cmd_data_0,
   ast_wr_ready_0,
   ast_wr_valid_0,
   ast_wr_data_0,
   ast_rd_ready_0,
   ast_rd_valid_0,
   ast_rd_data_0,
   
   ast_cmd_ready_1,
   ast_cmd_valid_1,
   ast_cmd_data_1,
   ast_wr_ready_1,
   ast_wr_valid_1,
   ast_wr_data_1,
   ast_rd_ready_1,
   ast_rd_valid_1,
   ast_rd_data_1,

   ctrl_ecc_sts_intr,
   ctrl_ecc_sts_sbe_error,
   ctrl_ecc_sts_dbe_error,
   ctrl_ecc_sts_corr_dropped,
   ctrl_ecc_sts_sbe_count,
   ctrl_ecc_sts_dbe_count,
   ctrl_ecc_sts_corr_dropped_count,
   ctrl_ecc_sts_err_addr,
   ctrl_ecc_sts_corr_dropped_addr,        

   ctrl_ecc_cmd_info_0,
   ctrl_ecc_rdata_id_0,
   ctrl_ecc_write_info_0,
   ctrl_ecc_read_info_0,
   ctrl_ecc_wr_pointer_info_0,
   ctrl_ecc_idle_0,
   ctrl_ecc_user_interrupt_0,
   ctrl_ecc_readdataerror_0,
   
   ctrl_ecc_cmd_info_1,
   ctrl_ecc_rdata_id_1,
   ctrl_ecc_write_info_1,
   ctrl_ecc_read_info_1,
   ctrl_ecc_wr_pointer_info_1,
   ctrl_ecc_idle_1,
   ctrl_ecc_user_interrupt_1,
   ctrl_ecc_readdataerror_1
);

// Override simulation-specific parameters for synthesis
// synthesis read_comments_as_HDL on
// `define DISABLE_SIM_PARAMS_FOR_SYNTH TRUE
// synthesis read_comments_as_HDL off
`ifdef DISABLE_SIM_PARAMS_FOR_SYNTH
   localparam DIAG_USE_ABSTRACT_PHY_AFT_SYNTH_OVRD    = 0;
   localparam DIAG_SIM_MEMORY_PRELOAD_AFT_SYNTH_OVRD  = 0;
`else
   localparam DIAG_USE_ABSTRACT_PHY_AFT_SYNTH_OVRD    = DIAG_USE_ABSTRACT_PHY;
   localparam DIAG_SIM_MEMORY_PRELOAD_AFT_SYNTH_OVRD  = DIAG_SIM_MEMORY_PRELOAD;
`endif

localparam PORT_CTRL_ECC_STS_MR_DATA              = PORT_CTRL_AST_RD_DATA_WIDTH;
localparam PORT_CTRL_ECC_STS_MR_DATA_VALID        = 1;

localparam CFG_LOCAL_CMD_WIDTH                    = 2;
localparam CFG_LOCAL_ADDR_WIDTH                   = PORT_CTRL_AMM_ADDRESS_WIDTH;
localparam CFG_LOCAL_SIZE_WIDTH                   = PORT_CTRL_AMM_BCOUNT_WIDTH;
localparam CFG_LOCAL_ID_WIDTH                     = 13;
localparam CFG_LOCAL_PRI_WIDTH                    = 1;
localparam CFG_LOCAL_AP_WIDTH                     = 1;
localparam CFG_LOCAL_MC_WIDTH                     = 1;
localparam CFG_ECC_CODE_WIDTH                     = 8;
localparam CFG_LOCAL_CMD_DATA_WIDTH               = PORT_CTRL_AST_CMD_DATA_WIDTH;
localparam CFG_LOCAL_CMD_INFO_WIDTH               = PORT_CTRL_ECC_CMD_INFO_WIDTH;
localparam CFG_LOCAL_DATA_WIDTH                   = PORT_CTRL_AMM_WDATA_WIDTH;
localparam CFG_LOCAL_BE_WIDTH                     = PORT_CTRL_AMM_WDATA_WIDTH / 8;
localparam CFG_LOCAL_DATA_INFO_WIDTH              = PORT_CTRL_ECC_READ_INFO_WIDTH;
localparam CFG_LOCAL_DATA_PTR_WIDTH               = PORT_CTRL_ECC_WB_POINTER_WIDTH;
localparam CFG_MEM_IF_DATA_WIDTH                  = PORT_CTRL_AMM_WDATA_WIDTH / USER_CLK_RATIO / 2;
localparam CFG_ECC_DATA_WIDTH                     = PORT_CTRL_AST_RD_DATA_WIDTH;
localparam CFG_ECC_BE_WIDTH                       = PORT_CTRL_AST_RD_DATA_WIDTH / 8;
localparam CFG_ECC_MULTIPLE_INSTANCE              = (CFG_MEM_IF_DATA_WIDTH <= 72) ? (USER_CLK_RATIO == 4) ? 8 : 4 : (USER_CLK_RATIO == 4) ? 16 : 8;

localparam CFG_ADDR_ENCODE_ENABLED                = 0;
localparam CFG_REGISTER_CMD_PATH                  = 1;
localparam CFG_REGISTER_RDATA_PATH                = 1;
localparam CFG_REGISTER_WDATA_PATH                = 1;
localparam CFG_MMR_WRPATH_PIPELINE_EN             = 1;
localparam CFG_WRBUFFER_ADDR_WIDTH                = 5;
localparam CFG_PORT_WIDTH_DRAM_DATA_WIDTH         = 8;
localparam CFG_PORT_WIDTH_LOCAL_DATA_WIDTH        = 8;
localparam CFG_PORT_WIDTH_ADDR_WIDTH              = 6;
localparam CFG_PORT_WIDTH_DATA_RATE               = 4;
localparam CFG_PORT_WIDTH_ECC_IN_PROTOCOL         = 1;
localparam CFG_PORT_WIDTH_WRPATH_PIPELINE_EN      = 1;
localparam CFG_PORT_WIDTH_ENABLE_ECC              = 1;
localparam CFG_PORT_WIDTH_ENABLE_DM               = 1;
localparam CFG_PORT_WIDTH_ENABLE_RMW              = 1;
localparam CFG_PORT_WIDTH_ENABLE_AUTO_CORR        = 1;
localparam CFG_PORT_WIDTH_ECC_CODE_OVERWRITE      = 1;
localparam CFG_PORT_WIDTH_GEN_SBE                 = 1;
localparam CFG_PORT_WIDTH_GEN_DBE                 = 1;
localparam CFG_PORT_WIDTH_ENABLE_INTR             = 1;
localparam CFG_PORT_WIDTH_MASK_SBE_INTR           = 1;
localparam CFG_PORT_WIDTH_MASK_DBE_INTR           = 1;
localparam CFG_PORT_WIDTH_MASK_CORR_DROPPED_INTR  = 1;
localparam CFG_PORT_WIDTH_MASK_HMI_INTR           = 1;
localparam CFG_PORT_WIDTH_CLR_INTR                = 1;
localparam CFG_PORT_WIDTH_CLR_MR_RDATA            = 1;
localparam CFG_MMR_DATA_WIDTH                     = 32;

localparam STS_PORT_WIDTH_ECC_INTR                = 1;
localparam STS_PORT_WIDTH_SBE_ERROR               = 1;
localparam STS_PORT_WIDTH_DBE_ERROR               = 1;
localparam STS_PORT_WIDTH_CORR_DROPPED            = 1;
localparam STS_PORT_WIDTH_SBE_COUNT               = 4;
localparam STS_PORT_WIDTH_DBE_COUNT               = 4;
localparam STS_PORT_WIDTH_CORR_DROPPED_COUNT      = 4;
localparam STS_PORT_WIDTH_ERR_ADDR                = 35;
localparam STS_PORT_WIDTH_CORR_DROPPED_ADDR       = 35;
localparam STS_PORT_WIDTH_MR_DATA                 = PORT_CTRL_AST_RD_DATA_WIDTH;
localparam STS_PORT_WIDTH_MR_DATA_VALID           = 1;


input                                                  emif_usr_reset_n_in;
input                                                  emif_usr_clk_in;
output                                                 emif_usr_reset_n;
output                                                 emif_usr_clk;

input                                                  emif_usr_reset_n_sec_in;
input                                                  emif_usr_clk_sec_in;
output                                                 emif_usr_reset_n_sec;
output                                                 emif_usr_clk_sec;

output wire [PORT_CTRL_ECC_STS_INTR_WIDTH               - 1 : 0] ctrl_ecc_sts_intr;
output wire [PORT_CTRL_ECC_STS_SBE_ERROR_WIDTH          - 1 : 0] ctrl_ecc_sts_sbe_error;
output wire [PORT_CTRL_ECC_STS_DBE_ERROR_WIDTH          - 1 : 0] ctrl_ecc_sts_dbe_error;
output wire [PORT_CTRL_ECC_STS_CORR_DROPPED_WIDTH       - 1 : 0] ctrl_ecc_sts_corr_dropped;
output wire [PORT_CTRL_ECC_STS_SBE_COUNT_WIDTH          - 1 : 0] ctrl_ecc_sts_sbe_count;
output wire [PORT_CTRL_ECC_STS_DBE_COUNT_WIDTH          - 1 : 0] ctrl_ecc_sts_dbe_count;
output wire [PORT_CTRL_ECC_STS_CORR_DROPPED_COUNT_WIDTH - 1 : 0] ctrl_ecc_sts_corr_dropped_count;
output wire [PORT_CTRL_ECC_STS_ERR_ADDR_WIDTH           - 1 : 0] ctrl_ecc_sts_err_addr;
output wire [PORT_CTRL_ECC_STS_CORR_DROPPED_ADDR_WIDTH  - 1 : 0] ctrl_ecc_sts_corr_dropped_addr;

wire  [STS_PORT_WIDTH_ECC_INTR                          - 1 : 0] sts_ecc_intr_0;
wire  [STS_PORT_WIDTH_SBE_ERROR                         - 1 : 0] sts_sbe_error_0;
wire  [STS_PORT_WIDTH_DBE_ERROR                         - 1 : 0] sts_dbe_error_0;
wire  [STS_PORT_WIDTH_CORR_DROPPED                      - 1 : 0] sts_corr_dropped_0;
wire  [STS_PORT_WIDTH_SBE_COUNT                         - 1 : 0] sts_sbe_count_0;
wire  [STS_PORT_WIDTH_DBE_COUNT                         - 1 : 0] sts_dbe_count_0;
wire  [STS_PORT_WIDTH_CORR_DROPPED_COUNT                - 1 : 0] sts_corr_dropped_count_0;
wire  [STS_PORT_WIDTH_ERR_ADDR                          - 1 : 0] sts_err_addr_0;
wire  [STS_PORT_WIDTH_CORR_DROPPED_ADDR                 - 1 : 0] sts_corr_dropped_addr_0;

wire  [STS_PORT_WIDTH_ECC_INTR                          - 1 : 0] sts_ecc_intr_1;
wire  [STS_PORT_WIDTH_SBE_ERROR                         - 1 : 0] sts_sbe_error_1;
wire  [STS_PORT_WIDTH_DBE_ERROR                         - 1 : 0] sts_dbe_error_1;
wire  [STS_PORT_WIDTH_CORR_DROPPED                      - 1 : 0] sts_corr_dropped_1;
wire  [STS_PORT_WIDTH_SBE_COUNT                         - 1 : 0] sts_sbe_count_1;
wire  [STS_PORT_WIDTH_DBE_COUNT                         - 1 : 0] sts_dbe_count_1;
wire  [STS_PORT_WIDTH_CORR_DROPPED_COUNT                - 1 : 0] sts_corr_dropped_count_1;
wire  [STS_PORT_WIDTH_ERR_ADDR                          - 1 : 0] sts_err_addr_1;
wire  [STS_PORT_WIDTH_CORR_DROPPED_ADDR                 - 1 : 0] sts_corr_dropped_addr_1;

output                                                 amm_ready_0;
input                                                  amm_read_0;
input                                                  amm_write_0;
input  [PORT_CTRL_AMM_ADDRESS_WIDTH     - 1 : 0]       amm_address_0;
output [PORT_CTRL_AMM_RDATA_WIDTH       - 1 : 0]       amm_readdata_0;
input  [PORT_CTRL_AMM_WDATA_WIDTH       - 1 : 0]       amm_writedata_0;
input  [PORT_CTRL_AMM_BCOUNT_WIDTH      - 1 : 0]       amm_burstcount_0;
input  [PORT_CTRL_AMM_BYTEEN_WIDTH      - 1 : 0]       amm_byteenable_0;
input                                                  amm_beginbursttransfer_0;
output                                                 amm_readdatavalid_0;

output                                                 amm_ready_1;
input                                                  amm_read_1;
input                                                  amm_write_1;
input  [PORT_CTRL_AMM_ADDRESS_WIDTH     - 1 : 0]       amm_address_1;
output [PORT_CTRL_AMM_RDATA_WIDTH       - 1 : 0]       amm_readdata_1;
input  [PORT_CTRL_AMM_WDATA_WIDTH       - 1 : 0]       amm_writedata_1;
input  [PORT_CTRL_AMM_BCOUNT_WIDTH      - 1 : 0]       amm_burstcount_1;
input  [PORT_CTRL_AMM_BYTEEN_WIDTH      - 1 : 0]       amm_byteenable_1;
input                                                  amm_beginbursttransfer_1;
output                                                 amm_readdatavalid_1;

output                                                 mmr_slave_waitrequest_0;
input  [PORT_CTRL_MMR_SLAVE_ADDRESS_WIDTH - 1 : 0]     mmr_slave_address_0;
input                                                  mmr_slave_write_0;
input                                                  mmr_slave_read_0;
input  [PORT_CTRL_MMR_SLAVE_BCOUNT_WIDTH - 1 : 0]      mmr_slave_burstcount_0;
input                                                  mmr_slave_beginbursttransfer_0;
input  [PORT_CTRL_MMR_SLAVE_WDATA_WIDTH  - 1 : 0]      mmr_slave_writedata_0;
output [PORT_CTRL_MMR_SLAVE_RDATA_WIDTH  - 1 : 0]      mmr_slave_readdata_0;
output                                                 mmr_slave_readdatavalid_0;

output                                                 mmr_slave_waitrequest_1;
input  [PORT_CTRL_MMR_SLAVE_ADDRESS_WIDTH - 1 : 0]     mmr_slave_address_1;
input                                                  mmr_slave_write_1;
input                                                  mmr_slave_read_1;
input  [PORT_CTRL_MMR_SLAVE_BCOUNT_WIDTH - 1 : 0]      mmr_slave_burstcount_1;
input                                                  mmr_slave_beginbursttransfer_1;
input  [PORT_CTRL_MMR_SLAVE_WDATA_WIDTH  - 1 : 0]      mmr_slave_writedata_1;
output [PORT_CTRL_MMR_SLAVE_RDATA_WIDTH  - 1 : 0]      mmr_slave_readdata_1;
output                                                 mmr_slave_readdatavalid_1;

input                                                  mmr_master_waitrequest_0;
output  [PORT_CTRL_MMR_MASTER_ADDRESS_WIDTH - 1 : 0]   mmr_master_address_0;
output                                                 mmr_master_write_0;
output                                                 mmr_master_read_0;
output  [PORT_CTRL_MMR_MASTER_BCOUNT_WIDTH  - 1 : 0]   mmr_master_burstcount_0;
output                                                 mmr_master_beginbursttransfer_0;
output  [PORT_CTRL_MMR_MASTER_WDATA_WIDTH   - 1 : 0]   mmr_master_writedata_0;
input   [PORT_CTRL_MMR_MASTER_RDATA_WIDTH   - 1 : 0]   mmr_master_readdata_0;
input                                                  mmr_master_readdatavalid_0;

input                                                  mmr_master_waitrequest_1;
output  [PORT_CTRL_MMR_MASTER_ADDRESS_WIDTH - 1 : 0]   mmr_master_address_1;
output                                                 mmr_master_write_1;
output                                                 mmr_master_read_1;
output  [PORT_CTRL_MMR_MASTER_BCOUNT_WIDTH  - 1 : 0]   mmr_master_burstcount_1;
output                                                 mmr_master_beginbursttransfer_1;
output  [PORT_CTRL_MMR_MASTER_WDATA_WIDTH   - 1 : 0]   mmr_master_writedata_1;
input   [PORT_CTRL_MMR_MASTER_RDATA_WIDTH   - 1 : 0]   mmr_master_readdata_1;
input                                                  mmr_master_readdatavalid_1;

input                                                  ctrl_user_priority_hi_0;
input                                                  ctrl_auto_precharge_req_0;

input                                                  ctrl_user_priority_hi_1;
input                                                  ctrl_auto_precharge_req_1;

input                                                  ast_cmd_ready_0;
output                                                 ast_cmd_valid_0;
output [PORT_CTRL_AST_CMD_DATA_WIDTH    - 1 : 0]       ast_cmd_data_0;
input                                                  ast_wr_ready_0;
output                                                 ast_wr_valid_0;
output [PORT_CTRL_AST_WR_DATA_WIDTH     - 1 : 0]       ast_wr_data_0;
output                                                 ast_rd_ready_0;
input                                                  ast_rd_valid_0;
input  [PORT_CTRL_AST_RD_DATA_WIDTH     - 1 : 0]       ast_rd_data_0;

input                                                  ast_cmd_ready_1;
output                                                 ast_cmd_valid_1;
output [PORT_CTRL_AST_CMD_DATA_WIDTH    - 1 : 0]       ast_cmd_data_1;
input                                                  ast_wr_ready_1;
output                                                 ast_wr_valid_1;
output [PORT_CTRL_AST_WR_DATA_WIDTH     - 1 : 0]       ast_wr_data_1;
output                                                 ast_rd_ready_1;
input                                                  ast_rd_valid_1;
input  [PORT_CTRL_AST_RD_DATA_WIDTH     - 1 : 0]       ast_rd_data_1;


input  [PORT_CTRL_ECC_CMD_INFO_WIDTH    - 1 : 0]       ctrl_ecc_cmd_info_0;
input  [PORT_CTRL_ECC_RDATA_ID_WIDTH    - 1 : 0]       ctrl_ecc_rdata_id_0;
output [PORT_CTRL_ECC_WRITE_INFO_WIDTH  - 1 : 0]       ctrl_ecc_write_info_0;
input  [PORT_CTRL_ECC_READ_INFO_WIDTH   - 1 : 0]       ctrl_ecc_read_info_0;
input  [PORT_CTRL_ECC_WB_POINTER_WIDTH  - 1 : 0]       ctrl_ecc_wr_pointer_info_0;
input                                                  ctrl_ecc_idle_0;
output                                                 ctrl_ecc_user_interrupt_0;
output                                                 ctrl_ecc_readdataerror_0;

input  [PORT_CTRL_ECC_CMD_INFO_WIDTH    - 1 : 0]       ctrl_ecc_cmd_info_1;
input  [PORT_CTRL_ECC_RDATA_ID_WIDTH    - 1 : 0]       ctrl_ecc_rdata_id_1;
output [PORT_CTRL_ECC_WRITE_INFO_WIDTH  - 1 : 0]       ctrl_ecc_write_info_1;
input  [PORT_CTRL_ECC_READ_INFO_WIDTH   - 1 : 0]       ctrl_ecc_read_info_1;
input  [PORT_CTRL_ECC_WB_POINTER_WIDTH  - 1 : 0]       ctrl_ecc_wr_pointer_info_1;
input                                                  ctrl_ecc_idle_1;
output                                                 ctrl_ecc_user_interrupt_1;
output                                                 ctrl_ecc_readdataerror_1;

assign emif_usr_reset_n = emif_usr_reset_n_in;
assign emif_usr_clk = emif_usr_clk_in;

assign emif_usr_reset_n_sec = emif_usr_reset_n_sec_in;
assign emif_usr_clk_sec = emif_usr_clk_sec_in;

generate

   wire [CFG_ECC_BE_WIDTH - 1 : 0]  ctrl_ecc_wr_byte_enable_0;
   wire [CFG_ECC_DATA_WIDTH -1 : 0] ast_wr_data_without_byteen_0;
   wire [34:0] amm_address_padded_0;
   wire [7:0]  amm_burstcount_padded_0;
   wire slave_mmr_ready_0;

   if (PORT_CTRL_AST_WR_DATA_WIDTH == PORT_CTRL_AST_RD_DATA_WIDTH)
      assign ast_wr_data_0 = ast_wr_data_without_byteen_0;
   else
      assign ast_wr_data_0 = {ctrl_ecc_wr_byte_enable_0, ast_wr_data_without_byteen_0};

   if (PORT_CTRL_AMM_ADDRESS_WIDTH >= 35) begin
      assign amm_address_padded_0 = amm_address_0;
   end else begin
      assign amm_address_padded_0 = {{(35 - PORT_CTRL_AMM_ADDRESS_WIDTH){1'b0}}, amm_address_0};
   end
   
   if (PORT_CTRL_AMM_BCOUNT_WIDTH >= 8) begin
      assign amm_burstcount_padded_0 = amm_burstcount_0;
   end else begin
      assign amm_burstcount_padded_0 = {{(8 - PORT_CTRL_AMM_BCOUNT_WIDTH){1'b0}}, amm_burstcount_0};
   end      
   
   wire [CFG_LOCAL_CMD_DATA_WIDTH - 1 : 0] slave_cmd_data_wire_0;

   assign slave_cmd_data_wire_0 = {{13{1'b0}},                                                            
                                   1'b0,                                                                  
                                   ctrl_auto_precharge_req_0,                                             
                                   ctrl_user_priority_hi_0,                                               
                                   amm_burstcount_padded_0,                                               
                                   amm_address_padded_0,                                                  
                                   amm_write_0,                                                           
                                   amm_read_0};                                                           

   fmiohmc_ecc_wrapper #(
      .CFG_LOCAL_CMD_WIDTH                    (CFG_LOCAL_CMD_WIDTH),
      .CFG_LOCAL_ADDR_WIDTH                   (CFG_LOCAL_ADDR_WIDTH),
      .CFG_LOCAL_SIZE_WIDTH                   (CFG_LOCAL_SIZE_WIDTH),
      .CFG_LOCAL_ID_WIDTH                     (CFG_LOCAL_ID_WIDTH),
      .CFG_LOCAL_PRI_WIDTH                    (CFG_LOCAL_PRI_WIDTH),
      .CFG_LOCAL_AP_WIDTH                     (CFG_LOCAL_AP_WIDTH),
      .CFG_LOCAL_MC_WIDTH                     (CFG_LOCAL_MC_WIDTH),
      .CFG_CMD_DATA_WIDTH                     (CFG_LOCAL_CMD_DATA_WIDTH),
      .CFG_CMD_INFO_WIDTH                     (CFG_LOCAL_CMD_INFO_WIDTH),
      .CFG_LOCAL_DATA_WIDTH                   (CFG_LOCAL_DATA_WIDTH),
      .CFG_LOCAL_BE_WIDTH                     (CFG_LOCAL_BE_WIDTH),
      .CFG_LOCAL_DATA_INFO_WIDTH              (CFG_LOCAL_DATA_INFO_WIDTH),
      .CFG_LOCAL_DATA_PTR_WIDTH               (CFG_LOCAL_DATA_PTR_WIDTH),
      .CFG_ECC_DATA_WIDTH                     (CFG_ECC_DATA_WIDTH),
      .CFG_ECC_BE_WIDTH                       (CFG_ECC_BE_WIDTH),
      .CFG_ECC_CODE_WIDTH                     (CFG_ECC_CODE_WIDTH),
      .CFG_ECC_MULTIPLE_INSTANCE              (CFG_ECC_MULTIPLE_INSTANCE),
      .CFG_REGISTER_CMD_PATH                  (CFG_REGISTER_CMD_PATH),
      .CFG_REGISTER_RDATA_PATH                (CFG_REGISTER_RDATA_PATH),
      .CFG_REGISTER_RDATA_PATH_NUM            (REGISTER_RDATA_PATH_NUM),
      .CFG_REGISTER_UFI_RDATA_PATH_NUM        (REGISTER_UFI_RDATA_PATH_NUM),
      .CFG_REGISTER_WDATA_PATH                (CFG_REGISTER_WDATA_PATH),
      .CFG_REGISTER_WDATA_PATH_NUM            (REGISTER_WDATA_PATH_NUM),
      .CFG_REGISTER_ST_WDATA_RDY_LAT_PATH     (REGISTER_ST_WDATA_RDY_LAT_PATH),
      .CFG_REGISTER_ST_RDATA_RDY_LAT_PATH     (REGISTER_ST_RDATA_RDY_LAT_PATH),
      .CFG_REGISTER_ST_CMD_RDY_LAT_PATH       (REGISTER_ST_CMD_RDY_LAT_PATH),
      .CORE_CMD_PIPELINE_WDATA                (REGISTER_CORE_CMD_PIPELINE_WDATA),
      .CFG_MMR_DATA_WIDTH                     (CFG_MMR_DATA_WIDTH),
      .MMR_DRAM_DATA_WIDTH                    (CFG_LOCAL_DATA_WIDTH / CFG_ECC_MULTIPLE_INSTANCE + CFG_ECC_CODE_WIDTH),
      .MMR_LOCAL_DATA_WIDTH                   (CFG_LOCAL_DATA_WIDTH / CFG_ECC_MULTIPLE_INSTANCE),
      .MMR_ADDR_WIDTH                         (CFG_LOCAL_ADDR_WIDTH),
      .MMR_DATA_RATE                          ((USER_CLK_RATIO == 4) ? 4'd8 : 4'd4),
      .MMR_ECC_IN_PROTOCOL                    (1),
      .MMR_WRPATH_PIPELINE_EN                 (CFG_MMR_WRPATH_PIPELINE_EN),
      .MMR_ENABLE_ECC                         (ENABLE_ECC),
      .MMR_ENABLE_DM                          ((USE_AVL_BYTEEN) ? 1 : 0),
      .MMR_ENABLE_RMW                         (ENABLE_ECC),
      .MMR_ENABLE_AUTO_CORR                   (ENABLE_ECC_AUTO_CORRECTION),
      .MMR_ECC_CODE_OVERWRITE                 (0),
      .MMR_GEN_SBE                            (0),
      .MMR_GEN_DBE                            (0),
      .MMR_ENABLE_INTR                        (1),
      .MMR_MASK_SBE_INTR                      (0),
      .MMR_MASK_DBE_INTR                      (0),
      .MMR_MASK_CORR_DROPPED_INTR             (0),
      .MMR_MASK_HMI_INTR                      (0),
      .MMR_CLR_INTR                           (0),
      .MMR_CLR_MR_RDATA                       (0),
      .ECC_MMR_READ_LATENCY                   (ECC_MMR_READ_LATENCY),
      .CFG_WRBUFFER_ADDR_WIDTH                (CFG_WRBUFFER_ADDR_WIDTH),
      .CFG_PORT_WIDTH_DRAM_DATA_WIDTH         (CFG_PORT_WIDTH_DRAM_DATA_WIDTH),
      .CFG_PORT_WIDTH_LOCAL_DATA_WIDTH        (CFG_PORT_WIDTH_LOCAL_DATA_WIDTH), 
      .CFG_PORT_WIDTH_ADDR_WIDTH              (CFG_PORT_WIDTH_ADDR_WIDTH),
      .CFG_PORT_WIDTH_DATA_RATE               (CFG_PORT_WIDTH_DATA_RATE),
      .CFG_PORT_WIDTH_ECC_IN_PROTOCOL         (CFG_PORT_WIDTH_ECC_IN_PROTOCOL),
      .CFG_PORT_WIDTH_WRPATH_PIPELINE_EN      (CFG_PORT_WIDTH_WRPATH_PIPELINE_EN),
      .CFG_PORT_WIDTH_ENABLE_ECC              (CFG_PORT_WIDTH_ENABLE_ECC),
      .CFG_PORT_WIDTH_ENABLE_DM               (CFG_PORT_WIDTH_ENABLE_DM),
      .CFG_PORT_WIDTH_ENABLE_RMW              (CFG_PORT_WIDTH_ENABLE_RMW),
      .CFG_PORT_WIDTH_ENABLE_AUTO_CORR        (CFG_PORT_WIDTH_ENABLE_AUTO_CORR),
      .CFG_PORT_WIDTH_ECC_CODE_OVERWRITE      (CFG_PORT_WIDTH_ECC_CODE_OVERWRITE),
      .CFG_PORT_WIDTH_GEN_SBE                 (CFG_PORT_WIDTH_GEN_SBE),
      .CFG_PORT_WIDTH_GEN_DBE                 (CFG_PORT_WIDTH_GEN_DBE),
      .CFG_PORT_WIDTH_ENABLE_INTR             (CFG_PORT_WIDTH_ENABLE_INTR),
      .CFG_PORT_WIDTH_MASK_SBE_INTR           (CFG_PORT_WIDTH_MASK_SBE_INTR),
      .CFG_PORT_WIDTH_MASK_DBE_INTR           (CFG_PORT_WIDTH_MASK_DBE_INTR),
      .CFG_PORT_WIDTH_MASK_CORR_DROPPED_INTR  (CFG_PORT_WIDTH_MASK_CORR_DROPPED_INTR),
      .CFG_PORT_WIDTH_MASK_HMI_INTR           (CFG_PORT_WIDTH_MASK_HMI_INTR),
      .CFG_PORT_WIDTH_CLR_INTR                (CFG_PORT_WIDTH_CLR_INTR),
      .CFG_PORT_WIDTH_CLR_MR_RDATA            (CFG_PORT_WIDTH_CLR_MR_RDATA),
      .STS_PORT_WIDTH_ECC_INTR                (STS_PORT_WIDTH_ECC_INTR),
      .STS_PORT_WIDTH_SBE_ERROR               (STS_PORT_WIDTH_SBE_ERROR),
      .STS_PORT_WIDTH_DBE_ERROR               (STS_PORT_WIDTH_DBE_ERROR),
      .STS_PORT_WIDTH_CORR_DROPPED            (STS_PORT_WIDTH_CORR_DROPPED),
      .STS_PORT_WIDTH_SBE_COUNT               (STS_PORT_WIDTH_SBE_COUNT),
      .STS_PORT_WIDTH_DBE_COUNT               (STS_PORT_WIDTH_DBE_COUNT),
      .STS_PORT_WIDTH_CORR_DROPPED_COUNT      (STS_PORT_WIDTH_CORR_DROPPED_COUNT),
      .STS_PORT_WIDTH_ERR_ADDR                (STS_PORT_WIDTH_ERR_ADDR),
      .STS_PORT_WIDTH_CORR_DROPPED_ADDR       (STS_PORT_WIDTH_CORR_DROPPED_ADDR),
      .STS_PORT_WIDTH_MR_DATA                 (STS_PORT_WIDTH_MR_DATA),
      .STS_PORT_WIDTH_MR_DATA_VALID           (STS_PORT_WIDTH_MR_DATA_VALID)
   ) ecc (
      .ctl_clk                                (emif_usr_clk_in),
      .ctl_reset_n_pre_reg                    (emif_usr_reset_n_in),

      .slave_cmd_ready                        (amm_ready_0),
      .slave_cmd_data                         (slave_cmd_data_wire_0),
      .slave_cmd_valid                        (amm_write_0 | amm_read_0),
      .slave_wr_data_ready                    (),
      .slave_wr_data_byte_enable              ((USE_AVL_BYTEEN) ? amm_byteenable_0 : {(CFG_LOCAL_BE_WIDTH){1'b1}}),
      .slave_wr_data                          (amm_writedata_0),
      .slave_wr_data_id                       ({(CFG_LOCAL_ID_WIDTH){1'b0}}), 
      .slave_wr_data_valid                    (amm_write_0),
      .slave_rd_data_ready                    (1'b1),
      .slave_rd_data                          (amm_readdata_0),
      .slave_rd_data_id                       (),
      .slave_rd_data_valid                    (amm_readdatavalid_0),
      .slave_rd_data_error                    (ctrl_ecc_readdataerror_0),
         
      .master_cmd_ready                       (ast_cmd_ready_0),
      .master_cmd_data                        (ast_cmd_data_0),
      .master_cmd_valid                       (ast_cmd_valid_0),
      .master_cmd_data_combi                  (),
      .master_cmd_valid_combi                 (),
      .master_cmd_info                        (ctrl_ecc_cmd_info_0),
      .master_wr_data_ready                   (ast_wr_ready_0),
      .master_wr_data_byte_enable             (ctrl_ecc_wr_byte_enable_0),
      .master_wr_data                         (ast_wr_data_without_byteen_0),
      .master_wr_data_id                      (),
      .master_wr_data_info                    (ctrl_ecc_write_info_0[2:0]),
      .master_wr_data_ptr_in                  (ctrl_ecc_wr_pointer_info_0),
      .master_wr_data_ptr_out                 (ctrl_ecc_write_info_0[PORT_CTRL_ECC_WRITE_INFO_WIDTH-1:3]),
      .master_wr_data_valid                   (ast_wr_valid_0),
      .master_rd_data_ready                   (ast_rd_ready_0),
      .master_rd_data                         (ast_rd_data_0),
      .master_rd_data_id                      (ctrl_ecc_rdata_id_0),
      .master_rd_data_info                    (ctrl_ecc_read_info_0),
      .master_rd_data_valid                   (ast_rd_valid_0),
      .master_rd_data_type                    (1'b0),

      .slave_mmr_ready                        (slave_mmr_ready_0),
      .slave_mmr_address                      ((CTRL_MMR_EN) ? mmr_slave_address_0 : {(PORT_CTRL_MMR_SLAVE_ADDRESS_WIDTH){1'b0}}),
      .slave_mmr_write                        ((CTRL_MMR_EN) ? mmr_slave_write_0 : 1'b0),
      .slave_mmr_read                         ((CTRL_MMR_EN) ? mmr_slave_read_0 : 1'b0),
      .slave_mmr_burstcount                   ((CTRL_MMR_EN) ? mmr_slave_burstcount_0 : {(PORT_CTRL_MMR_SLAVE_BCOUNT_WIDTH){1'b0}}),
      .slave_mmr_begintransfer                ((CTRL_MMR_EN) ? mmr_slave_beginbursttransfer_0 : 1'b0),
      .slave_mmr_wr_data                      ((CTRL_MMR_EN) ? mmr_slave_writedata_0 : {(PORT_CTRL_MMR_SLAVE_WDATA_WIDTH){1'b0}}),
      .slave_mmr_rd_data                      (mmr_slave_readdata_0),
      .slave_mmr_rd_data_valid                (mmr_slave_readdatavalid_0),
        
      .master_mmr_ready                       ((CTRL_MMR_EN) ? ~mmr_master_waitrequest_0 : 1'b1),
      .master_mmr_address                     (mmr_master_address_0),
      .master_mmr_write                       (mmr_master_write_0),
      .master_mmr_read                        (mmr_master_read_0),
      .master_mmr_burstcount                  (mmr_master_burstcount_0),
      .master_mmr_begintransfer               (mmr_master_beginbursttransfer_0),
      .master_mmr_wr_data                     (mmr_master_writedata_0),
      .master_mmr_rd_data                     ((CTRL_MMR_EN) ? mmr_master_readdata_0 : {(PORT_CTRL_MMR_MASTER_RDATA_WIDTH){1'b0}}),
      .master_mmr_rd_data_valid               ((CTRL_MMR_EN) ? mmr_master_readdatavalid_0 : 1'b0),

      .sts_ecc_intr                           (sts_ecc_intr_0),
      .sts_sbe_error                          (sts_sbe_error_0),
      .sts_dbe_error                          (sts_dbe_error_0),
      .sts_corr_dropped                       (sts_corr_dropped_0),
      .sts_sbe_count                          (sts_sbe_count_0),
      .sts_dbe_count                          (sts_dbe_count_0),
      .sts_corr_dropped_count                 (sts_corr_dropped_count_0),
      .sts_err_addr                           (sts_err_addr_0),
      .sts_corr_dropped_addr                  (sts_corr_dropped_addr_0),

      .user_interrupt                         (ctrl_ecc_user_interrupt_0),
      .hmi_interrupt                          (1'b0) 
   );
   
   assign mmr_slave_waitrequest_0 = ~slave_mmr_ready_0;

   if (DIAG_SIM_MEMORY_PRELOAD_AFT_SYNTH_OVRD) begin : gen_preload
      altera_emif_preload_ecc_encoder #
      ( 
         .DIAG_USE_ABSTRACT_PHY                  (DIAG_USE_ABSTRACT_PHY_AFT_SYNTH_OVRD),
         .DIAG_SIM_MEMORY_PRELOAD_ECC_FILE       (DIAG_SIM_MEMORY_PRELOAD_PRI_ECC_FILE),
         .DIAG_SIM_MEMORY_PRELOAD_MEM_FILE       (DIAG_SIM_MEMORY_PRELOAD_PRI_MEM_FILE),
         .DIAG_SIM_MEMORY_PRELOAD_ABPHY_FILE     (DIAG_SIM_MEMORY_PRELOAD_PRI_ABPHY_FILE),
         .CTRL_AMM_ADDRESS_WIDTH                 (PORT_CTRL_AMM_ADDRESS_WIDTH),
         .CTRL_AMM_DATA_WIDTH                    (PORT_CTRL_AMM_WDATA_WIDTH),
         .MEM_DQ_WIDTH                           (MEM_DQ_WIDTH),
         .USE_AVL_BYTEEN                         (USE_AVL_BYTEEN),
         .CFG_ADDR_ENCODE_ENABLED                (CFG_ADDR_ENCODE_ENABLED)
      ) preload_inst (
         .emif_usr_clk                           (emif_usr_clk_in)
      );
   end

   if (PHY_PING_PONG_EN) begin : pp_ecc
   
      wire [CFG_ECC_BE_WIDTH - 1 : 0]  ctrl_ecc_wr_byte_enable_1;
      wire [CFG_ECC_DATA_WIDTH -1 : 0] ast_wr_data_without_byteen_1;
      wire [34:0] amm_address_padded_1;
      wire [7:0]  amm_burstcount_padded_1;
      wire slave_mmr_ready_1;

      if (PORT_CTRL_AST_WR_DATA_WIDTH == PORT_CTRL_AST_RD_DATA_WIDTH)
         assign ast_wr_data_1 = ast_wr_data_without_byteen_1;
      else
         assign ast_wr_data_1 = {ctrl_ecc_wr_byte_enable_1, ast_wr_data_without_byteen_1};
         
      if (PORT_CTRL_AMM_ADDRESS_WIDTH >= 35) begin
         assign amm_address_padded_1 = amm_address_1;
      end else begin
         assign amm_address_padded_1 = {{(35 - PORT_CTRL_AMM_ADDRESS_WIDTH){1'b0}}, amm_address_1};
      end
      
      if (PORT_CTRL_AMM_BCOUNT_WIDTH >= 8) begin
         assign amm_burstcount_padded_1 = amm_burstcount_1;
      end else begin
         assign amm_burstcount_padded_1 = {{(8 - PORT_CTRL_AMM_BCOUNT_WIDTH){1'b0}}, amm_burstcount_1};
      end               
   
      wire [CFG_LOCAL_CMD_DATA_WIDTH - 1 : 0] slave_cmd_data_wire_1;
                           
      assign slave_cmd_data_wire_1 = {{13{1'b0}},                                                            
                                      1'b0,                                                                  
                                      ctrl_auto_precharge_req_1,                                             
                                      ctrl_user_priority_hi_1,                                               
                                      amm_burstcount_padded_1,                                               
                                      amm_address_padded_1,                                                  
                                      amm_write_1,                                                           
                                      amm_read_1};                                                           
   
      fmiohmc_ecc_wrapper #(
         .CFG_LOCAL_CMD_WIDTH                    (CFG_LOCAL_CMD_WIDTH),
         .CFG_LOCAL_ADDR_WIDTH                   (CFG_LOCAL_ADDR_WIDTH),
         .CFG_LOCAL_SIZE_WIDTH                   (CFG_LOCAL_SIZE_WIDTH),
         .CFG_LOCAL_ID_WIDTH                     (CFG_LOCAL_ID_WIDTH),
         .CFG_LOCAL_PRI_WIDTH                    (CFG_LOCAL_PRI_WIDTH),
         .CFG_LOCAL_AP_WIDTH                     (CFG_LOCAL_AP_WIDTH),
         .CFG_LOCAL_MC_WIDTH                     (CFG_LOCAL_MC_WIDTH),
         .CFG_CMD_DATA_WIDTH                     (CFG_LOCAL_CMD_DATA_WIDTH),
         .CFG_CMD_INFO_WIDTH                     (CFG_LOCAL_CMD_INFO_WIDTH),
         .CFG_LOCAL_DATA_WIDTH                   (CFG_LOCAL_DATA_WIDTH),
         .CFG_LOCAL_BE_WIDTH                     (CFG_LOCAL_BE_WIDTH),
         .CFG_LOCAL_DATA_INFO_WIDTH              (CFG_LOCAL_DATA_INFO_WIDTH),
         .CFG_LOCAL_DATA_PTR_WIDTH               (CFG_LOCAL_DATA_PTR_WIDTH),
         .CFG_ECC_DATA_WIDTH                     (CFG_ECC_DATA_WIDTH),
         .CFG_ECC_BE_WIDTH                       (CFG_ECC_BE_WIDTH),
         .CFG_ECC_CODE_WIDTH                     (CFG_ECC_CODE_WIDTH),
         .CFG_ECC_MULTIPLE_INSTANCE              (CFG_ECC_MULTIPLE_INSTANCE),
         .CFG_REGISTER_CMD_PATH                  (CFG_REGISTER_CMD_PATH),
         .CFG_REGISTER_RDATA_PATH                (CFG_REGISTER_RDATA_PATH),
         .CFG_REGISTER_RDATA_PATH_NUM            (REGISTER_RDATA_PATH_NUM),
         .CFG_REGISTER_UFI_RDATA_PATH_NUM        (REGISTER_UFI_RDATA_PATH_NUM),
         .CFG_REGISTER_WDATA_PATH                (CFG_REGISTER_WDATA_PATH),
         .CFG_REGISTER_WDATA_PATH_NUM            (REGISTER_WDATA_PATH_NUM),
         .CFG_REGISTER_ST_WDATA_RDY_LAT_PATH     (REGISTER_ST_WDATA_RDY_LAT_PATH),
         .CFG_REGISTER_ST_RDATA_RDY_LAT_PATH     (REGISTER_ST_RDATA_RDY_LAT_PATH),
         .CFG_REGISTER_ST_CMD_RDY_LAT_PATH       (REGISTER_ST_CMD_RDY_LAT_PATH),
         .CORE_CMD_PIPELINE_WDATA                (REGISTER_CORE_CMD_PIPELINE_WDATA),
         .CFG_MMR_DATA_WIDTH                     (CFG_MMR_DATA_WIDTH),
         .MMR_DRAM_DATA_WIDTH                    (CFG_LOCAL_DATA_WIDTH / CFG_ECC_MULTIPLE_INSTANCE + CFG_ECC_CODE_WIDTH),
         .MMR_LOCAL_DATA_WIDTH                   (CFG_LOCAL_DATA_WIDTH / CFG_ECC_MULTIPLE_INSTANCE),
         .MMR_ADDR_WIDTH                         (CFG_LOCAL_ADDR_WIDTH),
         .MMR_DATA_RATE                          ((USER_CLK_RATIO == 4) ? 4'd8 : 4'd4),
         .MMR_ECC_IN_PROTOCOL                    (1),
         .MMR_WRPATH_PIPELINE_EN                 (CFG_MMR_WRPATH_PIPELINE_EN),
         .MMR_ENABLE_ECC                         (ENABLE_ECC),
         .MMR_ENABLE_DM                          ((USE_AVL_BYTEEN) ? 1 : 0),
         .MMR_ENABLE_RMW                         (ENABLE_ECC),
         .MMR_ENABLE_AUTO_CORR                   (ENABLE_ECC_AUTO_CORRECTION),
         .MMR_ECC_CODE_OVERWRITE                 (0),
         .MMR_GEN_SBE                            (0),
         .MMR_GEN_DBE                            (0),
         .MMR_ENABLE_INTR                        (1),
         .MMR_MASK_SBE_INTR                      (0),
         .MMR_MASK_DBE_INTR                      (0),
         .MMR_MASK_CORR_DROPPED_INTR             (0),
         .MMR_MASK_HMI_INTR                      (0),
         .MMR_CLR_INTR                           (0),
         .MMR_CLR_MR_RDATA                       (0),
         .CFG_WRBUFFER_ADDR_WIDTH                (CFG_WRBUFFER_ADDR_WIDTH),
         .CFG_PORT_WIDTH_DRAM_DATA_WIDTH         (CFG_PORT_WIDTH_DRAM_DATA_WIDTH),
         .CFG_PORT_WIDTH_LOCAL_DATA_WIDTH        (CFG_PORT_WIDTH_LOCAL_DATA_WIDTH), 
         .CFG_PORT_WIDTH_ADDR_WIDTH              (CFG_PORT_WIDTH_ADDR_WIDTH),
         .CFG_PORT_WIDTH_DATA_RATE               (CFG_PORT_WIDTH_DATA_RATE),
         .CFG_PORT_WIDTH_ECC_IN_PROTOCOL         (CFG_PORT_WIDTH_ECC_IN_PROTOCOL),
         .CFG_PORT_WIDTH_WRPATH_PIPELINE_EN      (CFG_PORT_WIDTH_WRPATH_PIPELINE_EN),
         .CFG_PORT_WIDTH_ENABLE_ECC              (CFG_PORT_WIDTH_ENABLE_ECC),
         .CFG_PORT_WIDTH_ENABLE_DM               (CFG_PORT_WIDTH_ENABLE_DM),
         .CFG_PORT_WIDTH_ENABLE_RMW              (CFG_PORT_WIDTH_ENABLE_RMW),
         .CFG_PORT_WIDTH_ENABLE_AUTO_CORR        (CFG_PORT_WIDTH_ENABLE_AUTO_CORR),
         .CFG_PORT_WIDTH_ECC_CODE_OVERWRITE      (CFG_PORT_WIDTH_ECC_CODE_OVERWRITE),
         .CFG_PORT_WIDTH_GEN_SBE                 (CFG_PORT_WIDTH_GEN_SBE),
         .CFG_PORT_WIDTH_GEN_DBE                 (CFG_PORT_WIDTH_GEN_DBE),
         .CFG_PORT_WIDTH_ENABLE_INTR             (CFG_PORT_WIDTH_ENABLE_INTR),
         .CFG_PORT_WIDTH_MASK_SBE_INTR           (CFG_PORT_WIDTH_MASK_SBE_INTR),
         .CFG_PORT_WIDTH_MASK_DBE_INTR           (CFG_PORT_WIDTH_MASK_DBE_INTR),
         .CFG_PORT_WIDTH_MASK_CORR_DROPPED_INTR  (CFG_PORT_WIDTH_MASK_CORR_DROPPED_INTR),
         .CFG_PORT_WIDTH_MASK_HMI_INTR           (CFG_PORT_WIDTH_MASK_HMI_INTR),
         .CFG_PORT_WIDTH_CLR_INTR                (CFG_PORT_WIDTH_CLR_INTR),
         .CFG_PORT_WIDTH_CLR_MR_RDATA            (CFG_PORT_WIDTH_CLR_MR_RDATA),
         .STS_PORT_WIDTH_ECC_INTR                (STS_PORT_WIDTH_ECC_INTR),
         .STS_PORT_WIDTH_SBE_ERROR               (STS_PORT_WIDTH_SBE_ERROR),
         .STS_PORT_WIDTH_DBE_ERROR               (STS_PORT_WIDTH_DBE_ERROR),
         .STS_PORT_WIDTH_CORR_DROPPED            (STS_PORT_WIDTH_CORR_DROPPED),
         .STS_PORT_WIDTH_SBE_COUNT               (STS_PORT_WIDTH_SBE_COUNT),
         .STS_PORT_WIDTH_DBE_COUNT               (STS_PORT_WIDTH_DBE_COUNT),
         .STS_PORT_WIDTH_CORR_DROPPED_COUNT      (STS_PORT_WIDTH_CORR_DROPPED_COUNT),
         .STS_PORT_WIDTH_ERR_ADDR                (STS_PORT_WIDTH_ERR_ADDR),
         .STS_PORT_WIDTH_CORR_DROPPED_ADDR       (STS_PORT_WIDTH_CORR_DROPPED_ADDR),
         .STS_PORT_WIDTH_MR_DATA                 (STS_PORT_WIDTH_MR_DATA),
         .STS_PORT_WIDTH_MR_DATA_VALID           (STS_PORT_WIDTH_MR_DATA_VALID)
      ) ecc (
         .ctl_clk                                (emif_usr_clk_sec_in),
         .ctl_reset_n_pre_reg                    (emif_usr_reset_n_sec_in),

         .slave_cmd_ready                        (amm_ready_1),
         .slave_cmd_data                         (slave_cmd_data_wire_1),
         .slave_cmd_valid                        (amm_write_1 | amm_read_1),
         .slave_wr_data_ready                    (),
         .slave_wr_data_byte_enable              ((USE_AVL_BYTEEN) ? amm_byteenable_1 : {(CFG_LOCAL_BE_WIDTH){1'b1}}),
         .slave_wr_data                          (amm_writedata_1),
         .slave_wr_data_id                       ({(CFG_LOCAL_ID_WIDTH){1'b0}}), 
         .slave_wr_data_valid                    (amm_write_1),
         .slave_rd_data_ready                    (1'b1),
         .slave_rd_data                          (amm_readdata_1),
         .slave_rd_data_id                       (),
         .slave_rd_data_valid                    (amm_readdatavalid_1),
         .slave_rd_data_error                    (ctrl_ecc_readdataerror_1),
            
         .master_cmd_ready                       (ast_cmd_ready_1),
         .master_cmd_data                        (ast_cmd_data_1),
         .master_cmd_valid                       (ast_cmd_valid_1),
         .master_cmd_data_combi                  (),
         .master_cmd_valid_combi                 (),
         .master_cmd_info                        (ctrl_ecc_cmd_info_1),
         .master_wr_data_ready                   (ast_wr_ready_1),
         .master_wr_data_byte_enable             (ctrl_ecc_wr_byte_enable_1),
         .master_wr_data                         (ast_wr_data_without_byteen_1),
         .master_wr_data_id                      (),
         .master_wr_data_info                    (ctrl_ecc_write_info_1[2:0]),
         .master_wr_data_ptr_in                  (ctrl_ecc_wr_pointer_info_1),
         .master_wr_data_ptr_out                 (ctrl_ecc_write_info_1[PORT_CTRL_ECC_WRITE_INFO_WIDTH-1:3]),
         .master_wr_data_valid                   (ast_wr_valid_1),
         .master_rd_data_ready                   (ast_rd_ready_1),
         .master_rd_data                         (ast_rd_data_1),
         .master_rd_data_id                      (ctrl_ecc_rdata_id_1),
         .master_rd_data_info                    (ctrl_ecc_read_info_1),
         .master_rd_data_valid                   (ast_rd_valid_1),
         .master_rd_data_type                    (1'b0),

         .slave_mmr_ready                        (slave_mmr_ready_1),
         .slave_mmr_address                      ((CTRL_MMR_EN) ? mmr_slave_address_1 : {(PORT_CTRL_MMR_SLAVE_ADDRESS_WIDTH){1'b0}}),
         .slave_mmr_write                        ((CTRL_MMR_EN) ? mmr_slave_write_1 : 1'b0),
         .slave_mmr_read                         ((CTRL_MMR_EN) ? mmr_slave_read_1 : 1'b0),
         .slave_mmr_burstcount                   ((CTRL_MMR_EN) ? mmr_slave_burstcount_1 : {(PORT_CTRL_MMR_SLAVE_BCOUNT_WIDTH){1'b0}}),
         .slave_mmr_begintransfer                ((CTRL_MMR_EN) ? mmr_slave_beginbursttransfer_1 : 1'b0),
         .slave_mmr_wr_data                      ((CTRL_MMR_EN) ? mmr_slave_writedata_1 : {(PORT_CTRL_MMR_SLAVE_WDATA_WIDTH){1'b0}}),
         .slave_mmr_rd_data                      (mmr_slave_readdata_1),
         .slave_mmr_rd_data_valid                (mmr_slave_readdatavalid_1),
           
         .master_mmr_ready                       ((CTRL_MMR_EN) ? ~mmr_master_waitrequest_1 : 1'b1),
         .master_mmr_address                     (mmr_master_address_1),
         .master_mmr_write                       (mmr_master_write_1),
         .master_mmr_read                        (mmr_master_read_1),
         .master_mmr_burstcount                  (mmr_master_burstcount_1),
         .master_mmr_begintransfer               (mmr_master_beginbursttransfer_1),
         .master_mmr_wr_data                     (mmr_master_writedata_1),
         .master_mmr_rd_data                     ((CTRL_MMR_EN) ? mmr_master_readdata_1 : {(PORT_CTRL_MMR_MASTER_RDATA_WIDTH){1'b0}}),
         .master_mmr_rd_data_valid               ((CTRL_MMR_EN) ? mmr_master_readdatavalid_1 : 1'b0),

         .sts_ecc_intr                           (sts_ecc_intr_1),
         .sts_sbe_error                          (sts_sbe_error_1),
         .sts_dbe_error                          (sts_dbe_error_1),
         .sts_corr_dropped                       (sts_corr_dropped_1),
         .sts_sbe_count                          (sts_sbe_count_1),
         .sts_dbe_count                          (sts_dbe_count_1),
         .sts_corr_dropped_count                 (sts_corr_dropped_count_1),
         .sts_err_addr                           (sts_err_addr_1),
         .sts_corr_dropped_addr                  (sts_corr_dropped_addr_1),

         .user_interrupt                         (ctrl_ecc_user_interrupt_1),
         .hmi_interrupt                          (1'b0) 
      );      
      
      assign mmr_slave_waitrequest_1 = ~slave_mmr_ready_1;

      if (DIAG_SIM_MEMORY_PRELOAD_AFT_SYNTH_OVRD) begin : gen_preload
         altera_emif_preload_ecc_encoder #
         ( 
            .DIAG_USE_ABSTRACT_PHY                  (DIAG_USE_ABSTRACT_PHY_AFT_SYNTH_OVRD),
            .DIAG_SIM_MEMORY_PRELOAD_ECC_FILE       (DIAG_SIM_MEMORY_PRELOAD_SEC_ECC_FILE),
            .DIAG_SIM_MEMORY_PRELOAD_MEM_FILE       (DIAG_SIM_MEMORY_PRELOAD_SEC_MEM_FILE),
            .DIAG_SIM_MEMORY_PRELOAD_ABPHY_FILE     (DIAG_SIM_MEMORY_PRELOAD_SEC_ABPHY_FILE),
            .CTRL_AMM_ADDRESS_WIDTH                 (PORT_CTRL_AMM_ADDRESS_WIDTH),
            .CTRL_AMM_DATA_WIDTH                    (PORT_CTRL_AMM_WDATA_WIDTH),
            .MEM_DQ_WIDTH                           (MEM_DQ_WIDTH),
            .USE_AVL_BYTEEN                         (USE_AVL_BYTEEN),
            .CFG_ADDR_ENCODE_ENABLED                (CFG_ADDR_ENCODE_ENABLED)
         ) preload_inst (
            .emif_usr_clk                           (emif_usr_clk_sec_in)
         );
      end

      assign ctrl_ecc_sts_intr               = {sts_ecc_intr_0, sts_ecc_intr_1};
      assign ctrl_ecc_sts_sbe_error          = {sts_sbe_error_0, sts_sbe_error_1};
      assign ctrl_ecc_sts_dbe_error          = {sts_dbe_error_0,  sts_dbe_error_1};
      assign ctrl_ecc_sts_corr_dropped       = {sts_corr_dropped_0, sts_corr_dropped_1};
      assign ctrl_ecc_sts_sbe_count          = {sts_sbe_count_0, sts_sbe_count_1};
      assign ctrl_ecc_sts_dbe_count          = {sts_dbe_count_0, sts_dbe_count_1};
      assign ctrl_ecc_sts_corr_dropped_count = {sts_corr_dropped_count_0, sts_corr_dropped_count_1};
      assign ctrl_ecc_sts_err_addr           = {sts_err_addr_0, sts_err_addr_1};
      assign ctrl_ecc_sts_corr_dropped_addr  = {sts_corr_dropped_addr_0, sts_corr_dropped_addr_1};

   end else begin : no_pp
      assign ctrl_ecc_sts_intr                = sts_ecc_intr_0;
      assign ctrl_ecc_sts_sbe_error           = sts_sbe_error_0;
      assign ctrl_ecc_sts_dbe_error           = sts_dbe_error_0;
      assign ctrl_ecc_sts_corr_dropped        = sts_corr_dropped_0;
      assign ctrl_ecc_sts_sbe_count           = sts_sbe_count_0;
      assign ctrl_ecc_sts_dbe_count           = sts_dbe_count_0;
      assign ctrl_ecc_sts_corr_dropped_count  = sts_corr_dropped_count_0;
      assign ctrl_ecc_sts_err_addr            = sts_err_addr_0;
      assign ctrl_ecc_sts_corr_dropped_addr   = sts_corr_dropped_addr_0;

      assign amm_readdata_1                   = {(PORT_CTRL_AMM_RDATA_WIDTH){1'b0}};
      assign mmr_slave_readdata_1             = {(PORT_CTRL_MMR_SLAVE_RDATA_WIDTH){1'b0}};
      assign mmr_master_burstcount_1          = {(PORT_CTRL_MMR_MASTER_BCOUNT_WIDTH){1'b0}};
      assign mmr_master_writedata_1           = {(PORT_CTRL_MMR_MASTER_WDATA_WIDTH){1'b0}};
      assign mmr_master_address_1             = {(PORT_CTRL_MMR_MASTER_ADDRESS_WIDTH){1'b0}};
      assign ast_cmd_data_1                   = {(PORT_CTRL_AST_CMD_DATA_WIDTH){1'b0}};
      assign ast_wr_data_1                    = {(PORT_CTRL_AST_WR_DATA_WIDTH){1'b0}};
      assign ctrl_ecc_write_info_1            = {(PORT_CTRL_ECC_WRITE_INFO_WIDTH){1'b0}};
      assign amm_ready_1                      = 1'b0;
      assign amm_readdatavalid_1              = 1'b0;
      assign mmr_slave_waitrequest_1          = 1'b0;
      assign mmr_slave_readdatavalid_1        = 1'b0;
      assign mmr_master_write_1               = 1'b0;
      assign mmr_master_read_1                = 1'b0;
      assign mmr_master_beginbursttransfer_1  = 1'b0;
      assign ast_cmd_valid_1                  = 1'b0;
      assign ast_wr_valid_1                   = 1'b0;
      assign ast_rd_ready_1                   = 1'b0;
      assign ctrl_ecc_user_interrupt_1        = 1'b0;
      assign ctrl_ecc_readdataerror_1         = 1'b0;

      assign sts_ecc_intr_1                   = 'b0;
      assign sts_sbe_error_1                  = 'b0;
      assign sts_dbe_error_1                  = 'b0;
      assign sts_corr_dropped_1               = 'b0;
      assign sts_sbe_count_1                  = 'b0;
      assign sts_dbe_count_1                  = 'b0;
      assign sts_corr_dropped_count_1         = 'b0;
      assign sts_err_addr_1                   = 'b0;
      assign sts_corr_dropped_addr_1          = 'b0;
   end
endgenerate

endmodule
`ifdef QUESTA_INTEL_OEM
`pragma questa_oem_00 "sfv4CgBD2gRw66FfSic/D/DxyUF4ju6abSGjNZTz+XJ5wNcp1RmzgamT61rscvjMkkNKCYCGE4Hkry++3eL2fSJkmOtrYLQextJ2AFr2kX/6sa63SwNG1Dg8CndZgqHpcPsbI8J/52/6EA/5eQJiUNmwpEDzzugi2WpUBRBy4gGrSJ7A8zUzUrkHlWNSHE1mVOTkuXrL/BUqA6hBwwkS7qZD/J3TRyAu6L9p+9tB0ECCy5xW0zVEhjVRYnBlvIZ0gabXjoi++UuH0Ry+p4WHjlOAwTfLhMEdy81sX9ucGLj3DSJZHTEcA6olC3FUtERI4eS530tdEhTR/rWvDsC3pVrXe0iMkS0+qpk6Z7xYD0QQeYxmR11sH9fVeH6vxfVgHN1nmO/04w80cvaFdAM4d2JT39YMz3CUHSatbmmgSCTUD0rDMLwW+TB4b6eGv10dSWf3Eaogt1QrDjOksgAPD42DXu/cLSXhpEQ//Ng6tpWvug3Yxe4efOvQXSsj5CwsSNhZjsGV7yljdDMP+OVqm8u5O9mjuIZ+ZNMwsqSUvDVbWoNbhF0WgPqP/HlTyS2NO3GDnxE4XX1kNiBgZF3c42u0s4MQbvDENl6/l+H7NW9CXLIKs9qM0V88YRXEpbM4da3IwZqsUBRzMSJF7G9DUItgq0MSr/1fhHtE0lgMMEuVzukFDnCqruyjIeDW6tAWkj8KZgDLWOxZMUewKSqGrRyxuD2Y4ksE3f6Nf0ikZQxNV8ixOlzKODCvfLwKYV4HJea2EMCwE+XWK57pvYerjTJ/UCnZryNgHG5qDGD2D2pvVTmbeMnU3KlXFt5qCjqEuRxOkpQ6Agtkr1fdynpZTWIRZUr17g4pBKNXSEEtRC54mibOeYSO3I9eQm1h00Ig0gRvyCrsxgW8qhCR1JOyppIN3yxaZzxfkAIgq7p0MAz6CTtEvdv6ifik8az6iSgFVsAf4zRD4TyLSeHtT3wi7fb+a5g1UWTHNRPX6FLYua+fSr9br/Fk1tpXinpIn+Z1"
`endif
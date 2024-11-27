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

module fmiohmc_ecc_wrapper #
    ( parameter
        CFG_LOCAL_CMD_WIDTH                    = 2,
        CFG_LOCAL_ADDR_WIDTH                   = 35,
        CFG_LOCAL_SIZE_WIDTH                   = 8,
        CFG_LOCAL_ID_WIDTH                     = 13,
        CFG_LOCAL_PRI_WIDTH                    = 1,
        CFG_LOCAL_AP_WIDTH                     = 1,
        CFG_LOCAL_MC_WIDTH                     = 1,
        CFG_CMD_DATA_WIDTH                     = 61,
        CFG_CMD_INFO_WIDTH                     = 3,
        CFG_LOCAL_DATA_WIDTH                   = 81*8,
        CFG_LOCAL_BE_WIDTH                     = 9*8,
        CFG_LOCAL_DATA_INFO_WIDTH              = 3,
        CFG_LOCAL_DATA_PTR_WIDTH               = 6*2,
        CFG_ECC_DATA_WIDTH                     = 81*8,
        CFG_ECC_BE_WIDTH                       = 9*8,
        CFG_ECC_CODE_WIDTH                     = 8,
        CFG_ECC_MULTIPLE_INSTANCE              = 8, 
        
        CFG_REGISTER_CMD_PATH                  = 0,
        CFG_REGISTER_RDATA_PATH                = 0,
        CFG_REGISTER_RDATA_PATH_NUM            = 0,
        CFG_REGISTER_UFI_RDATA_PATH_NUM        = 0,
        CFG_REGISTER_WDATA_PATH                = 0,
        CFG_REGISTER_WDATA_PATH_NUM            = 0,
        CFG_REGISTER_ST_WDATA_RDY_LAT_PATH     = 0,
        CFG_REGISTER_ST_RDATA_RDY_LAT_PATH     = 0,
        CFG_REGISTER_ST_CMD_RDY_LAT_PATH       = 0,
        CORE_CMD_PIPELINE_WDATA                = 0,
        
        CFG_MMR_ADDR_WIDTH                     = 10,
        CFG_MMR_DATA_WIDTH                     = 32,
        CFG_MMR_BYTE_ENABLE_WIDTH              = 4,
        CFG_MMR_BURSTCOUNT_WIDTH               = 2,
        
        MMR_DRAM_DATA_WIDTH                    = 0,
        MMR_LOCAL_DATA_WIDTH                   = 0,
        MMR_ADDR_WIDTH                         = 0,
        MMR_DATA_RATE                          = 0,
        MMR_ECC_IN_PROTOCOL                    = 0,
        MMR_WRPATH_PIPELINE_EN                 = 0,
        MMR_ENABLE_ECC                         = 0,
        MMR_ENABLE_DM                          = 0,
        MMR_ENABLE_RMW                         = 0,
        MMR_ENABLE_AUTO_CORR                   = 0,
        MMR_ECC_CODE_OVERWRITE                 = 0,
        MMR_GEN_SBE                            = 0,
        MMR_GEN_DBE                            = 0,
        MMR_ENABLE_INTR                        = 0,
        MMR_MASK_SBE_INTR                      = 0,
        MMR_MASK_DBE_INTR                      = 0,
        MMR_MASK_CORR_DROPPED_INTR             = 0,
        MMR_MASK_HMI_INTR                      = 0,
        MMR_CLR_INTR                           = 0,
        MMR_CLR_MR_RDATA                       = 0,
        ECC_MMR_READ_LATENCY                   = 2,
        
        CFG_WRBUFFER_ADDR_WIDTH                = 4,
        CFG_PORT_WIDTH_DRAM_DATA_WIDTH         = 8,
        CFG_PORT_WIDTH_LOCAL_DATA_WIDTH        = 8,
        CFG_PORT_WIDTH_ADDR_WIDTH              = 6,
        CFG_PORT_WIDTH_DATA_RATE               = 4,
        CFG_PORT_WIDTH_ECC_IN_PROTOCOL         = 1,
        CFG_PORT_WIDTH_WRPATH_PIPELINE_EN      = 1,
        CFG_PORT_WIDTH_ENABLE_ECC              = 1,
        CFG_PORT_WIDTH_ENABLE_DM               = 1,
        CFG_PORT_WIDTH_ENABLE_RMW              = 1,
        CFG_PORT_WIDTH_ENABLE_AUTO_CORR        = 1,
        CFG_PORT_WIDTH_ECC_CODE_OVERWRITE      = 1,
        CFG_PORT_WIDTH_GEN_SBE                 = 1,
        CFG_PORT_WIDTH_GEN_DBE                 = 1,
        CFG_PORT_WIDTH_ENABLE_INTR             = 1,
        CFG_PORT_WIDTH_MASK_SBE_INTR           = 1,
        CFG_PORT_WIDTH_MASK_DBE_INTR           = 1,
        CFG_PORT_WIDTH_MASK_CORR_DROPPED_INTR  = 1,
        CFG_PORT_WIDTH_MASK_HMI_INTR           = 1,
        CFG_PORT_WIDTH_CLR_INTR                = 1,
        CFG_PORT_WIDTH_CLR_MR_RDATA            = 1,
        
        STS_PORT_WIDTH_ECC_INTR                = 1,
        STS_PORT_WIDTH_SBE_ERROR               = 1,
        STS_PORT_WIDTH_DBE_ERROR               = 1,
        STS_PORT_WIDTH_CORR_DROPPED            = 1,
        STS_PORT_WIDTH_SBE_COUNT               = 4,
        STS_PORT_WIDTH_DBE_COUNT               = 4,
        STS_PORT_WIDTH_CORR_DROPPED_COUNT      = 4,
        STS_PORT_WIDTH_ERR_ADDR                = 35,
        STS_PORT_WIDTH_CORR_DROPPED_ADDR       = 35,
        STS_PORT_WIDTH_MR_DATA                 = 81*8,
        STS_PORT_WIDTH_MR_DATA_VALID           = 1
    )
    (
        ctl_clk,
        ctl_reset_n_pre_reg,
        
        slave_mmr_ready,
        slave_mmr_address,
        slave_mmr_write,
        slave_mmr_read,
        slave_mmr_burstcount,
        slave_mmr_begintransfer,
        slave_mmr_wr_data,
        slave_mmr_rd_data,
        slave_mmr_rd_data_valid,
        
        master_mmr_ready,
        master_mmr_address,
        master_mmr_write,
        master_mmr_read,
        master_mmr_burstcount,
        master_mmr_begintransfer,
        master_mmr_wr_data,
        master_mmr_rd_data,
        master_mmr_rd_data_valid,
        
        slave_cmd_ready,
        slave_cmd_data,
        slave_cmd_valid,
        slave_wr_data_ready,
        slave_wr_data_byte_enable,
        slave_wr_data,
        slave_wr_data_id,
        slave_wr_data_valid,
        slave_rd_data_ready,
        slave_rd_data,
        slave_rd_data_id,
        slave_rd_data_valid,
        slave_rd_data_error,
        slave_rd_data_type,

        sts_ecc_intr,
        sts_sbe_error,
        sts_dbe_error,
        sts_corr_dropped,
        sts_sbe_count,
        sts_dbe_count,
        sts_corr_dropped_count,
        sts_err_addr,
        sts_corr_dropped_addr,
        
        master_cmd_ready,
        master_cmd_data,
        master_cmd_valid,
        master_cmd_data_combi,
        master_cmd_valid_combi,
        master_cmd_info,
        master_wr_data_ready,
        master_wr_data_byte_enable,
        master_wr_data,
        master_wr_data_id,
        master_wr_data_info,
        master_wr_data_ptr_in,
        master_wr_data_ptr_out,
        master_wr_data_valid,
        master_rd_data_ready,
        master_rd_data,
        master_rd_data_id,
        master_rd_data_info,
        master_rd_data_valid,
        master_rd_data_type,
        
        user_interrupt,
        hmi_interrupt
    );

localparam RD_FIFO_WIDTH = CFG_ECC_DATA_WIDTH + CFG_LOCAL_ID_WIDTH + CFG_LOCAL_DATA_INFO_WIDTH + 1;

input                                                  ctl_clk;
input                                                  ctl_reset_n_pre_reg;

output                                                 slave_mmr_ready;
input  [CFG_MMR_ADDR_WIDTH                    - 1 : 0] slave_mmr_address;
input                                                  slave_mmr_write;
input                                                  slave_mmr_read;
input  [CFG_MMR_BURSTCOUNT_WIDTH              - 1 : 0] slave_mmr_burstcount;
input                                                  slave_mmr_begintransfer;
input  [CFG_MMR_DATA_WIDTH                    - 1 : 0] slave_mmr_wr_data;
output [CFG_MMR_DATA_WIDTH                    - 1 : 0] slave_mmr_rd_data;
output                                                 slave_mmr_rd_data_valid;

input                                                  master_mmr_ready;
output [CFG_MMR_ADDR_WIDTH                    - 1 : 0] master_mmr_address;
output                                                 master_mmr_write;
output                                                 master_mmr_read;
output [CFG_MMR_BURSTCOUNT_WIDTH              - 1 : 0] master_mmr_burstcount;
output                                                 master_mmr_begintransfer;
output [CFG_MMR_DATA_WIDTH                    - 1 : 0] master_mmr_wr_data;
input  [CFG_MMR_DATA_WIDTH                    - 1 : 0] master_mmr_rd_data;
input                                                  master_mmr_rd_data_valid;

output                                                 slave_cmd_ready;
input  [CFG_CMD_DATA_WIDTH                    - 1 : 0] slave_cmd_data;
input                                                  slave_cmd_valid;
output                                                 slave_wr_data_ready;
input  [CFG_LOCAL_BE_WIDTH                    - 1 : 0] slave_wr_data_byte_enable;
input  [CFG_LOCAL_DATA_WIDTH                  - 1 : 0] slave_wr_data;
input  [CFG_LOCAL_ID_WIDTH                    - 1 : 0] slave_wr_data_id;
input                                                  slave_wr_data_valid;
input                                                  slave_rd_data_ready;
output [CFG_LOCAL_DATA_WIDTH                  - 1 : 0] slave_rd_data;
output [CFG_LOCAL_ID_WIDTH                    - 1 : 0] slave_rd_data_id;
output                                                 slave_rd_data_valid;
output                                                 slave_rd_data_error;
output                                                 slave_rd_data_type;

input                                                  master_cmd_ready;
output [CFG_CMD_DATA_WIDTH                    - 1 : 0] master_cmd_data;
output                                                 master_cmd_valid;
output [CFG_CMD_DATA_WIDTH                    - 1 : 0] master_cmd_data_combi;
output                                                 master_cmd_valid_combi;
input  [CFG_CMD_INFO_WIDTH                    - 1 : 0] master_cmd_info;
input                                                  master_wr_data_ready;
output [CFG_ECC_BE_WIDTH                      - 1 : 0] master_wr_data_byte_enable;
output [CFG_ECC_DATA_WIDTH                    - 1 : 0] master_wr_data;
output [CFG_LOCAL_ID_WIDTH                    - 1 : 0] master_wr_data_id;
output [CFG_LOCAL_DATA_INFO_WIDTH             - 1 : 0] master_wr_data_info;
input  [CFG_LOCAL_DATA_PTR_WIDTH              - 1 : 0] master_wr_data_ptr_in;
output [CFG_LOCAL_DATA_PTR_WIDTH              - 1 : 0] master_wr_data_ptr_out;
output                                                 master_wr_data_valid;
output                                                 master_rd_data_ready;
input  [CFG_ECC_DATA_WIDTH                    - 1 : 0] master_rd_data;
input  [CFG_LOCAL_ID_WIDTH                    - 1 : 0] master_rd_data_id;
input  [CFG_LOCAL_DATA_INFO_WIDTH             - 1 : 0] master_rd_data_info;
input                                                  master_rd_data_valid;
input                                                  master_rd_data_type;

output                                                 user_interrupt;
input                                                  hmi_interrupt;


output wire [STS_PORT_WIDTH_ECC_INTR          - 1 : 0] sts_ecc_intr;
output wire [STS_PORT_WIDTH_SBE_ERROR         - 1 : 0] sts_sbe_error;
output wire [STS_PORT_WIDTH_DBE_ERROR         - 1 : 0] sts_dbe_error;
output wire [STS_PORT_WIDTH_CORR_DROPPED      - 1 : 0] sts_corr_dropped;
output wire [STS_PORT_WIDTH_SBE_COUNT         - 1 : 0] sts_sbe_count;
output wire [STS_PORT_WIDTH_DBE_COUNT         - 1 : 0] sts_dbe_count;
output wire [STS_PORT_WIDTH_CORR_DROPPED_COUNT- 1 : 0] sts_corr_dropped_count;
output wire [STS_PORT_WIDTH_ERR_ADDR          - 1 : 0] sts_err_addr;
output wire [STS_PORT_WIDTH_CORR_DROPPED_ADDR - 1 : 0] sts_corr_dropped_addr;

wire [STS_PORT_WIDTH_MR_DATA                  - 1 : 0] sts_mr_rdata_0;
wire [STS_PORT_WIDTH_MR_DATA                  - 1 : 0] sts_mr_rdata_1;
wire [STS_PORT_WIDTH_MR_DATA_VALID            - 1 : 0] sts_mr_rdata_valid;
wire                                                   slave_cmd_ready;
wire                                                   slave_wr_data_ready;
wire [CFG_LOCAL_DATA_WIDTH                    - 1 : 0] slave_rd_data;
wire [CFG_LOCAL_ID_WIDTH                      - 1 : 0] slave_rd_data_id;
wire                                                   slave_rd_data_valid;
wire                                                   slave_rd_data_error;
wire                                                   slave_rd_data_type;
wire [CFG_CMD_DATA_WIDTH                      - 1 : 0] master_cmd_data;
wire                                                   master_cmd_valid;
wire [CFG_CMD_DATA_WIDTH                      - 1 : 0] master_cmd_data_combi;
wire                                                   master_cmd_valid_combi;
wire [CFG_ECC_BE_WIDTH                        - 1 : 0] master_wr_data_byte_enable;
wire [CFG_ECC_DATA_WIDTH                      - 1 : 0] master_wr_data;
wire [CFG_LOCAL_ID_WIDTH                      - 1 : 0] master_wr_data_id;
wire [CFG_LOCAL_DATA_INFO_WIDTH               - 1 : 0] master_wr_data_info;
wire [CFG_LOCAL_DATA_PTR_WIDTH                - 1 : 0] master_wr_data_ptr_out;
wire                                                   master_wr_data_valid;
wire                                                   master_rd_data_ready;
wire                                                   user_interrupt;
wire [CFG_PORT_WIDTH_DRAM_DATA_WIDTH          - 1 : 0] cfg_dram_data_width;
wire [CFG_PORT_WIDTH_LOCAL_DATA_WIDTH         - 1 : 0] cfg_local_data_width;
wire [CFG_PORT_WIDTH_ADDR_WIDTH               - 1 : 0] cfg_addr_width;
wire [CFG_PORT_WIDTH_DATA_RATE                - 1 : 0] cfg_data_rate;
wire [CFG_PORT_WIDTH_ECC_IN_PROTOCOL          - 1 : 0] cfg_ecc_in_protocol;
wire [CFG_PORT_WIDTH_WRPATH_PIPELINE_EN       - 1 : 0] cfg_wrpath_pipeline_en;
wire [CFG_PORT_WIDTH_ENABLE_ECC               - 1 : 0] cfg_enable_ecc;
wire [CFG_PORT_WIDTH_ENABLE_DM                - 1 : 0] cfg_enable_dm;
wire [CFG_PORT_WIDTH_ENABLE_RMW               - 1 : 0] cfg_enable_rmw;
wire [CFG_PORT_WIDTH_ENABLE_AUTO_CORR         - 1 : 0] cfg_enable_auto_corr;
wire [CFG_PORT_WIDTH_ECC_CODE_OVERWRITE       - 1 : 0] cfg_ecc_code_overwrite;
wire [CFG_PORT_WIDTH_GEN_SBE                  - 1 : 0] cfg_gen_sbe;
wire [CFG_PORT_WIDTH_GEN_DBE                  - 1 : 0] cfg_gen_dbe;
wire [CFG_PORT_WIDTH_ENABLE_INTR              - 1 : 0] cfg_enable_intr;
wire [CFG_PORT_WIDTH_MASK_SBE_INTR            - 1 : 0] cfg_mask_sbe_intr;
wire [CFG_PORT_WIDTH_MASK_DBE_INTR            - 1 : 0] cfg_mask_dbe_intr;
wire [CFG_PORT_WIDTH_MASK_CORR_DROPPED_INTR   - 1 : 0] cfg_mask_corr_dropped_intr;
wire [CFG_PORT_WIDTH_MASK_HMI_INTR            - 1 : 0] cfg_mask_hmi_intr;
wire [CFG_PORT_WIDTH_CLR_INTR                 - 1 : 0] cfg_clr_intr;
wire [CFG_PORT_WIDTH_CLR_MR_RDATA             - 1 : 0] cfg_clr_mr_rdata;
wire                                                   slave_mmr_ready;
wire [CFG_MMR_DATA_WIDTH                      - 1 : 0] slave_mmr_rd_data;
wire                                                   slave_mmr_rd_data_valid;
wire [CFG_MMR_ADDR_WIDTH                      - 1 : 0] master_mmr_address;
wire                                                   master_mmr_write;
wire                                                   master_mmr_read;
wire [CFG_MMR_BURSTCOUNT_WIDTH                - 1 : 0] master_mmr_burstcount;
wire                                                   master_mmr_begintransfer;
wire [CFG_MMR_DATA_WIDTH                      - 1 : 0] master_mmr_wr_data;

(* altera_attribute = {"-name MAX_FANOUT 1; -name ADV_NETLIST_OPT_ALLOWED ALWAYS_ALLOW"}*) reg                                                    internal_master_wr_data_ready;
(* altera_attribute = {"-name MAX_FANOUT 1; -name ADV_NETLIST_OPT_ALLOWED ALWAYS_ALLOW"}*) reg  [CFG_ECC_BE_WIDTH                        - 1 : 0] internal_master_wr_data_byte_enable;
reg  [CFG_LOCAL_DATA_INFO_WIDTH               - 1 : 0] internal_master_wr_data_info;
(* altera_attribute = {"-name MAX_FANOUT 1; -name ADV_NETLIST_OPT_ALLOWED ALWAYS_ALLOW"}*) reg  [CFG_LOCAL_DATA_PTR_WIDTH                - 1 : 0] internal_master_wr_data_ptr_in;
reg  [CFG_LOCAL_DATA_PTR_WIDTH                - 1 : 0] internal_master_wr_data_ptr_out;
reg                                                    internal_master_wr_data_valid;
reg                                                    internal_master_rd_data_ready;

(* altera_attribute = {"-name MAX_FANOUT 1; -name ADV_NETLIST_OPT_ALLOWED ALWAYS_ALLOW"}*) reg                                                    internal_master_cmd_ready;
reg  [CFG_CMD_DATA_WIDTH                      - 1 : 0] internal_master_cmd_data;
(* altera_attribute = {"-name MAX_FANOUT 1; -name ADV_NETLIST_OPT_ALLOWED ALWAYS_ALLOW"}*) reg                                                    internal_master_cmd_valid;
reg  [CFG_CMD_INFO_WIDTH                      - 1 : 0] internal_master_cmd_info;

wire                                                   int_master_cmd_ready;
wire [CFG_CMD_DATA_WIDTH                      - 1 : 0] int_master_cmd_data;
wire [CFG_CMD_INFO_WIDTH                      - 1 : 0] int_master_cmd_info;
wire                                                   int_master_cmd_valid;

reg  [CFG_ECC_DATA_WIDTH                      - 1 : 0] internal_master_wr_data;
reg  [CFG_LOCAL_ID_WIDTH                      - 1 : 0] internal_master_wr_data_id;

wire                                                   int_master_wr_data_ready;
wire [CFG_ECC_BE_WIDTH                        - 1 : 0] int_master_wr_data_byte_enable;
wire [CFG_ECC_DATA_WIDTH                      - 1 : 0] int_master_wr_data;
wire [CFG_LOCAL_ID_WIDTH                      - 1 : 0] int_master_wr_data_id;
wire [CFG_LOCAL_DATA_INFO_WIDTH               - 1 : 0] int_master_wr_data_info;
wire [CFG_LOCAL_DATA_PTR_WIDTH                - 1 : 0] int_master_wr_data_ptr_in;
wire [CFG_LOCAL_DATA_PTR_WIDTH                - 1 : 0] int_master_wr_data_ptr_out;
wire                                                   int_master_wr_data_valid;

wire [CFG_ECC_DATA_WIDTH                      - 1 : 0] internal_master_rd_data;
wire [CFG_LOCAL_ID_WIDTH                      - 1 : 0] internal_master_rd_data_id;
wire [CFG_LOCAL_DATA_INFO_WIDTH               - 1 : 0] internal_master_rd_data_info;
wire                                                   internal_master_rd_data_valid;
wire                                                   internal_master_rd_data_type;

wire                                                   int_master_rd_data_ready;
wire [CFG_ECC_DATA_WIDTH                      - 1 : 0] int_master_rd_data;
wire [CFG_LOCAL_ID_WIDTH                      - 1 : 0] int_master_rd_data_id;
wire [CFG_LOCAL_DATA_INFO_WIDTH               - 1 : 0] int_master_rd_data_info;
wire                                                   int_master_rd_data_valid;
wire                                                   int_master_rd_data_type;

wire                                                   mux_master_cmd_ready;

// Pipeline the input reset_n signal.
// Don't use input reset_n directly because if it is promoted to global,
// the insertion delay is big enough to cause downstream logic that uses the
// reset as comb input to fail setup timing.
reg [25:0] ctl_reset_n /* synthesis preserve_syn_only = 1 */;
always @(posedge ctl_clk or negedge ctl_reset_n_pre_reg)
begin
   if (!ctl_reset_n_pre_reg) begin
      ctl_reset_n[25:0] <= 26'b0;
   end else begin
      ctl_reset_n[25:0] <= {26{1'b1}};
   end
end

always @ (posedge ctl_clk)
begin
    internal_master_cmd_ready <= master_cmd_ready;
end

always @ (posedge ctl_clk)
begin
    internal_master_cmd_valid <= int_master_cmd_valid & mux_master_cmd_ready;
end
    
always @ (posedge ctl_clk)
begin
    internal_master_cmd_data  <= int_master_cmd_data;
    internal_master_cmd_info  <= master_cmd_info;
end

assign int_master_cmd_ready = (CFG_REGISTER_CMD_PATH == 1) ? internal_master_cmd_ready : master_cmd_ready;
assign int_master_cmd_info  = (CFG_REGISTER_CMD_PATH == 1) ? internal_master_cmd_info  : master_cmd_info;

assign master_cmd_data      = (CFG_REGISTER_CMD_PATH == 1) ? internal_master_cmd_data  : int_master_cmd_data;
assign master_cmd_valid     = (CFG_REGISTER_CMD_PATH == 1) ? internal_master_cmd_valid : (int_master_cmd_valid & mux_master_cmd_ready);

reg  [CFG_ECC_BE_WIDTH                        - 1 : 0] internal_master_wr_data_byte_enable_r [1:0];
reg  [CFG_LOCAL_DATA_INFO_WIDTH               - 1 : 0] internal_master_wr_data_info_r [1:0];
reg  [CFG_LOCAL_DATA_PTR_WIDTH                - 1 : 0] internal_master_wr_data_ptr_out_r [1:0];
reg                                                    internal_master_wr_data_valid_r [1:0];
reg  [CFG_ECC_DATA_WIDTH                      - 1 : 0] internal_master_wr_data_r [1:0];
reg  [CFG_LOCAL_ID_WIDTH                      - 1 : 0] internal_master_wr_data_id_r [1:0];
reg                                                    internal_master_wr_data_ready_r [1:0];
reg  [CFG_LOCAL_DATA_PTR_WIDTH                - 1 : 0] internal_master_wr_data_ptr_in_r [1:0];

always @ (posedge ctl_clk)
begin
    internal_master_wr_data_valid_r[0] <= int_master_wr_data_valid;
    internal_master_wr_data_valid_r[1] <= internal_master_wr_data_valid_r[0];

    internal_master_wr_data_r[0]             <= int_master_wr_data;
    internal_master_wr_data_r[1]             <= internal_master_wr_data_r[0];
    internal_master_wr_data_byte_enable_r[0] <= int_master_wr_data_byte_enable;
    internal_master_wr_data_byte_enable_r[1] <= internal_master_wr_data_byte_enable_r[0];
    internal_master_wr_data_id_r[0]          <= int_master_wr_data_id;
    internal_master_wr_data_id_r[1]          <= internal_master_wr_data_id_r[0];
    internal_master_wr_data_info_r[0]        <= int_master_wr_data_info;
    internal_master_wr_data_info_r[1]        <= internal_master_wr_data_info_r[0];
    internal_master_wr_data_ptr_out_r[0]     <= int_master_wr_data_ptr_out;
    internal_master_wr_data_ptr_out_r[1]     <= internal_master_wr_data_ptr_out_r[0];
    
    internal_master_wr_data_ptr_in_r[0]    <= master_wr_data_ptr_in;
    internal_master_wr_data_ptr_in_r[1]    <= internal_master_wr_data_ptr_in_r[0];
    
    internal_master_wr_data_ready_r[0] <= master_wr_data_ready;
    internal_master_wr_data_ready_r[1] <= internal_master_wr_data_ready_r[0];

    if (CFG_REGISTER_WDATA_PATH_NUM < 2)
    begin
       internal_master_wr_data_valid         <= int_master_wr_data_valid;
       internal_master_wr_data               <= int_master_wr_data;
       internal_master_wr_data_byte_enable   <= int_master_wr_data_byte_enable;
       internal_master_wr_data_id            <= int_master_wr_data_id;
       internal_master_wr_data_info          <= int_master_wr_data_info;
       internal_master_wr_data_ptr_out       <= int_master_wr_data_ptr_out;
       internal_master_wr_data_ready         <= master_wr_data_ready;
       internal_master_wr_data_ptr_in        <= master_wr_data_ptr_in;
    end
    else if (CFG_REGISTER_WDATA_PATH_NUM == 2)
    begin
       internal_master_wr_data_valid         <= internal_master_wr_data_valid_r       [0];
       internal_master_wr_data               <= internal_master_wr_data_r             [0];
       internal_master_wr_data_byte_enable   <= internal_master_wr_data_byte_enable_r [0];
       internal_master_wr_data_id            <= internal_master_wr_data_id_r          [0];
       internal_master_wr_data_info          <= internal_master_wr_data_info_r        [0];
       internal_master_wr_data_ptr_out       <= internal_master_wr_data_ptr_out_r     [0];
       internal_master_wr_data_ready         <= internal_master_wr_data_ready_r       [0];
       internal_master_wr_data_ptr_in        <= internal_master_wr_data_ptr_in_r      [0];
    end
    else if (CFG_REGISTER_WDATA_PATH_NUM == 4)
    begin
       internal_master_wr_data_valid         <= internal_master_wr_data_valid_r       [1];
       internal_master_wr_data               <= internal_master_wr_data_r             [1];
       internal_master_wr_data_byte_enable   <= internal_master_wr_data_byte_enable_r [1];
       internal_master_wr_data_id            <= internal_master_wr_data_id_r          [1];
       internal_master_wr_data_info          <= internal_master_wr_data_info_r        [1];
       internal_master_wr_data_ptr_out       <= internal_master_wr_data_ptr_out_r     [1];
       internal_master_wr_data_ready         <= internal_master_wr_data_ready_r       [1];
       internal_master_wr_data_ptr_in        <= internal_master_wr_data_ptr_in_r      [1];
    end
end

assign int_master_wr_data_ready   = (CFG_REGISTER_WDATA_PATH == 1) ? internal_master_wr_data_ready       : master_wr_data_ready;
assign int_master_wr_data_ptr_in  = (CFG_REGISTER_WDATA_PATH == 1) ? internal_master_wr_data_ptr_in      : master_wr_data_ptr_in;

assign master_wr_data_byte_enable = (CFG_REGISTER_WDATA_PATH == 1) ? internal_master_wr_data_byte_enable : int_master_wr_data_byte_enable;
assign master_wr_data             = (CFG_REGISTER_WDATA_PATH == 1) ? internal_master_wr_data             : int_master_wr_data;
assign master_wr_data_id          = (CFG_REGISTER_WDATA_PATH == 1) ? internal_master_wr_data_id          : int_master_wr_data_id;
assign master_wr_data_info        = (CFG_REGISTER_WDATA_PATH == 1) ? internal_master_wr_data_info        : int_master_wr_data_info;
assign master_wr_data_ptr_out     = (CFG_REGISTER_WDATA_PATH == 1) ? internal_master_wr_data_ptr_out     : int_master_wr_data_ptr_out;
assign master_wr_data_valid       = (CFG_REGISTER_WDATA_PATH == 1) ? internal_master_wr_data_valid       : int_master_wr_data_valid;

assign master_rd_data_ready       = (CFG_REGISTER_RDATA_PATH == 1) ? internal_master_rd_data_ready       : int_master_rd_data_ready;

assign int_master_rd_data         = (CFG_REGISTER_RDATA_PATH == 1) ? internal_master_rd_data             : master_rd_data;
assign int_master_rd_data_id      = (CFG_REGISTER_RDATA_PATH == 1) ? internal_master_rd_data_id          : master_rd_data_id;
assign int_master_rd_data_info    = (CFG_REGISTER_RDATA_PATH == 1) ? internal_master_rd_data_info        : master_rd_data_info;
assign int_master_rd_data_valid   = (CFG_REGISTER_RDATA_PATH == 1) ? internal_master_rd_data_valid       : master_rd_data_valid;
assign int_master_rd_data_type    = (CFG_REGISTER_RDATA_PATH == 1) ? internal_master_rd_data_type        : master_rd_data_type;

generate
    if (CFG_REGISTER_RDATA_PATH == 1)
    begin
        reg  [CFG_ECC_DATA_WIDTH        - 1 : 0] master_rd_data_r;
        reg  [CFG_LOCAL_ID_WIDTH        - 1 : 0] master_rd_data_id_r;
        reg  [CFG_LOCAL_DATA_INFO_WIDTH - 1 : 0] master_rd_data_info_r;
        reg                                      master_rd_data_valid_r;
        reg                                      master_rd_data_type_r;
        
        reg  [CFG_ECC_DATA_WIDTH        - 1 : 0] master_rd_data_pipe_out;
        reg  [CFG_LOCAL_ID_WIDTH        - 1 : 0] master_rd_data_id_pipe_out;
        reg  [CFG_LOCAL_DATA_INFO_WIDTH - 1 : 0] master_rd_data_info_pipe_out;
        reg                                      master_rd_data_valid_pipe_out;
        reg                                      master_rd_data_type_pipe_out;
        
        wire [RD_FIFO_WIDTH             - 1 : 0] rd_fifo_wr_data;
        wire                                     rd_fifo_wr_ready;
        wire                                     rd_fifo_wr_valid;
        wire [RD_FIFO_WIDTH             - 1 : 0] rd_fifo_rd_data;
        wire                                     rd_fifo_rd_ready;
        wire                                     rd_fifo_rd_valid;
        
        reg                                      rd_fifo_wr_ready_r;
        
        assign rd_fifo_wr_data  = {master_rd_data_pipe_out, master_rd_data_id_pipe_out, master_rd_data_info_pipe_out, master_rd_data_type_pipe_out};
        assign rd_fifo_wr_valid = master_rd_data_valid_pipe_out;
        assign rd_fifo_rd_ready = int_master_rd_data_ready;
        
        assign {internal_master_rd_data, internal_master_rd_data_id, internal_master_rd_data_info, internal_master_rd_data_type} = rd_fifo_rd_data;
        assign internal_master_rd_data_valid                                                                                     = rd_fifo_rd_valid;
        
        always @ (posedge ctl_clk)
        begin
            master_rd_data_valid_r <= master_rd_data_valid;
            
            master_rd_data_r             <= master_rd_data;
            master_rd_data_id_r          <= master_rd_data_id;
            master_rd_data_info_r        <= master_rd_data_info;
            master_rd_data_type_r        <= master_rd_data_type;

            master_rd_data_pipe_out       <= (CFG_REGISTER_RDATA_PATH_NUM == 2) ? master_rd_data_r       : master_rd_data;
            master_rd_data_id_pipe_out    <= (CFG_REGISTER_RDATA_PATH_NUM == 2) ? master_rd_data_id_r    : master_rd_data_id;
            master_rd_data_info_pipe_out  <= (CFG_REGISTER_RDATA_PATH_NUM == 2) ? master_rd_data_info_r  : master_rd_data_info;
            master_rd_data_type_pipe_out  <= (CFG_REGISTER_RDATA_PATH_NUM == 2) ? master_rd_data_type_r  : master_rd_data_type;
            master_rd_data_valid_pipe_out <= (CFG_REGISTER_RDATA_PATH_NUM == 2) ? master_rd_data_valid_r : master_rd_data_valid;
        end
        
        always @ (posedge ctl_clk)
        begin
            rd_fifo_wr_ready_r <= rd_fifo_wr_ready;
            internal_master_rd_data_ready <= (CFG_REGISTER_RDATA_PATH_NUM == 2) ? rd_fifo_wr_ready_r : rd_fifo_wr_ready;
        end
        
        (* altera_attribute = "-name AUTO_RAM_RECOGNITION OFF; -name INFER_RAMS_FROM_RAW_LOGIC OFF" *)
        fmiohmc_ecc_interface_fifo
        #(
            .DATA_WIDTH      (RD_FIFO_WIDTH              ),
            .RESERVE_ENTRY   (2*(CFG_REGISTER_RDATA_PATH_NUM + CFG_REGISTER_UFI_RDATA_PATH_NUM))
        )
        iohmc_ecc_interface_fifo_inst
        (
            .clk             (ctl_clk                   ),
            .reset_n         (ctl_reset_n[0]            ),
            .in_ready        (rd_fifo_wr_ready          ),
            .in_valid        (rd_fifo_wr_valid          ),
            .in_data         (rd_fifo_wr_data           ),
            .out_ready       (rd_fifo_rd_ready          ),
            .out_valid       (rd_fifo_rd_valid          ),
            .out_data        (rd_fifo_rd_data           )
        );
    end
    else
    begin
        assign {internal_master_rd_data, internal_master_rd_data_id, internal_master_rd_data_info, internal_master_rd_data_type} = {RD_FIFO_WIDTH{1'b0}};
        assign internal_master_rd_data_valid                                                                                     = 1'b0;
    end
endgenerate

fmiohmc_ecc #
    (
        .CFG_LOCAL_CMD_WIDTH                    (CFG_LOCAL_CMD_WIDTH                    ),
        .CFG_LOCAL_ADDR_WIDTH                   (CFG_LOCAL_ADDR_WIDTH                   ),
        .CFG_LOCAL_SIZE_WIDTH                   (CFG_LOCAL_SIZE_WIDTH                   ),
        .CFG_LOCAL_ID_WIDTH                     (CFG_LOCAL_ID_WIDTH                     ),
        .CFG_LOCAL_PRI_WIDTH                    (CFG_LOCAL_PRI_WIDTH                    ),
        .CFG_LOCAL_AP_WIDTH                     (CFG_LOCAL_AP_WIDTH                     ),
        .CFG_LOCAL_MC_WIDTH                     (CFG_LOCAL_MC_WIDTH                     ),
        .CFG_CMD_DATA_WIDTH                     (CFG_CMD_DATA_WIDTH                     ),
        .CFG_CMD_INFO_WIDTH                     (CFG_CMD_INFO_WIDTH                     ),
        .CFG_LOCAL_DATA_WIDTH                   (CFG_LOCAL_DATA_WIDTH                   ),
        .CFG_LOCAL_BE_WIDTH                     (CFG_LOCAL_BE_WIDTH                     ),
        .CFG_LOCAL_DATA_INFO_WIDTH              (CFG_LOCAL_DATA_INFO_WIDTH              ),
        .CFG_LOCAL_DATA_PTR_WIDTH               (CFG_LOCAL_DATA_PTR_WIDTH               ),
        .CFG_ECC_DATA_WIDTH                     (CFG_ECC_DATA_WIDTH                     ),
        .CFG_ECC_BE_WIDTH                       (CFG_ECC_BE_WIDTH                       ),
        .CFG_ECC_CODE_WIDTH                     (CFG_ECC_CODE_WIDTH                     ),
        .CFG_ECC_MULTIPLE_INSTANCE              (CFG_ECC_MULTIPLE_INSTANCE              ),
        .CFG_ECC_IN_PROTOCOL                    (MMR_ECC_IN_PROTOCOL                    ),
        .CFG_REGISTER_RDATA_PATH                (CFG_REGISTER_RDATA_PATH                ),
        .CFG_REGISTER_WDATA_PATH                (CFG_REGISTER_WDATA_PATH                ),
        .CFG_REGISTER_WDATA_PATH_NUM            (CFG_REGISTER_WDATA_PATH_NUM            ),
        .CFG_REGISTER_UFI_RDATA_PATH_NUM        (CFG_REGISTER_UFI_RDATA_PATH_NUM        ),
        .CFG_REGISTER_ST_WDATA_RDY_LAT_PATH     (CFG_REGISTER_ST_WDATA_RDY_LAT_PATH     ),
        .CFG_REGISTER_ST_RDATA_RDY_LAT_PATH     (CFG_REGISTER_ST_RDATA_RDY_LAT_PATH     ),
        .CFG_REGISTER_ST_CMD_RDY_LAT_PATH       (CFG_REGISTER_ST_CMD_RDY_LAT_PATH       ),
        .CORE_CMD_PIPELINE_WDATA                (CORE_CMD_PIPELINE_WDATA                ),
        .CFG_WRBUFFER_ADDR_WIDTH                (CFG_WRBUFFER_ADDR_WIDTH                ),
        .CFG_PORT_WIDTH_DRAM_DATA_WIDTH         (CFG_PORT_WIDTH_DRAM_DATA_WIDTH         ),
        .CFG_PORT_WIDTH_LOCAL_DATA_WIDTH        (CFG_PORT_WIDTH_LOCAL_DATA_WIDTH        ),
        .CFG_PORT_WIDTH_ADDR_WIDTH              (CFG_PORT_WIDTH_ADDR_WIDTH              ),
        .CFG_PORT_WIDTH_DATA_RATE               (CFG_PORT_WIDTH_DATA_RATE               ),
        .CFG_PORT_WIDTH_ECC_IN_PROTOCOL         (CFG_PORT_WIDTH_ECC_IN_PROTOCOL         ),
        .CFG_PORT_WIDTH_WRPATH_PIPELINE_EN      (CFG_PORT_WIDTH_WRPATH_PIPELINE_EN      ),
        .CFG_PORT_WIDTH_ENABLE_ECC              (CFG_PORT_WIDTH_ENABLE_ECC              ),
        .CFG_PORT_WIDTH_ENABLE_DM               (CFG_PORT_WIDTH_ENABLE_DM               ),
        .CFG_PORT_WIDTH_ENABLE_RMW              (CFG_PORT_WIDTH_ENABLE_RMW              ),
        .CFG_PORT_WIDTH_ENABLE_AUTO_CORR        (CFG_PORT_WIDTH_ENABLE_AUTO_CORR        ),
        .CFG_PORT_WIDTH_ECC_CODE_OVERWRITE      (CFG_PORT_WIDTH_ECC_CODE_OVERWRITE      ),
        .CFG_PORT_WIDTH_GEN_SBE                 (CFG_PORT_WIDTH_GEN_SBE                 ),
        .CFG_PORT_WIDTH_GEN_DBE                 (CFG_PORT_WIDTH_GEN_DBE                 ),
        .CFG_PORT_WIDTH_ENABLE_INTR             (CFG_PORT_WIDTH_ENABLE_INTR             ),
        .CFG_PORT_WIDTH_MASK_SBE_INTR           (CFG_PORT_WIDTH_MASK_SBE_INTR           ),
        .CFG_PORT_WIDTH_MASK_DBE_INTR           (CFG_PORT_WIDTH_MASK_DBE_INTR           ),
        .CFG_PORT_WIDTH_MASK_CORR_DROPPED_INTR  (CFG_PORT_WIDTH_MASK_CORR_DROPPED_INTR  ),
        .CFG_PORT_WIDTH_MASK_HMI_INTR           (CFG_PORT_WIDTH_MASK_HMI_INTR           ),
        .CFG_PORT_WIDTH_CLR_INTR                (CFG_PORT_WIDTH_CLR_INTR                ),
        .CFG_PORT_WIDTH_CLR_MR_RDATA            (CFG_PORT_WIDTH_CLR_MR_RDATA            ),
        .STS_PORT_WIDTH_ECC_INTR                (STS_PORT_WIDTH_ECC_INTR                ),
        .STS_PORT_WIDTH_SBE_ERROR               (STS_PORT_WIDTH_SBE_ERROR               ),
        .STS_PORT_WIDTH_DBE_ERROR               (STS_PORT_WIDTH_DBE_ERROR               ),
        .STS_PORT_WIDTH_CORR_DROPPED            (STS_PORT_WIDTH_CORR_DROPPED            ),
        .STS_PORT_WIDTH_SBE_COUNT               (STS_PORT_WIDTH_SBE_COUNT               ),
        .STS_PORT_WIDTH_DBE_COUNT               (STS_PORT_WIDTH_DBE_COUNT               ),
        .STS_PORT_WIDTH_CORR_DROPPED_COUNT      (STS_PORT_WIDTH_CORR_DROPPED_COUNT      ),
        .STS_PORT_WIDTH_ERR_ADDR                (STS_PORT_WIDTH_ERR_ADDR                ),
        .STS_PORT_WIDTH_CORR_DROPPED_ADDR       (STS_PORT_WIDTH_CORR_DROPPED_ADDR       ),
        .STS_PORT_WIDTH_MR_DATA                 (STS_PORT_WIDTH_MR_DATA                 ),
        .STS_PORT_WIDTH_MR_DATA_VALID           (STS_PORT_WIDTH_MR_DATA_VALID           )
    )
iohmc_ecc_inst
    (
        .ctl_clk                                (ctl_clk                                ),
        .ctl_reset_n                            (ctl_reset_n[24:1]                      ),
        .cfg_dram_data_width                    (cfg_dram_data_width                    ),
        .cfg_local_data_width                   (cfg_local_data_width                   ),
        .cfg_addr_width                         (cfg_addr_width                         ),
        .cfg_data_rate                          (cfg_data_rate                          ),
        .cfg_ecc_in_protocol                    (cfg_ecc_in_protocol                    ),
        .cfg_wrpath_pipeline_en                 (cfg_wrpath_pipeline_en                 ),
        .cfg_enable_ecc                         (cfg_enable_ecc                         ),
        .cfg_enable_dm                          (cfg_enable_dm                          ),
        .cfg_enable_rmw                         (cfg_enable_rmw                         ),
        .cfg_enable_auto_corr                   (cfg_enable_auto_corr                   ),
        .cfg_ecc_code_overwrite                 (cfg_ecc_code_overwrite                 ),
        .cfg_gen_sbe                            (cfg_gen_sbe                            ),
        .cfg_gen_dbe                            (cfg_gen_dbe                            ),
        .cfg_enable_intr                        (cfg_enable_intr                        ),
        .cfg_mask_sbe_intr                      (cfg_mask_sbe_intr                      ),
        .cfg_mask_dbe_intr                      (cfg_mask_dbe_intr                      ),
        .cfg_mask_corr_dropped_intr             (cfg_mask_corr_dropped_intr             ),
        .cfg_mask_hmi_intr                      (cfg_mask_hmi_intr                      ),
        .cfg_clr_intr                           (cfg_clr_intr                           ),
        .cfg_clr_mr_rdata                       (cfg_clr_mr_rdata                       ),
        .sts_ecc_intr                           (sts_ecc_intr                           ),
        .sts_sbe_error                          (sts_sbe_error                          ),
        .sts_dbe_error                          (sts_dbe_error                          ),
        .sts_corr_dropped                       (sts_corr_dropped                       ),
        .sts_sbe_count                          (sts_sbe_count                          ),
        .sts_dbe_count                          (sts_dbe_count                          ),
        .sts_corr_dropped_count                 (sts_corr_dropped_count                 ),
        .sts_err_addr                           (sts_err_addr                           ),
        .sts_corr_dropped_addr                  (sts_corr_dropped_addr                  ),
        .sts_mr_rdata_0                         (sts_mr_rdata_0                         ),
        .sts_mr_rdata_1                         (sts_mr_rdata_1                         ),
        .sts_mr_rdata_valid                     (sts_mr_rdata_valid                     ),
        .sts_corr_dropped_valid                 (                                       ), 
        .sts_current_addr                       (                                       ), 
        .decoder_output_err_addr                (                                       ), 
        .decoder_output_data_valid              (                                       ), 
        .decoder_output_sbe                     (                                       ), 
        .decoder_output_dbe                     (                                       ), 
        .decoder_output_data_dbe                (                                       ), 
        .decoder_output_addrerr                 (                                       ), 
        .slave_cmd_ready                        (slave_cmd_ready                        ),
        .slave_cmd_data                         (slave_cmd_data                         ),
        .slave_cmd_valid                        (slave_cmd_valid                        ),
        .slave_wr_data_ready                    (slave_wr_data_ready                    ),
        .slave_wr_data_byte_enable              (slave_wr_data_byte_enable              ),
        .slave_wr_data                          (slave_wr_data                          ),
        .slave_wr_data_id                       (slave_wr_data_id                       ),
        .slave_wr_data_valid                    (slave_wr_data_valid                    ),
        .slave_rd_data_ready                    (slave_rd_data_ready                    ),
        .slave_rd_data                          (slave_rd_data                          ),
        .slave_rd_data_id                       (slave_rd_data_id                       ),
        .slave_rd_data_valid                    (slave_rd_data_valid                    ),
        .slave_rd_data_error                    (slave_rd_data_error                    ),
        .slave_rd_data_type                     (slave_rd_data_type                     ),
        .master_cmd_ready                       (int_master_cmd_ready                   ),
        .master_cmd_data                        (int_master_cmd_data                    ),
        .master_cmd_valid                       (int_master_cmd_valid                   ),
        .master_cmd_data_combi                  (master_cmd_data_combi                  ),
        .master_cmd_valid_combi                 (master_cmd_valid_combi                 ),
        .master_cmd_info                        (int_master_cmd_info                    ),
        .master_wr_data_ready                   (int_master_wr_data_ready               ),
        .master_wr_data_byte_enable             (int_master_wr_data_byte_enable         ),
        .master_wr_data                         (int_master_wr_data                     ),
        .master_wr_data_id                      (int_master_wr_data_id                  ),
        .master_wr_data_info                    (int_master_wr_data_info                ),
        .master_wr_data_ptr_in                  (int_master_wr_data_ptr_in              ),
        .master_wr_data_ptr_out                 (int_master_wr_data_ptr_out             ),
        .master_wr_data_valid                   (int_master_wr_data_valid               ),
        .master_rd_data_ready                   (int_master_rd_data_ready               ),
        .master_rd_data                         (int_master_rd_data                     ),
        .master_rd_data_id                      (int_master_rd_data_id                  ),
        .master_rd_data_info                    (int_master_rd_data_info                ),
        .master_rd_data_valid                   (int_master_rd_data_valid               ),
        .master_rd_data_type                    (int_master_rd_data_type                ),
        .mux_master_cmd_ready                   (mux_master_cmd_ready                   ),
        .user_interrupt                         (user_interrupt                         ),
        .hmi_interrupt                          (hmi_interrupt                          ),
        .idle                                   (                                       ), 
        .push_to_error_address_fifo             (                                       )  
    );

fmiohmc_ecc_mmr #
    (
        .CFG_MMR_ADDR_WIDTH                     (CFG_MMR_ADDR_WIDTH                     ),
        .CFG_MMR_DATA_WIDTH                     (CFG_MMR_DATA_WIDTH                     ),
        .CFG_MMR_BYTE_ENABLE_WIDTH              (CFG_MMR_BYTE_ENABLE_WIDTH              ),
        .CFG_MMR_BURSTCOUNT_WIDTH               (CFG_MMR_BURSTCOUNT_WIDTH               ),
        .CFG_DRAM_DATA_WIDTH                    (MMR_DRAM_DATA_WIDTH                    ),
        .CFG_LOCAL_DATA_WIDTH                   (MMR_LOCAL_DATA_WIDTH                   ),
        .CFG_ADDR_WIDTH                         (MMR_ADDR_WIDTH                         ),
        .CFG_DATA_RATE                          (MMR_DATA_RATE                          ),
        .CFG_ECC_IN_PROTOCOL                    (MMR_ECC_IN_PROTOCOL                    ),
        .CFG_WRPATH_PIPELINE_EN                 (MMR_WRPATH_PIPELINE_EN                 ),
        .CFG_ENABLE_ECC                         (MMR_ENABLE_ECC                         ),
        .CFG_ENABLE_DM                          (MMR_ENABLE_DM                          ),
        .CFG_ENABLE_RMW                         (MMR_ENABLE_RMW                         ),
        .CFG_ENABLE_AUTO_CORR                   (MMR_ENABLE_AUTO_CORR                   ),
        .CFG_ECC_CODE_OVERWRITE                 (MMR_ECC_CODE_OVERWRITE                 ),
        .CFG_GEN_SBE                            (MMR_GEN_SBE                            ),
        .CFG_GEN_DBE                            (MMR_GEN_DBE                            ),
        .CFG_ENABLE_INTR                        (MMR_ENABLE_INTR                        ),
        .CFG_MASK_SBE_INTR                      (MMR_MASK_SBE_INTR                      ),
        .CFG_MASK_DBE_INTR                      (MMR_MASK_DBE_INTR                      ),
        .CFG_MASK_CORR_DROPPED_INTR             (MMR_MASK_CORR_DROPPED_INTR             ),
        .CFG_MASK_HMI_INTR                      (MMR_MASK_HMI_INTR                      ),
        .CFG_CLR_INTR                           (MMR_CLR_INTR                           ),
        .CFG_CLR_MR_RDATA                       (MMR_CLR_MR_RDATA                       ),
        .CFG_PORT_WIDTH_DRAM_DATA_WIDTH         (CFG_PORT_WIDTH_DRAM_DATA_WIDTH         ),
        .CFG_PORT_WIDTH_LOCAL_DATA_WIDTH        (CFG_PORT_WIDTH_LOCAL_DATA_WIDTH        ),
        .CFG_PORT_WIDTH_ADDR_WIDTH              (CFG_PORT_WIDTH_ADDR_WIDTH              ),
        .CFG_PORT_WIDTH_DATA_RATE               (CFG_PORT_WIDTH_DATA_RATE               ),
        .CFG_PORT_WIDTH_ECC_IN_PROTOCOL         (CFG_PORT_WIDTH_ECC_IN_PROTOCOL         ),
        .CFG_PORT_WIDTH_WRPATH_PIPELINE_EN      (CFG_PORT_WIDTH_WRPATH_PIPELINE_EN      ),
        .CFG_PORT_WIDTH_ENABLE_ECC              (CFG_PORT_WIDTH_ENABLE_ECC              ),
        .CFG_PORT_WIDTH_ENABLE_DM               (CFG_PORT_WIDTH_ENABLE_DM               ),
        .CFG_PORT_WIDTH_ENABLE_RMW              (CFG_PORT_WIDTH_ENABLE_RMW              ),
        .CFG_PORT_WIDTH_ENABLE_AUTO_CORR        (CFG_PORT_WIDTH_ENABLE_AUTO_CORR        ),
        .CFG_PORT_WIDTH_ECC_CODE_OVERWRITE      (CFG_PORT_WIDTH_ECC_CODE_OVERWRITE      ),
        .CFG_PORT_WIDTH_GEN_SBE                 (CFG_PORT_WIDTH_GEN_SBE                 ),
        .CFG_PORT_WIDTH_GEN_DBE                 (CFG_PORT_WIDTH_GEN_DBE                 ),
        .CFG_PORT_WIDTH_ENABLE_INTR             (CFG_PORT_WIDTH_ENABLE_INTR             ),
        .CFG_PORT_WIDTH_MASK_SBE_INTR           (CFG_PORT_WIDTH_MASK_SBE_INTR           ),
        .CFG_PORT_WIDTH_MASK_DBE_INTR           (CFG_PORT_WIDTH_MASK_DBE_INTR           ),
        .CFG_PORT_WIDTH_MASK_CORR_DROPPED_INTR  (CFG_PORT_WIDTH_MASK_CORR_DROPPED_INTR  ),
        .CFG_PORT_WIDTH_MASK_HMI_INTR           (CFG_PORT_WIDTH_MASK_HMI_INTR           ),
        .CFG_PORT_WIDTH_CLR_INTR                (CFG_PORT_WIDTH_CLR_INTR                ),
        .CFG_PORT_WIDTH_CLR_MR_RDATA            (CFG_PORT_WIDTH_CLR_MR_RDATA            ),
        .ECC_MMR_READ_LATENCY                   (ECC_MMR_READ_LATENCY                   ),
        .STS_PORT_WIDTH_ECC_INTR                (STS_PORT_WIDTH_ECC_INTR                ),
        .STS_PORT_WIDTH_SBE_ERROR               (STS_PORT_WIDTH_SBE_ERROR               ),
        .STS_PORT_WIDTH_DBE_ERROR               (STS_PORT_WIDTH_DBE_ERROR               ),
        .STS_PORT_WIDTH_CORR_DROPPED            (STS_PORT_WIDTH_CORR_DROPPED            ),
        .STS_PORT_WIDTH_SBE_COUNT               (STS_PORT_WIDTH_SBE_COUNT               ),
        .STS_PORT_WIDTH_DBE_COUNT               (STS_PORT_WIDTH_DBE_COUNT               ),
        .STS_PORT_WIDTH_CORR_DROPPED_COUNT      (STS_PORT_WIDTH_CORR_DROPPED_COUNT      ),
        .STS_PORT_WIDTH_ERR_ADDR                (STS_PORT_WIDTH_ERR_ADDR                ),
        .STS_PORT_WIDTH_CORR_DROPPED_ADDR       (STS_PORT_WIDTH_CORR_DROPPED_ADDR       ),
        .STS_PORT_WIDTH_MR_DATA                 (STS_PORT_WIDTH_MR_DATA                 ),
        .STS_PORT_WIDTH_MR_DATA_VALID           (STS_PORT_WIDTH_MR_DATA_VALID           )
    )
iohmc_ecc_mmr_inst
    (
        .ctl_clk                                (ctl_clk                                ),
        .ctl_reset_n                            (ctl_reset_n[25]                        ),
        .cfg_dram_data_width                    (cfg_dram_data_width                    ),
        .cfg_local_data_width                   (cfg_local_data_width                   ),
        .cfg_addr_width                         (cfg_addr_width                         ),
        .cfg_data_rate                          (cfg_data_rate                          ),
        .cfg_ecc_in_protocol                    (cfg_ecc_in_protocol                    ),
        .cfg_wrpath_pipeline_en                 (cfg_wrpath_pipeline_en                 ),
        .cfg_enable_ecc                         (cfg_enable_ecc                         ),
        .cfg_enable_dm                          (cfg_enable_dm                          ),
        .cfg_enable_rmw                         (cfg_enable_rmw                         ),
        .cfg_enable_auto_corr                   (cfg_enable_auto_corr                   ),
        .cfg_ecc_code_overwrite                 (cfg_ecc_code_overwrite                 ),
        .cfg_gen_sbe                            (cfg_gen_sbe                            ),
        .cfg_gen_dbe                            (cfg_gen_dbe                            ),
        .cfg_enable_intr                        (cfg_enable_intr                        ),
        .cfg_mask_sbe_intr                      (cfg_mask_sbe_intr                      ),
        .cfg_mask_dbe_intr                      (cfg_mask_dbe_intr                      ),
        .cfg_mask_corr_dropped_intr             (cfg_mask_corr_dropped_intr             ),
        .cfg_mask_hmi_intr                      (cfg_mask_hmi_intr                      ),
        .cfg_clr_intr                           (cfg_clr_intr                           ),
        .cfg_clr_mr_rdata                       (cfg_clr_mr_rdata                       ),
        .sts_ecc_intr                           (sts_ecc_intr                           ),
        .sts_sbe_error                          (sts_sbe_error                          ),
        .sts_dbe_error                          (sts_dbe_error                          ),
        .sts_corr_dropped                       (sts_corr_dropped                       ),
        .sts_sbe_count                          (sts_sbe_count                          ),
        .sts_dbe_count                          (sts_dbe_count                          ),
        .sts_corr_dropped_count                 (sts_corr_dropped_count                 ),
        .sts_err_addr                           (sts_err_addr                           ),
        .sts_corr_dropped_addr                  (sts_corr_dropped_addr                  ),
        .sts_mr_rdata_0                         (sts_mr_rdata_0                         ),
        .sts_mr_rdata_1                         (sts_mr_rdata_1                         ),
        .sts_mr_rdata_valid                     (sts_mr_rdata_valid                     ),
        .slave_ready                            (slave_mmr_ready                        ),
        .slave_address                          (slave_mmr_address                      ),
        .slave_write                            (slave_mmr_write                        ),
        .slave_read                             (slave_mmr_read                         ),
        .slave_burstcount                       (slave_mmr_burstcount                   ),
        .slave_begintransfer                    (slave_mmr_begintransfer                ),
        .slave_wr_data                          (slave_mmr_wr_data                      ),
        .slave_byte_enable                      ({CFG_MMR_BYTE_ENABLE_WIDTH{1'b1}}      ),
        .slave_rd_data                          (slave_mmr_rd_data                      ),
        .slave_rd_data_valid                    (slave_mmr_rd_data_valid                ),
        .master_ready                           (master_mmr_ready                       ),
        .master_address                         (master_mmr_address                     ),
        .master_write                           (master_mmr_write                       ),
        .master_read                            (master_mmr_read                        ),
        .master_burstcount                      (master_mmr_burstcount                  ),
        .master_begintransfer                   (master_mmr_begintransfer               ),
        .master_wr_data                         (master_mmr_wr_data                     ),
        .master_byte_enable                     (                                       ), 
        .master_rd_data                         (master_mmr_rd_data                     ),
        .master_rd_data_valid                   (master_mmr_rd_data_valid               )
    );

endmodule
`ifdef QUESTA_INTEL_OEM
`pragma questa_oem_00 "sfv4CgBD2gRw66FfSic/D/DxyUF4ju6abSGjNZTz+XJ5wNcp1RmzgamT61rscvjMkkNKCYCGE4Hkry++3eL2fSJkmOtrYLQextJ2AFr2kX/6sa63SwNG1Dg8CndZgqHpcPsbI8J/52/6EA/5eQJiUNmwpEDzzugi2WpUBRBy4gGrSJ7A8zUzUrkHlWNSHE1mVOTkuXrL/BUqA6hBwwkS7qZD/J3TRyAu6L9p+9tB0EAZQO90Dgd3nOG9fz0cZkTU/GwE4wVUkuFaV7A9pMioWVcKxYeem7Kcqtc06fudP6NbZe2IwH31SXPkNsqeSigvGVzTswSNsC4uM4HA/+WdW8tImjaW+juss32WEaDcClstCUamM5jZSOHuSKQMoOXRKtTyCM04ijGqdSj9/c4WuK62TdxiVtCsMpQPMfKBt6w5HIUgiw/45AVlX+Axx/JapLZgvS1P98v4FXC5aCr6WpPQu+5UJ+GwEKUsR0bLK+7L+uFMs902Xt2xLgMI4nsIsXj8A/1hwJmzGaCxqc001L5WWVHcyDJAMDMYaIJ2SoR3ZpPA1mIEe4x1t7kaAMsnjEb3IPcm1tC9eoo30iz8p1ZrwRgbbKUgO9RW0/R2tMRX7YmwR830bT2qTF8GnSdURFDcri5gwjFcfTHU3strIdfQ0scFoxIdtt0Jjuc3GYyq76855NGls2SysVvZ8UedXJ/S+em+xD4ohSQr7sG4omSg6cM0Zg1m9ONsuXzy6KW10hAaMYZoYp4heTHUcRh+0+XFjpuANa6bP5vUhUvv3vDvASJwpl7BoUb83uggBsf7qzYFALRmfY2PonCmgSPzxUXFIAL7J7hJ4UDqiwDwTXORiQVv77Qs8D0NW8HdSrVgqH2UJYlq8B3TNNqWkG55kOFEgtgrnfBz4fxUWENBJYrqqAlLWztraLos9kruMskrCkl64O85dYPnJDkTBJtHclGvVI3PG94SUWE9kBWEEdzAlOrLPDqnk0WAI7S8O3OVDi3NBnPP9liL7+PdnqVg"
`endif
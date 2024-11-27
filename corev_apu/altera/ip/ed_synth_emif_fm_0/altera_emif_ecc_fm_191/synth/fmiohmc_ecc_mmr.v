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

module fmiohmc_ecc_mmr #
    ( parameter
        CFG_MMR_ADDR_WIDTH                     = 10,
        CFG_MMR_DATA_WIDTH                     = 35,
        CFG_MMR_BYTE_ENABLE_WIDTH              = 4,
        CFG_MMR_BURSTCOUNT_WIDTH               = 2,
        
        CFG_DRAM_DATA_WIDTH                    = 0,
        CFG_LOCAL_DATA_WIDTH                   = 0,
        CFG_ADDR_WIDTH                         = 0,
        CFG_DATA_RATE                          = 0,
        CFG_ECC_IN_PROTOCOL                    = 0,
        CFG_WRPATH_PIPELINE_EN                 = 0,
        CFG_ENABLE_ECC                         = 0,
        CFG_ENABLE_DM                          = 0,
        CFG_ENABLE_RMW                         = 0,
        CFG_ENABLE_AUTO_CORR                   = 0,
        CFG_ECC_CODE_OVERWRITE                 = 0,
        CFG_GEN_SBE                            = 0,
        CFG_GEN_DBE                            = 0,
        CFG_ENABLE_INTR                        = 0,
        CFG_MASK_SBE_INTR                      = 0,
        CFG_MASK_DBE_INTR                      = 0,
        CFG_MASK_CORR_DROPPED_INTR             = 0,
        CFG_MASK_HMI_INTR                      = 0,
        CFG_CLR_INTR                           = 0,
        CFG_CLR_MR_RDATA                       = 0,
        
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
        ECC_MMR_READ_LATENCY                   = 2,
        
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
        ctl_reset_n,
        
        cfg_dram_data_width,
        cfg_local_data_width,
        cfg_addr_width,
        cfg_data_rate, 
        cfg_ecc_in_protocol,
        cfg_wrpath_pipeline_en,
        cfg_enable_ecc,
        cfg_enable_dm,
        cfg_enable_rmw,
        cfg_enable_auto_corr,
        cfg_ecc_code_overwrite,
        cfg_gen_sbe,
        cfg_gen_dbe,
        cfg_enable_intr,
        cfg_mask_sbe_intr,
        cfg_mask_dbe_intr,
        cfg_mask_corr_dropped_intr,
        cfg_mask_hmi_intr,
        cfg_clr_intr,
        cfg_clr_mr_rdata,
        
        sts_ecc_intr,
        sts_sbe_error,
        sts_dbe_error,
        sts_corr_dropped,
        sts_sbe_count,
        sts_dbe_count,
        sts_corr_dropped_count,
        sts_err_addr,
        sts_corr_dropped_addr,
        sts_mr_rdata_0,
        sts_mr_rdata_1,
        sts_mr_rdata_valid,
        
        slave_ready,
        slave_address,
        slave_write,
        slave_read,
        slave_burstcount,
        slave_begintransfer,
        slave_wr_data,
        slave_byte_enable,
        slave_rd_data,
        slave_rd_data_valid,
        
        master_ready,
        master_address,
        master_write,
        master_read,
        master_burstcount,
        master_begintransfer,
        master_wr_data,
        master_byte_enable,
        master_rd_data,
        master_rd_data_valid
    );

/*
    For an MMR read between the ECC core and HMC (for addresses less than 0x7F), 
    the following latency is incurred:
                  ______________          _                   ______________
    CMD   -----> |              | -----> | | -----> * -----> |              |
                 |              |        |_|                 |              |
                 |              |                            |              |
                 |      ECC     |         _                  |      HMC     |
    READ  <----- |              | <----- | | <----- * <----- | 3 or 4 cycle |
    DATA         |              |        |_|                 |   latency    |
                 |______________|                            |______________|

                                      HMC_MMR_IF    UFI
    Signal names:
        mmr_master_*              slave_*        master_*  

    In the above diagram, the UFI command and read paths do not have any latency delays.
    Typically, CFG_REGISTER_UFI_RDATA_PATH_NUM has 2 pipeline stages for Rev A boards
                                               or  0 pipeline stages for Rev B boards
    
    There is a general exception to UFI Latency for MMR interfaces - whereas RevA in this exceptional case
    does not incur an additional two cycle delay in either direction. However, for RevB2 boards with half rate
    and a core clock >= 400 MHz, the 2 cycle UFI latency is applied in each direction.

    The calculation for ECC_MMR_READ_LATENCY is performed in ip_ecc/ip_core_fm/main.tcl and is dependent
    on the IO Bank revision, whether or not rate conversion is on, and the core clock frequency.

    TODO: The IP can force the UFI latency via a diagnostic override (DIAG_EXTRA_CONFIGS: FORCE_L2_UFI=ON),
          thus changing the FILTER_MASTER_RD_DATA_VALID_LATENCY value. Changes will have to be made
          in the future to reflect that.

*/ 
localparam FILTER_MASTER_RD_DATA_VALID_LATENCY       = ECC_MMR_READ_LATENCY;

input                                                  ctl_clk;
input                                                  ctl_reset_n;

output [CFG_PORT_WIDTH_DRAM_DATA_WIDTH        - 1 : 0] cfg_dram_data_width;
output [CFG_PORT_WIDTH_LOCAL_DATA_WIDTH       - 1 : 0] cfg_local_data_width;
output [CFG_PORT_WIDTH_ADDR_WIDTH             - 1 : 0] cfg_addr_width;
output [CFG_PORT_WIDTH_DATA_RATE              - 1 : 0] cfg_data_rate;
output [CFG_PORT_WIDTH_ECC_IN_PROTOCOL        - 1 : 0] cfg_ecc_in_protocol;
output [CFG_PORT_WIDTH_WRPATH_PIPELINE_EN     - 1 : 0] cfg_wrpath_pipeline_en;
output [CFG_PORT_WIDTH_ENABLE_ECC             - 1 : 0] cfg_enable_ecc;
output [CFG_PORT_WIDTH_ENABLE_DM              - 1 : 0] cfg_enable_dm;
output [CFG_PORT_WIDTH_ENABLE_RMW             - 1 : 0] cfg_enable_rmw;
output [CFG_PORT_WIDTH_ENABLE_AUTO_CORR       - 1 : 0] cfg_enable_auto_corr;
output [CFG_PORT_WIDTH_ECC_CODE_OVERWRITE     - 1 : 0] cfg_ecc_code_overwrite;
output [CFG_PORT_WIDTH_GEN_SBE                - 1 : 0] cfg_gen_sbe;
output [CFG_PORT_WIDTH_GEN_DBE                - 1 : 0] cfg_gen_dbe;
output [CFG_PORT_WIDTH_ENABLE_INTR            - 1 : 0] cfg_enable_intr;
output [CFG_PORT_WIDTH_MASK_SBE_INTR          - 1 : 0] cfg_mask_sbe_intr;
output [CFG_PORT_WIDTH_MASK_DBE_INTR          - 1 : 0] cfg_mask_dbe_intr;
output [CFG_PORT_WIDTH_MASK_CORR_DROPPED_INTR - 1 : 0] cfg_mask_corr_dropped_intr;
output [CFG_PORT_WIDTH_MASK_HMI_INTR          - 1 : 0] cfg_mask_hmi_intr;
output [CFG_PORT_WIDTH_CLR_INTR               - 1 : 0] cfg_clr_intr;
output [CFG_PORT_WIDTH_CLR_MR_RDATA           - 1 : 0] cfg_clr_mr_rdata;

input  [STS_PORT_WIDTH_ECC_INTR               - 1 : 0] sts_ecc_intr;
input  [STS_PORT_WIDTH_SBE_ERROR              - 1 : 0] sts_sbe_error;
input  [STS_PORT_WIDTH_DBE_ERROR              - 1 : 0] sts_dbe_error;
input  [STS_PORT_WIDTH_CORR_DROPPED           - 1 : 0] sts_corr_dropped;
input  [STS_PORT_WIDTH_SBE_COUNT              - 1 : 0] sts_sbe_count;
input  [STS_PORT_WIDTH_DBE_COUNT              - 1 : 0] sts_dbe_count;
input  [STS_PORT_WIDTH_CORR_DROPPED_COUNT     - 1 : 0] sts_corr_dropped_count;
input  [STS_PORT_WIDTH_ERR_ADDR               - 1 : 0] sts_err_addr;
input  [STS_PORT_WIDTH_CORR_DROPPED_ADDR      - 1 : 0] sts_corr_dropped_addr;
input  [STS_PORT_WIDTH_MR_DATA                - 1 : 0] sts_mr_rdata_0;
input  [STS_PORT_WIDTH_MR_DATA                - 1 : 0] sts_mr_rdata_1;
input  [STS_PORT_WIDTH_MR_DATA_VALID          - 1 : 0] sts_mr_rdata_valid;

output                                                 slave_ready;
input  [CFG_MMR_ADDR_WIDTH                    - 1 : 0] slave_address;
input                                                  slave_write;
input                                                  slave_read;
input  [CFG_MMR_BURSTCOUNT_WIDTH              - 1 : 0] slave_burstcount;
input                                                  slave_begintransfer;
input  [CFG_MMR_DATA_WIDTH                    - 1 : 0] slave_wr_data;
input  [CFG_MMR_BYTE_ENABLE_WIDTH             - 1 : 0] slave_byte_enable;
output [CFG_MMR_DATA_WIDTH                    - 1 : 0] slave_rd_data;
output                                                 slave_rd_data_valid;

input                                                  master_ready;
output [CFG_MMR_ADDR_WIDTH                    - 1 : 0] master_address;
output                                                 master_write;
output                                                 master_read;
output [CFG_MMR_BURSTCOUNT_WIDTH              - 1 : 0] master_burstcount;
output                                                 master_begintransfer;
output [CFG_MMR_DATA_WIDTH                    - 1 : 0] master_wr_data;
output [CFG_MMR_BYTE_ENABLE_WIDTH             - 1 : 0] master_byte_enable;
input  [CFG_MMR_DATA_WIDTH                    - 1 : 0] master_rd_data;
input                                                  master_rd_data_valid;


reg  [CFG_PORT_WIDTH_WRPATH_PIPELINE_EN     - 1 : 0] reg_wrpath_pipeline_en;
reg  [CFG_PORT_WIDTH_ENABLE_ECC             - 1 : 0] reg_enable_ecc;
reg  [CFG_PORT_WIDTH_ENABLE_DM              - 1 : 0] reg_enable_dm;
reg  [CFG_PORT_WIDTH_ENABLE_RMW             - 1 : 0] reg_enable_rmw;
reg  [CFG_PORT_WIDTH_ENABLE_AUTO_CORR       - 1 : 0] reg_enable_auto_corr;
reg  [CFG_PORT_WIDTH_ECC_CODE_OVERWRITE     - 1 : 0] reg_ecc_code_overwrite;
reg  [CFG_PORT_WIDTH_GEN_SBE                - 1 : 0] reg_gen_sbe;
reg  [CFG_PORT_WIDTH_GEN_DBE                - 1 : 0] reg_gen_dbe;
reg  [CFG_PORT_WIDTH_ENABLE_INTR            - 1 : 0] reg_enable_intr;
reg  [CFG_PORT_WIDTH_MASK_SBE_INTR          - 1 : 0] reg_mask_sbe_intr;
reg  [CFG_PORT_WIDTH_MASK_DBE_INTR          - 1 : 0] reg_mask_dbe_intr;
reg  [CFG_PORT_WIDTH_MASK_CORR_DROPPED_INTR - 1 : 0] reg_mask_corr_dropped_intr;
reg  [CFG_PORT_WIDTH_MASK_HMI_INTR          - 1 : 0] reg_mask_hmi_intr;
reg  [CFG_PORT_WIDTH_CLR_INTR               - 1 : 0] reg_clr_intr;
reg  [CFG_PORT_WIDTH_CLR_MR_RDATA           - 1 : 0] reg_clr_mr_rdata;
reg  [STS_PORT_WIDTH_ECC_INTR               - 1 : 0] reg_ecc_intr;
reg  [STS_PORT_WIDTH_SBE_ERROR              - 1 : 0] reg_sbe_error;
reg  [STS_PORT_WIDTH_DBE_ERROR              - 1 : 0] reg_dbe_error;
reg  [STS_PORT_WIDTH_CORR_DROPPED           - 1 : 0] reg_corr_dropped;
reg  [STS_PORT_WIDTH_SBE_COUNT              - 1 : 0] reg_sbe_count;
reg  [STS_PORT_WIDTH_DBE_COUNT              - 1 : 0] reg_dbe_count;
reg  [STS_PORT_WIDTH_CORR_DROPPED_COUNT     - 1 : 0] reg_corr_dropped_count;
reg  [STS_PORT_WIDTH_ERR_ADDR               - 1 : 0] reg_err_addr;
reg  [STS_PORT_WIDTH_CORR_DROPPED_ADDR      - 1 : 0] reg_corr_dropped_addr;
reg  [STS_PORT_WIDTH_MR_DATA                - 1 : 0] reg_mr_rdata_0;
reg  [STS_PORT_WIDTH_MR_DATA                - 1 : 0] reg_mr_rdata_1;
reg  [STS_PORT_WIDTH_MR_DATA_VALID          - 1 : 0] reg_mr_rdata_valid;

wire                                                 slave_ready;
wire [CFG_MMR_DATA_WIDTH                    - 1 : 0] slave_rd_data;
wire                                                 slave_rd_data_valid;
wire [CFG_MMR_ADDR_WIDTH                    - 1 : 0] master_address;
wire                                                 master_write;
wire                                                 master_read;
wire [CFG_MMR_BURSTCOUNT_WIDTH              - 1 : 0] master_burstcount;
wire                                                 master_begintransfer;
wire [CFG_MMR_DATA_WIDTH                    - 1 : 0] master_wr_data;
wire [CFG_MMR_BYTE_ENABLE_WIDTH             - 1 : 0] master_byte_enable;
wire [CFG_MMR_DATA_WIDTH                    - 1 : 0] master_rd_data;

reg  [CFG_MMR_ADDR_WIDTH                    - 1 : 0] int_slave_address_count;
reg  [CFG_MMR_BURSTCOUNT_WIDTH              - 1 : 0] int_slave_burstcount_left;
reg                                                  int_slave_writing;

reg                                                  int_slave_ready;
reg  [CFG_MMR_ADDR_WIDTH                    - 1 : 0] int_slave_address;
reg                                                  int_slave_write;
reg                                                  int_slave_read;
reg  [CFG_MMR_DATA_WIDTH                    - 1 : 0] int_slave_rd_data;
reg                                                  int_slave_rd_data_valid;

reg                                                  filter_slave_rd_data_valid;
reg  [FILTER_MASTER_RD_DATA_VALID_LATENCY   - 1 : 0] filter_master_rd_data_valid;

always @ (posedge ctl_clk)
begin
    if (!ctl_reset_n)
    begin
        filter_slave_rd_data_valid  <= 1'b0;
        filter_master_rd_data_valid <= {FILTER_MASTER_RD_DATA_VALID_LATENCY{1'b0}};
    end
    else
    begin
        filter_slave_rd_data_valid  <= slave_ready & slave_read & !master_read;
        filter_master_rd_data_valid <= {filter_master_rd_data_valid[FILTER_MASTER_RD_DATA_VALID_LATENCY - 2 : 0], (master_ready & master_read)};
    end
end
assign slave_ready          = int_slave_ready & master_ready;
assign slave_rd_data        = (int_slave_rd_data_valid == 1'b1) ? int_slave_rd_data       : master_rd_data;
assign slave_rd_data_valid  = (int_slave_rd_data_valid == 1'b1) ? (int_slave_rd_data_valid & filter_slave_rd_data_valid) 
                                                                : (master_rd_data_valid & filter_master_rd_data_valid[FILTER_MASTER_RD_DATA_VALID_LATENCY - 1]);
assign master_address       = slave_address;
assign master_write         = slave_write && !(|slave_address [CFG_MMR_ADDR_WIDTH - 1 : 7]);
assign master_read          = slave_read  && !(|slave_address [CFG_MMR_ADDR_WIDTH - 1 : 7]);
assign master_burstcount    = slave_burstcount;
assign master_begintransfer = slave_begintransfer;
assign master_wr_data       = slave_wr_data;
assign master_byte_enable   = slave_byte_enable;

assign cfg_dram_data_width        = CFG_DRAM_DATA_WIDTH    [CFG_PORT_WIDTH_DRAM_DATA_WIDTH    - 1 : 0]; 
assign cfg_local_data_width       = CFG_LOCAL_DATA_WIDTH   [CFG_PORT_WIDTH_LOCAL_DATA_WIDTH   - 1 : 0]; 
assign cfg_addr_width             = CFG_ADDR_WIDTH         [CFG_PORT_WIDTH_ADDR_WIDTH         - 1 : 0]; 
assign cfg_data_rate              = CFG_DATA_RATE          [CFG_PORT_WIDTH_DATA_RATE          - 1 : 0]; 
assign cfg_ecc_in_protocol        = CFG_ECC_IN_PROTOCOL    [CFG_PORT_WIDTH_ECC_IN_PROTOCOL    - 1 : 0]; 
assign cfg_wrpath_pipeline_en     = CFG_WRPATH_PIPELINE_EN [CFG_PORT_WIDTH_WRPATH_PIPELINE_EN - 1 : 0]; 
assign cfg_enable_ecc             = CFG_ENABLE_ECC         [CFG_PORT_WIDTH_ENABLE_ECC         - 1 : 0]; 
assign cfg_enable_dm              = CFG_ENABLE_DM          [CFG_PORT_WIDTH_ENABLE_DM          - 1 : 0]; 
assign cfg_enable_rmw             = CFG_ENABLE_RMW         [CFG_PORT_WIDTH_ENABLE_RMW         - 1 : 0]; 
assign cfg_enable_auto_corr       = CFG_ENABLE_AUTO_CORR   [CFG_PORT_WIDTH_ENABLE_AUTO_CORR   - 1 : 0]; 
assign cfg_ecc_code_overwrite     = CFG_ECC_CODE_OVERWRITE [CFG_PORT_WIDTH_ECC_CODE_OVERWRITE - 1 : 0]; 
assign cfg_gen_sbe                = reg_gen_sbe;
assign cfg_gen_dbe                = reg_gen_dbe;
assign cfg_enable_intr            = CFG_ENABLE_INTR        [CFG_PORT_WIDTH_ENABLE_INTR        - 1 : 0]; 
assign cfg_mask_sbe_intr          = reg_mask_sbe_intr;
assign cfg_mask_dbe_intr          = reg_mask_dbe_intr;
assign cfg_mask_corr_dropped_intr = reg_mask_corr_dropped_intr;
assign cfg_mask_hmi_intr          = reg_mask_hmi_intr;
assign cfg_clr_intr               = reg_clr_intr;
assign cfg_clr_mr_rdata           = reg_clr_mr_rdata;

always @ (*)
begin
    int_slave_ready   =  (int_slave_burstcount_left == 0) ? 1'b1          :  int_slave_writing;
    int_slave_address =  (int_slave_burstcount_left == 0) ? slave_address :  int_slave_address_count;
    int_slave_write   = (                                   slave_write                       ) & master_ready;
    int_slave_read    = ((int_slave_burstcount_left == 0) ? slave_read    : ~int_slave_writing) & master_ready;
end

always @ (posedge ctl_clk)
begin
    if (!ctl_reset_n)
    begin
        int_slave_address_count   <= {CFG_MMR_ADDR_WIDTH{1'b0}};
        int_slave_burstcount_left <= {CFG_MMR_BURSTCOUNT_WIDTH{1'b0}};
        int_slave_writing         <= 1'b0;
    end
    else
    begin
        if (master_ready && (slave_read || slave_write) && slave_begintransfer && slave_burstcount > 1'b1) 
        begin
            int_slave_address_count   <= slave_address + 1'b1;
            int_slave_burstcount_left <= slave_burstcount - 1'b1;
            int_slave_writing         <= slave_write;
        end
        else if (int_slave_burstcount_left > 1'b1)
        begin
            if ((int_slave_writing && master_ready && slave_write) || !int_slave_writing)
            begin
                int_slave_address_count   <= int_slave_address_count + 1'b1;
                int_slave_burstcount_left <= int_slave_burstcount_left - 1'b1;
            end
        end
        else
        begin
            int_slave_address_count   <= {CFG_MMR_ADDR_WIDTH{1'b0}};
            int_slave_burstcount_left <= {CFG_MMR_BURSTCOUNT_WIDTH{1'b0}};
            int_slave_writing         <= 1'b0;
        end
    end
end

always @ (posedge ctl_clk)
begin
    if (!ctl_reset_n)
    begin
        reg_wrpath_pipeline_en     <= CFG_WRPATH_PIPELINE_EN     [CFG_PORT_WIDTH_WRPATH_PIPELINE_EN     - 1 : 0];
        reg_enable_ecc             <= CFG_ENABLE_ECC             [CFG_PORT_WIDTH_ENABLE_ECC             - 1 : 0];
        reg_enable_dm              <= CFG_ENABLE_DM              [CFG_PORT_WIDTH_ENABLE_DM              - 1 : 0];
        reg_enable_rmw             <= CFG_ENABLE_RMW             [CFG_PORT_WIDTH_ENABLE_RMW             - 1 : 0];
        reg_enable_auto_corr       <= CFG_ENABLE_AUTO_CORR       [CFG_PORT_WIDTH_ENABLE_AUTO_CORR       - 1 : 0];
        reg_ecc_code_overwrite     <= CFG_ECC_CODE_OVERWRITE     [CFG_PORT_WIDTH_ECC_CODE_OVERWRITE     - 1 : 0];
        reg_gen_sbe                <= CFG_GEN_SBE                [CFG_PORT_WIDTH_GEN_SBE                - 1 : 0];
        reg_gen_dbe                <= CFG_GEN_DBE                [CFG_PORT_WIDTH_GEN_DBE                - 1 : 0];
        reg_enable_intr            <= CFG_ENABLE_INTR            [CFG_PORT_WIDTH_ENABLE_INTR            - 1 : 0];
        reg_mask_sbe_intr          <= CFG_MASK_SBE_INTR          [CFG_PORT_WIDTH_MASK_SBE_INTR          - 1 : 0];
        reg_mask_dbe_intr          <= CFG_MASK_DBE_INTR          [CFG_PORT_WIDTH_MASK_DBE_INTR          - 1 : 0];
        reg_mask_corr_dropped_intr <= CFG_MASK_CORR_DROPPED_INTR [CFG_PORT_WIDTH_MASK_CORR_DROPPED_INTR - 1 : 0];
        reg_mask_hmi_intr          <= CFG_MASK_HMI_INTR          [CFG_PORT_WIDTH_MASK_HMI_INTR          - 1 : 0];
        reg_clr_intr               <= CFG_CLR_INTR               [CFG_PORT_WIDTH_CLR_INTR               - 1 : 0];
        reg_clr_mr_rdata           <= CFG_CLR_MR_RDATA           [CFG_PORT_WIDTH_CLR_MR_RDATA           - 1 : 0];
        reg_ecc_intr               <= {STS_PORT_WIDTH_ECC_INTR          {1'b0}};
        reg_sbe_error              <= {STS_PORT_WIDTH_SBE_ERROR         {1'b0}};
        reg_dbe_error              <= {STS_PORT_WIDTH_DBE_ERROR         {1'b0}};
        reg_corr_dropped           <= {STS_PORT_WIDTH_CORR_DROPPED      {1'b0}};
        reg_sbe_count              <= {STS_PORT_WIDTH_SBE_COUNT         {1'b0}};
        reg_dbe_count              <= {STS_PORT_WIDTH_DBE_COUNT         {1'b0}};
        reg_corr_dropped_count     <= {STS_PORT_WIDTH_CORR_DROPPED_COUNT{1'b0}};
        reg_err_addr               <= {STS_PORT_WIDTH_ERR_ADDR          {1'b0}};
        reg_corr_dropped_addr      <= {STS_PORT_WIDTH_CORR_DROPPED_ADDR {1'b0}};
        reg_mr_rdata_0             <= {STS_PORT_WIDTH_MR_DATA           {1'b0}};
        reg_mr_rdata_1             <= {STS_PORT_WIDTH_MR_DATA           {1'b0}};
        reg_mr_rdata_valid         <= {STS_PORT_WIDTH_MR_DATA_VALID     {1'b0}};
        
        int_slave_rd_data          <= {CFG_MMR_DATA_WIDTH               {1'b0}};
        int_slave_rd_data_valid    <= 1'b0;
    end
    else
    begin
        reg_ecc_intr               <= sts_ecc_intr;
        reg_sbe_error              <= sts_sbe_error;
        reg_dbe_error              <= sts_dbe_error;
        reg_corr_dropped           <= sts_corr_dropped;
        reg_sbe_count              <= sts_sbe_count;
        reg_dbe_count              <= sts_dbe_count;
        reg_corr_dropped_count     <= sts_corr_dropped_count;
        reg_err_addr               <= sts_err_addr;
        reg_corr_dropped_addr      <= sts_corr_dropped_addr;
        reg_mr_rdata_0             <= sts_mr_rdata_0;
        reg_mr_rdata_1             <= sts_mr_rdata_1;
        reg_mr_rdata_valid         <= sts_mr_rdata_valid;
        
        case (int_slave_address)
            10'h080 :
                begin
                    reg_clr_intr            <= 1'b0; 
                    reg_clr_mr_rdata        <= 1'b0; 
                    
                    if (int_slave_write)
                    begin
                        reg_wrpath_pipeline_en <= slave_wr_data [     10] & slave_byte_enable [1];
                        reg_ecc_code_overwrite <= slave_wr_data [      9] & slave_byte_enable [1];
                        reg_enable_auto_corr   <= slave_wr_data [      8] & slave_byte_enable [1];
                        reg_enable_rmw         <= slave_wr_data [      2] & slave_byte_enable [0];
                        reg_enable_dm          <= slave_wr_data [      1] & slave_byte_enable [0];
                        reg_enable_ecc         <= slave_wr_data [      0] & slave_byte_enable [0];
                    end
                    
                    if (int_slave_read)
                    begin
                        int_slave_rd_data       <=  {
                                                        {(CFG_MMR_DATA_WIDTH - 11){1'b0}},
                                                        reg_wrpath_pipeline_en           ,
                                                        reg_ecc_code_overwrite           ,
                                                        reg_enable_auto_corr             ,
                                                        cfg_ecc_in_protocol              , 
                                                        cfg_data_rate                    , 
                                                        reg_enable_rmw                   ,
                                                        reg_enable_dm                    ,
                                                        reg_enable_ecc                    
                                                    };
                        int_slave_rd_data_valid <= 1'b1;
                    end
                    else
                    begin
                       int_slave_rd_data_valid <= 1'b0;
                    end                    
                end
            10'h081 :
                begin
                    reg_clr_intr            <= 1'b0; 
                    reg_clr_mr_rdata        <= 1'b0; 
                    
                    
                    if (int_slave_read)
                    begin
                        int_slave_rd_data       <=  {
                                                        {(CFG_MMR_DATA_WIDTH - 22){1'b0}},
                                                        cfg_addr_width                   , 
                                                        cfg_local_data_width             , 
                                                        cfg_dram_data_width                
                                                    };
                        int_slave_rd_data_valid <= 1'b1;
                    end
                    else
                    begin
                       int_slave_rd_data_valid <= 1'b0;
                    end                    
                end
            10'h082 :
                begin
                    if (int_slave_write)
                    begin
                        reg_clr_mr_rdata           <= slave_wr_data [      8] & slave_byte_enable [1];
                        reg_clr_intr               <= slave_wr_data [      7] & slave_byte_enable [0];
                        reg_mask_hmi_intr          <= slave_wr_data [      6] & slave_byte_enable [0];
                        reg_mask_corr_dropped_intr <= slave_wr_data [      5] & slave_byte_enable [0];
                        reg_mask_dbe_intr          <= slave_wr_data [      4] & slave_byte_enable [0];
                        reg_mask_sbe_intr          <= slave_wr_data [      3] & slave_byte_enable [0];
                        reg_enable_intr            <= slave_wr_data [      2] & slave_byte_enable [0];
                        reg_gen_dbe                <= slave_wr_data [      1] & slave_byte_enable [0];
                        reg_gen_sbe                <= slave_wr_data [      0] & slave_byte_enable [0];
                    end
                    else
                    begin
                        reg_clr_intr            <= 1'b0; 
                        reg_clr_mr_rdata        <= 1'b0; 
                    end
                    
                    if (int_slave_read)
                    begin
                        int_slave_rd_data       <=  {
                                                        {(CFG_MMR_DATA_WIDTH -  9){1'b0}},
                                                        reg_clr_mr_rdata                 ,
                                                        reg_clr_intr                     ,
                                                        reg_mask_hmi_intr                ,
                                                        reg_mask_corr_dropped_intr       ,
                                                        reg_mask_dbe_intr                ,
                                                        reg_mask_sbe_intr                ,
                                                        reg_enable_intr                  ,
                                                        reg_gen_dbe                      ,
                                                        reg_gen_sbe                      
                                                    };
                        int_slave_rd_data_valid <= 1'b1;
                    end
                    else
                    begin
                       int_slave_rd_data_valid <= 1'b0;
                    end                    
                end
            10'h090 :
                begin
                    reg_clr_intr            <= 1'b0; 
                    reg_clr_mr_rdata        <= 1'b0; 
                    
                    if (int_slave_read)
                    begin
                        int_slave_rd_data       <=  {
                                                        {(CFG_MMR_DATA_WIDTH -  16){1'b0}},
                                                        reg_corr_dropped_count           ,
                                                        reg_dbe_count                    ,
                                                        reg_sbe_count                    ,
                                                        reg_corr_dropped                 ,
                                                        reg_dbe_error                    ,
                                                        reg_sbe_error                    ,
                                                        reg_ecc_intr                     
                                                    };
                        int_slave_rd_data_valid <= 1'b1;
                    end
                    else
                    begin
                       int_slave_rd_data_valid <= 1'b0;
                    end                    
                end
            10'h091 :
                begin
                    reg_clr_intr            <= 1'b0; 
                    reg_clr_mr_rdata        <= 1'b0; 
                    
                    if (int_slave_read)
                    begin
                        int_slave_rd_data       <=  {
                                                        reg_err_addr [31 : 0]
                                                    };
                        int_slave_rd_data_valid <= 1'b1;
                    end
                    else
                    begin
                       int_slave_rd_data_valid <= 1'b0;
                    end                    
                end
            10'h092 :
                begin
                    reg_clr_intr            <= 1'b0; 
                    reg_clr_mr_rdata        <= 1'b0; 
                    
                    if (int_slave_read)
                    begin
                        int_slave_rd_data       <=  {
                                                        reg_corr_dropped_addr [31 : 0]
                                                    };
                        int_slave_rd_data_valid <= 1'b1;
                    end
		    else
		    begin
		    	int_slave_rd_data_valid <= 1'b0;
		    end
                end
            10'h093 :
                begin
                    reg_clr_intr            <= 1'b0; 
                    reg_clr_mr_rdata        <= 1'b0; 
                    
                    if (int_slave_read)
                    begin
                        int_slave_rd_data       <=  {
                                                        {{(32 - (STS_PORT_WIDTH_ERR_ADDR - 32)){1'b0}}, reg_err_addr [STS_PORT_WIDTH_ERR_ADDR - 1 : 32]}
                                                    };
                        int_slave_rd_data_valid <= 1'b1;
                    end
		    else
		    begin
		    	int_slave_rd_data_valid <= 1'b0;
		    end
                end
            10'h094 :
                begin
                    reg_clr_intr            <= 1'b0; 
                    reg_clr_mr_rdata        <= 1'b0; 
                    
                    if (int_slave_read)
                    begin
                        int_slave_rd_data       <=  {
                                                        {{(32 - (STS_PORT_WIDTH_CORR_DROPPED_ADDR - 32)){1'b0}}, reg_corr_dropped_addr [STS_PORT_WIDTH_CORR_DROPPED_ADDR - 1 : 32]}
                                                    };
                        int_slave_rd_data_valid <= 1'b1;
                    end
		    else
		    begin
		    	int_slave_rd_data_valid <= 1'b0;
		    end
                end
            default :
                begin
                    reg_clr_intr            <= 1'b0; 
                    reg_clr_mr_rdata        <= 1'b0; 
                    
                    int_slave_rd_data       <= {CFG_MMR_DATA_WIDTH{1'b0}};
                    
                    if (int_slave_read)
                    begin
                        int_slave_rd_data_valid <= 1'b1;
                    end
                    else
                    begin
                        int_slave_rd_data_valid <= 1'b0;
                    end
                end
        endcase
    end
end

endmodule
`ifdef QUESTA_INTEL_OEM
`pragma questa_oem_00 "sfv4CgBD2gRw66FfSic/D/DxyUF4ju6abSGjNZTz+XJ5wNcp1RmzgamT61rscvjMkkNKCYCGE4Hkry++3eL2fSJkmOtrYLQextJ2AFr2kX/6sa63SwNG1Dg8CndZgqHpcPsbI8J/52/6EA/5eQJiUNmwpEDzzugi2WpUBRBy4gGrSJ7A8zUzUrkHlWNSHE1mVOTkuXrL/BUqA6hBwwkS7qZD/J3TRyAu6L9p+9tB0EC6BZU03E9XujYoOegoms/HKoZkTgEKH+H+1LaGQuI02/rKOrWOgIvS5S+SrJ/ns80Ht5Z659wxkjh80w1/sxXKGZgBW0GqFao4/FnSgRFLMpxvu2+d+Pl8BNjdbnA+fO5lry8cxEU8HhS77JzcyxvUSVXEk5FkmWTQpqQxKFUkn6uN6waeMLrkhPc7/orrbU0Z3bu66Ny3rAxrhcWwq4BLOw+PHRFz48U7MDx8QswunTH+nnmnOwIJ53au0ZTtJnhrWmv/DWeQuks9rwDbSSFZgU0XcaIviIBWnT54FnF658QbFAma8bFSzMBiDhacVGvwQeTpC7Sh59R9xrbOaQjnhwKfJYbGV2cA53IDjG65Onul0WPKI8CEB9B07KMfAGo4fQb7pGKAk/oOVkUAWFbiU8UegA8ri5XdEd6nfjy8DQvBGE2tX6zDTmUrb2arP6Fpi+f7Z3vyL2y3hHOGPByOCu/4YiLY/YpDIFqIB8UqUVVRJbESya0YZpLEJSejeDPTSNAUUqotTuH5MzOephIFr/LUJJXGY1dtgelEz0XerNl20372JT9y0GTlDN0cVO5SwMfQg0YgQrdzTik77nAMRkk1sy3X3N7GfZIsHejmERX27XF/ch+CfaG73mVaMqI6PQGuS0nDnxOR0YIv4owDVb5Bk5lklFkBRgwl5SPBokoJYmSc6MThUNj8qoo5IQR4omzKgVAPtu1J/9QPT4nNXQ/G6PZJc5H0nKQLeRtiUxlsFaSkdyWaqEunSZTwGSDqhsydSIeWtdEEFPjt09QY"
`endif
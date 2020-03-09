// Copyright (c) 2019 ETH Zurich, University of Bologna
//
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Simple standalone synthesis bench for axi_riscv_atomics
module axi_riscv_atomics_synth #(
    /// AXI Parameters
    parameter integer AXI_ADDR_WIDTH = 64,
    parameter integer AXI_DATA_WIDTH = 64,
    parameter integer AXI_ID_WIDTH = 4,
    parameter integer AXI_USER_WIDTH = 0,
    /// Maximum number of AXI bursts outstanding at the same time
    parameter integer AXI_MAX_WRITE_TXNS = 4,
    // Word width of the widest RISC-V processor that can issue requests to this module.
    // 32 for RV32; 64 for RV64, where both 32-bit (.W suffix) and 64-bit (.D suffix) AMOs are
    // supported if `aw_strb` is set correctly.
    parameter integer RISCV_WORD_WIDTH = 64,
    /// Derived Parameters (do NOT change manually!)
    localparam integer AXI_STRB_WIDTH = AXI_DATA_WIDTH / 8
) (
    input                          clk_i,
    input                          rst_ni,

    /// Slave Interface
    input   [AXI_ADDR_WIDTH-1:0]   slv_aw_addr_i,
    input   [2:0]                  slv_aw_prot_i,
    input   [3:0]                  slv_aw_region_i,
    input   [5:0]                  slv_aw_atop_i,
    input   [7:0]                  slv_aw_len_i,
    input   [2:0]                  slv_aw_size_i,
    input   [1:0]                  slv_aw_burst_i,
    input                          slv_aw_lock_i,
    input   [3:0]                  slv_aw_cache_i,
    input   [3:0]                  slv_aw_qos_i,
    input   [AXI_ID_WIDTH-1:0]     slv_aw_id_i,
    input   [AXI_USER_WIDTH-1:0]   slv_aw_user_i,
    output                         slv_aw_ready_o,
    input                          slv_aw_valid_i,

    input   [AXI_ADDR_WIDTH-1:0]   slv_ar_addr_i,
    input   [2:0]                  slv_ar_prot_i,
    input   [3:0]                  slv_ar_region_i,
    input   [7:0]                  slv_ar_len_i,
    input   [2:0]                  slv_ar_size_i,
    input   [1:0]                  slv_ar_burst_i,
    input                          slv_ar_lock_i,
    input   [3:0]                  slv_ar_cache_i,
    input   [3:0]                  slv_ar_qos_i,
    input   [AXI_ID_WIDTH-1:0]     slv_ar_id_i,
    input   [AXI_USER_WIDTH-1:0]   slv_ar_user_i,
    output                         slv_ar_ready_o,
    input                          slv_ar_valid_i,

    input   [AXI_DATA_WIDTH-1:0]   slv_w_data_i,
    input   [AXI_STRB_WIDTH-1:0]   slv_w_strb_i,
    input   [AXI_USER_WIDTH-1:0]   slv_w_user_i,
    input                          slv_w_last_i,
    output                         slv_w_ready_o,
    input                          slv_w_valid_i,

    output  [AXI_DATA_WIDTH-1:0]   slv_r_data_o,
    output  [1:0]                  slv_r_resp_o,
    output                         slv_r_last_o,
    output  [AXI_ID_WIDTH-1:0]     slv_r_id_o,
    output  [AXI_USER_WIDTH-1:0]   slv_r_user_o,
    input                          slv_r_ready_i,
    output                         slv_r_valid_o,

    output  [1:0]                  slv_b_resp_o,
    output  [AXI_ID_WIDTH-1:0]     slv_b_id_o,
    output  [AXI_USER_WIDTH-1:0]   slv_b_user_o,
    input                          slv_b_ready_i,
    output                         slv_b_valid_o,

    /// Master Interface
    output  [AXI_ADDR_WIDTH-1:0]   mst_aw_addr_o,
    output  [2:0]                  mst_aw_prot_o,
    output  [3:0]                  mst_aw_region_o,
    output  [5:0]                  mst_aw_atop_o,
    output  [7:0]                  mst_aw_len_o,
    output  [2:0]                  mst_aw_size_o,
    output  [1:0]                  mst_aw_burst_o,
    output                         mst_aw_lock_o,
    output  [3:0]                  mst_aw_cache_o,
    output  [3:0]                  mst_aw_qos_o,
    output  [AXI_ID_WIDTH-1:0]     mst_aw_id_o,
    output  [AXI_USER_WIDTH-1:0]   mst_aw_user_o,
    input                          mst_aw_ready_i,
    output                         mst_aw_valid_o,

    output  [AXI_ADDR_WIDTH-1:0]   mst_ar_addr_o,
    output  [2:0]                  mst_ar_prot_o,
    output  [3:0]                  mst_ar_region_o,
    output  [7:0]                  mst_ar_len_o,
    output  [2:0]                  mst_ar_size_o,
    output  [1:0]                  mst_ar_burst_o,
    output                         mst_ar_lock_o,
    output  [3:0]                  mst_ar_cache_o,
    output  [3:0]                  mst_ar_qos_o,
    output  [AXI_ID_WIDTH-1:0]     mst_ar_id_o,
    output  [AXI_USER_WIDTH-1:0]   mst_ar_user_o,
    input                          mst_ar_ready_i,
    output                         mst_ar_valid_o,

    output  [AXI_DATA_WIDTH-1:0]   mst_w_data_o,
    output  [AXI_STRB_WIDTH-1:0]   mst_w_strb_o,
    output  [AXI_USER_WIDTH-1:0]   mst_w_user_o,
    output                         mst_w_last_o,
    input                          mst_w_ready_i,
    output                         mst_w_valid_o,

    input   [AXI_DATA_WIDTH-1:0]   mst_r_data_i,
    input   [1:0]                  mst_r_resp_i,
    input                          mst_r_last_i,
    input   [AXI_ID_WIDTH-1:0]     mst_r_id_i,
    input   [AXI_USER_WIDTH-1:0]   mst_r_user_i,
    output                         mst_r_ready_o,
    input                          mst_r_valid_i,

    input   [1:0]                  mst_b_resp_i,
    input   [AXI_ID_WIDTH-1:0]     mst_b_id_i,
    input   [AXI_USER_WIDTH-1:0]   mst_b_user_i,
    output                         mst_b_ready_o,
    input                          mst_b_valid_i
);

    axi_riscv_atomics #(
        .AXI_ADDR_WIDTH     (AXI_ADDR_WIDTH),
        .AXI_DATA_WIDTH     (AXI_DATA_WIDTH),
        .AXI_ID_WIDTH       (AXI_ID_WIDTH),
        .AXI_USER_WIDTH     (AXI_USER_WIDTH),
        .AXI_MAX_WRITE_TXNS (AXI_MAX_WRITE_TXNS),
        .RISCV_WORD_WIDTH   (RISCV_WORD_WIDTH)
    ) i_axi_riscv_atomics (
        .clk_i(clk_i),
        .rst_ni(rst_ni),

        /// Slave Interface
        .slv_aw_addr_i(slv_aw_addr_i),
        .slv_aw_prot_i(slv_aw_prot_i),
        .slv_aw_region_i(slv_aw_region_i),
        .slv_aw_atop_i(slv_aw_atop_i),
        .slv_aw_len_i(slv_aw_len_i),
        .slv_aw_size_i(slv_aw_size_i),
        .slv_aw_burst_i(slv_aw_burst_i),
        .slv_aw_lock_i(slv_aw_lock_i),
        .slv_aw_cache_i(slv_aw_cache_i),
        .slv_aw_qos_i(slv_aw_qos_i),
        .slv_aw_id_i(slv_aw_id_i),
        .slv_aw_user_i(slv_aw_user_i),
        .slv_aw_ready_o(slv_aw_ready_o),
        .slv_aw_valid_i(slv_aw_valid_i),

        .slv_ar_addr_i(slv_ar_addr_i),
        .slv_ar_prot_i(slv_ar_prot_i),
        .slv_ar_region_i(slv_ar_region_i),
        .slv_ar_len_i(slv_ar_len_i),
        .slv_ar_size_i(slv_ar_size_i),
        .slv_ar_burst_i(slv_ar_burst_i),
        .slv_ar_lock_i(slv_ar_lock_i),
        .slv_ar_cache_i(slv_ar_cache_i),
        .slv_ar_qos_i(slv_ar_qos_i),
        .slv_ar_id_i(slv_ar_id_i),
        .slv_ar_user_i(slv_ar_user_i),
        .slv_ar_ready_o(slv_ar_ready_o),
        .slv_ar_valid_i(slv_ar_valid_i),

        .slv_w_data_i(slv_w_data_i),
        .slv_w_strb_i(slv_w_strb_i),
        .slv_w_user_i(slv_w_user_i),
        .slv_w_last_i(slv_w_last_i),
        .slv_w_ready_o(slv_w_ready_o),
        .slv_w_valid_i(slv_w_valid_i),

        .slv_r_data_o(slv_r_data_o),
        .slv_r_resp_o(slv_r_resp_o),
        .slv_r_last_o(slv_r_last_o),
        .slv_r_id_o(slv_r_id_o),
        .slv_r_user_o(slv_r_user_o),
        .slv_r_ready_i(slv_r_ready_i),
        .slv_r_valid_o(slv_r_valid_o),

        .slv_b_resp_o(slv_b_resp_o),
        .slv_b_id_o(slv_b_id_o),
        .slv_b_user_o(slv_b_user_o),
        .slv_b_ready_i(slv_b_ready_i),
        .slv_b_valid_o(slv_b_valid_o),

        /// Master Interface
        .mst_aw_addr_o(mst_aw_addr_o),
        .mst_aw_prot_o(mst_aw_prot_o),
        .mst_aw_region_o(mst_aw_region_o),
        .mst_aw_atop_o(mst_aw_atop_o),
        .mst_aw_len_o(mst_aw_len_o),
        .mst_aw_size_o(mst_aw_size_o),
        .mst_aw_burst_o(mst_aw_burst_o),
        .mst_aw_lock_o(mst_aw_lock_o),
        .mst_aw_cache_o(mst_aw_cache_o),
        .mst_aw_qos_o(mst_aw_qos_o),
        .mst_aw_id_o(mst_aw_id_o),
        .mst_aw_user_o(mst_aw_user_o),
        .mst_aw_ready_i(mst_aw_ready_i),
        .mst_aw_valid_o(mst_aw_valid_o),

        .mst_ar_addr_o(mst_ar_addr_o),
        .mst_ar_prot_o(mst_ar_prot_o),
        .mst_ar_region_o(mst_ar_region_o),
        .mst_ar_len_o(mst_ar_len_o),
        .mst_ar_size_o(mst_ar_size_o),
        .mst_ar_burst_o(mst_ar_burst_o),
        .mst_ar_lock_o(mst_ar_lock_o),
        .mst_ar_cache_o(mst_ar_cache_o),
        .mst_ar_qos_o(mst_ar_qos_o),
        .mst_ar_id_o(mst_ar_id_o),
        .mst_ar_user_o(mst_ar_user_o),
        .mst_ar_ready_i(mst_ar_ready_i),
        .mst_ar_valid_o(mst_ar_valid_o),

        .mst_w_data_o(mst_w_data_o),
        .mst_w_strb_o(mst_w_strb_o),
        .mst_w_user_o(mst_w_user_o),
        .mst_w_last_o(mst_w_last_o),
        .mst_w_ready_i(mst_w_ready_i),
        .mst_w_valid_o(mst_w_valid_o),

        .mst_r_data_i(mst_r_data_i),
        .mst_r_resp_i(mst_r_resp_i),
        .mst_r_last_i(mst_r_last_i),
        .mst_r_id_i(mst_r_id_i),
        .mst_r_user_i(mst_r_user_i),
        .mst_r_ready_o(mst_r_ready_o),
        .mst_r_valid_i(mst_r_valid_i),

        .mst_b_resp_i(mst_b_resp_i),
        .mst_b_id_i(mst_b_id_i),
        .mst_b_user_i(mst_b_user_i),
        .mst_b_ready_o(mst_b_ready_o),
        .mst_b_valid_i(mst_b_valid_i)
    );

endmodule

// Copyright (c) 2018 ETH Zurich, University of Bologna
//
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Wrapper for the AXI RISC-V Atomics Adapter that exposes AXI SystemVerilog interfaces.
//
// See the header of `axi_riscv_atomics` for a description.
//
// Maintainer: Andreas Kurth <akurth@iis.ee.ethz.ch>

module axi_riscv_atomics_wrap #(
    /// AXI Parameters
    parameter int unsigned AXI_ADDR_WIDTH = 0,
    parameter int unsigned AXI_DATA_WIDTH = 0,
    parameter int unsigned AXI_ID_WIDTH = 0,
    parameter int unsigned AXI_USER_WIDTH = 0,
    /// Maximum number of AXI bursts outstanding at the same time
    parameter int unsigned AXI_MAX_WRITE_TXNS = 0,
    // Word width of the widest RISC-V processor that can issue requests to this module.
    // 32 for RV32; 64 for RV64, where both 32-bit (.W suffix) and 64-bit (.D suffix) AMOs are
    // supported if `aw_strb` is set correctly.
    parameter int unsigned RISCV_WORD_WIDTH = 0,
    /// Derived Parameters (do NOT change manually!)
    localparam int unsigned AXI_STRB_WIDTH = AXI_DATA_WIDTH / 8
) (
    input  logic    clk_i,
    input  logic    rst_ni,
    AXI_BUS.Master  mst,
    AXI_BUS.Slave   slv
);

    axi_riscv_atomics #(
        .AXI_ADDR_WIDTH     (AXI_ADDR_WIDTH),
        .AXI_DATA_WIDTH     (AXI_DATA_WIDTH),
        .AXI_ID_WIDTH       (AXI_ID_WIDTH),
        .AXI_USER_WIDTH     (AXI_USER_WIDTH),
        .AXI_MAX_WRITE_TXNS (AXI_MAX_WRITE_TXNS),
        .RISCV_WORD_WIDTH   (RISCV_WORD_WIDTH)
    ) i_atomics (
        .clk_i           ( clk_i         ),
        .rst_ni          ( rst_ni        ),
        .slv_aw_addr_i   ( slv.aw_addr   ),
        .slv_aw_prot_i   ( slv.aw_prot   ),
        .slv_aw_region_i ( slv.aw_region ),
        .slv_aw_atop_i   ( slv.aw_atop   ),
        .slv_aw_len_i    ( slv.aw_len    ),
        .slv_aw_size_i   ( slv.aw_size   ),
        .slv_aw_burst_i  ( slv.aw_burst  ),
        .slv_aw_lock_i   ( slv.aw_lock   ),
        .slv_aw_cache_i  ( slv.aw_cache  ),
        .slv_aw_qos_i    ( slv.aw_qos    ),
        .slv_aw_id_i     ( slv.aw_id     ),
        .slv_aw_user_i   ( slv.aw_user   ),
        .slv_aw_ready_o  ( slv.aw_ready  ),
        .slv_aw_valid_i  ( slv.aw_valid  ),
        .slv_ar_addr_i   ( slv.ar_addr   ),
        .slv_ar_prot_i   ( slv.ar_prot   ),
        .slv_ar_region_i ( slv.ar_region ),
        .slv_ar_len_i    ( slv.ar_len    ),
        .slv_ar_size_i   ( slv.ar_size   ),
        .slv_ar_burst_i  ( slv.ar_burst  ),
        .slv_ar_lock_i   ( slv.ar_lock   ),
        .slv_ar_cache_i  ( slv.ar_cache  ),
        .slv_ar_qos_i    ( slv.ar_qos    ),
        .slv_ar_id_i     ( slv.ar_id     ),
        .slv_ar_user_i   ( slv.ar_user   ),
        .slv_ar_ready_o  ( slv.ar_ready  ),
        .slv_ar_valid_i  ( slv.ar_valid  ),
        .slv_w_data_i    ( slv.w_data    ),
        .slv_w_strb_i    ( slv.w_strb    ),
        .slv_w_user_i    ( slv.w_user    ),
        .slv_w_last_i    ( slv.w_last    ),
        .slv_w_ready_o   ( slv.w_ready   ),
        .slv_w_valid_i   ( slv.w_valid   ),
        .slv_r_data_o    ( slv.r_data    ),
        .slv_r_resp_o    ( slv.r_resp    ),
        .slv_r_last_o    ( slv.r_last    ),
        .slv_r_id_o      ( slv.r_id      ),
        .slv_r_user_o    ( slv.r_user    ),
        .slv_r_ready_i   ( slv.r_ready   ),
        .slv_r_valid_o   ( slv.r_valid   ),
        .slv_b_resp_o    ( slv.b_resp    ),
        .slv_b_id_o      ( slv.b_id      ),
        .slv_b_user_o    ( slv.b_user    ),
        .slv_b_ready_i   ( slv.b_ready   ),
        .slv_b_valid_o   ( slv.b_valid   ),
        .mst_aw_addr_o   ( mst.aw_addr   ),
        .mst_aw_prot_o   ( mst.aw_prot   ),
        .mst_aw_region_o ( mst.aw_region ),
        .mst_aw_atop_o   ( mst.aw_atop   ),
        .mst_aw_len_o    ( mst.aw_len    ),
        .mst_aw_size_o   ( mst.aw_size   ),
        .mst_aw_burst_o  ( mst.aw_burst  ),
        .mst_aw_lock_o   ( mst.aw_lock   ),
        .mst_aw_cache_o  ( mst.aw_cache  ),
        .mst_aw_qos_o    ( mst.aw_qos    ),
        .mst_aw_id_o     ( mst.aw_id     ),
        .mst_aw_user_o   ( mst.aw_user   ),
        .mst_aw_ready_i  ( mst.aw_ready  ),
        .mst_aw_valid_o  ( mst.aw_valid  ),
        .mst_ar_addr_o   ( mst.ar_addr   ),
        .mst_ar_prot_o   ( mst.ar_prot   ),
        .mst_ar_region_o ( mst.ar_region ),
        .mst_ar_len_o    ( mst.ar_len    ),
        .mst_ar_size_o   ( mst.ar_size   ),
        .mst_ar_burst_o  ( mst.ar_burst  ),
        .mst_ar_lock_o   ( mst.ar_lock   ),
        .mst_ar_cache_o  ( mst.ar_cache  ),
        .mst_ar_qos_o    ( mst.ar_qos    ),
        .mst_ar_id_o     ( mst.ar_id     ),
        .mst_ar_user_o   ( mst.ar_user   ),
        .mst_ar_ready_i  ( mst.ar_ready  ),
        .mst_ar_valid_o  ( mst.ar_valid  ),
        .mst_w_data_o    ( mst.w_data    ),
        .mst_w_strb_o    ( mst.w_strb    ),
        .mst_w_user_o    ( mst.w_user    ),
        .mst_w_last_o    ( mst.w_last    ),
        .mst_w_ready_i   ( mst.w_ready   ),
        .mst_w_valid_o   ( mst.w_valid   ),
        .mst_r_data_i    ( mst.r_data    ),
        .mst_r_resp_i    ( mst.r_resp    ),
        .mst_r_last_i    ( mst.r_last    ),
        .mst_r_id_i      ( mst.r_id      ),
        .mst_r_user_i    ( mst.r_user    ),
        .mst_r_ready_o   ( mst.r_ready   ),
        .mst_r_valid_i   ( mst.r_valid   ),
        .mst_b_resp_i    ( mst.b_resp    ),
        .mst_b_id_i      ( mst.b_id      ),
        .mst_b_user_i    ( mst.b_user    ),
        .mst_b_ready_o   ( mst.b_ready   ),
        .mst_b_valid_i   ( mst.b_valid   )
    );

    // Validate parameters.
// pragma translate_off
`ifndef VERILATOR
    initial begin: validate_params
        assert (AXI_STRB_WIDTH == AXI_DATA_WIDTH/8)
            else $fatal(1, "AXI_STRB_WIDTH must equal AXI_DATA_WIDTH/8!");
    end
`endif
// pragma translate_on

endmodule

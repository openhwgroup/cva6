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

// AXI RISC-V LR/SC Adapter
//
// This adapter adds support for AXI4 exclusive accesses to a slave that natively does not support
// exclusive accesses.  It is to be placed between that slave and the upstream master port, so that
// the `mst` port of this module drives the slave and the `slv` port of this module is driven by
// the upstream master.
//
// Exclusive accesses are only enabled for a range of addresses specified through parameters.  All
// addresses within that range are guaranteed to fulfill the constraints described in A7.2 of the
// AXI4 standard, both for normal and exclusive memory accesses.  Addresses outside that range
// behave like a slave that does not support exclusive memory accesses (see AXI4, A7.2.5).
//
// Limitations:
//  -   The adapter allows at most one read and one write access to be outstanding at any given
//      time.
//  -   The adapter does not support bursts in exclusive accessing.  Only single words can be
//      reserved.
//
// Maintainer: Andreas Kurth <akurth@iis.ee.ethz.ch>

module axi_riscv_lrsc #(
    /// Exclusively-accessible address range (closed interval from ADDR_BEGIN to ADDR_END)
    parameter longint unsigned ADDR_BEGIN = 0,
    parameter longint unsigned ADDR_END = 0,
    /// AXI Parameters
    parameter int unsigned AXI_ADDR_WIDTH = 0,
    parameter int unsigned AXI_DATA_WIDTH = 0,
    parameter int unsigned AXI_ID_WIDTH = 0,
    parameter int unsigned AXI_USER_WIDTH = 0,
    /// Derived Parameters (do NOT change manually!)
    localparam int unsigned AXI_STRB_WIDTH = AXI_DATA_WIDTH / 8
) (
    input logic                         clk_i,
    input logic                         rst_ni,

    /// Slave Interface
    input  logic [AXI_ADDR_WIDTH-1:0]   slv_aw_addr_i,
    input  logic [2:0]                  slv_aw_prot_i,
    input  logic [3:0]                  slv_aw_region_i,
    input  logic [5:0]                  slv_aw_atop_i,
    input  logic [7:0]                  slv_aw_len_i,
    input  logic [2:0]                  slv_aw_size_i,
    input  logic [1:0]                  slv_aw_burst_i,
    input  logic                        slv_aw_lock_i,
    input  logic [3:0]                  slv_aw_cache_i,
    input  logic [3:0]                  slv_aw_qos_i,
    input  logic [AXI_ID_WIDTH-1:0]     slv_aw_id_i,
    input  logic [AXI_USER_WIDTH-1:0]   slv_aw_user_i,
    output logic                        slv_aw_ready_o,
    input  logic                        slv_aw_valid_i,

    input  logic [AXI_ADDR_WIDTH-1:0]   slv_ar_addr_i,
    input  logic [2:0]                  slv_ar_prot_i,
    input  logic [3:0]                  slv_ar_region_i,
    input  logic [7:0]                  slv_ar_len_i,
    input  logic [2:0]                  slv_ar_size_i,
    input  logic [1:0]                  slv_ar_burst_i,
    input  logic                        slv_ar_lock_i,
    input  logic [3:0]                  slv_ar_cache_i,
    input  logic [3:0]                  slv_ar_qos_i,
    input  logic [AXI_ID_WIDTH-1:0]     slv_ar_id_i,
    input  logic [AXI_USER_WIDTH-1:0]   slv_ar_user_i,
    output logic                        slv_ar_ready_o,
    input  logic                        slv_ar_valid_i,

    input  logic [AXI_DATA_WIDTH-1:0]   slv_w_data_i,
    input  logic [AXI_STRB_WIDTH-1:0]   slv_w_strb_i,
    input  logic [AXI_USER_WIDTH-1:0]   slv_w_user_i,
    input  logic                        slv_w_last_i,
    output logic                        slv_w_ready_o,
    input  logic                        slv_w_valid_i,

    output logic [AXI_DATA_WIDTH-1:0]   slv_r_data_o,
    output logic [1:0]                  slv_r_resp_o,
    output logic                        slv_r_last_o,
    output logic [AXI_ID_WIDTH-1:0]     slv_r_id_o,
    output logic [AXI_USER_WIDTH-1:0]   slv_r_user_o,
    input  logic                        slv_r_ready_i,
    output logic                        slv_r_valid_o,

    output logic [1:0]                  slv_b_resp_o,
    output logic [AXI_ID_WIDTH-1:0]     slv_b_id_o,
    output logic [AXI_USER_WIDTH-1:0]   slv_b_user_o,
    input  logic                        slv_b_ready_i,
    output logic                        slv_b_valid_o,

    /// Master Interface
    output logic [AXI_ADDR_WIDTH-1:0]   mst_aw_addr_o,
    output logic [2:0]                  mst_aw_prot_o,
    output logic [3:0]                  mst_aw_region_o,
    output logic [5:0]                  mst_aw_atop_o,
    output logic [7:0]                  mst_aw_len_o,
    output logic [2:0]                  mst_aw_size_o,
    output logic [1:0]                  mst_aw_burst_o,
    output logic                        mst_aw_lock_o,
    output logic [3:0]                  mst_aw_cache_o,
    output logic [3:0]                  mst_aw_qos_o,
    output logic [AXI_ID_WIDTH-1:0]     mst_aw_id_o,
    output logic [AXI_USER_WIDTH-1:0]   mst_aw_user_o,
    input  logic                        mst_aw_ready_i,
    output logic                        mst_aw_valid_o,

    output logic [AXI_ADDR_WIDTH-1:0]   mst_ar_addr_o,
    output logic [2:0]                  mst_ar_prot_o,
    output logic [3:0]                  mst_ar_region_o,
    output logic [7:0]                  mst_ar_len_o,
    output logic [2:0]                  mst_ar_size_o,
    output logic [1:0]                  mst_ar_burst_o,
    output logic                        mst_ar_lock_o,
    output logic [3:0]                  mst_ar_cache_o,
    output logic [3:0]                  mst_ar_qos_o,
    output logic [AXI_ID_WIDTH-1:0]     mst_ar_id_o,
    output logic [AXI_USER_WIDTH-1:0]   mst_ar_user_o,
    input  logic                        mst_ar_ready_i,
    output logic                        mst_ar_valid_o,

    output logic [AXI_DATA_WIDTH-1:0]   mst_w_data_o,
    output logic [AXI_STRB_WIDTH-1:0]   mst_w_strb_o,
    output logic [AXI_USER_WIDTH-1:0]   mst_w_user_o,
    output logic                        mst_w_last_o,
    input  logic                        mst_w_ready_i,
    output logic                        mst_w_valid_o,

    input  logic [AXI_DATA_WIDTH-1:0]   mst_r_data_i,
    input  logic [1:0]                  mst_r_resp_i,
    input  logic                        mst_r_last_i,
    input  logic [AXI_ID_WIDTH-1:0]     mst_r_id_i,
    input  logic [AXI_USER_WIDTH-1:0]   mst_r_user_i,
    output logic                        mst_r_ready_o,
    input  logic                        mst_r_valid_i,

    input  logic [1:0]                  mst_b_resp_i,
    input  logic [AXI_ID_WIDTH-1:0]     mst_b_id_i,
    input  logic [AXI_USER_WIDTH-1:0]   mst_b_user_i,
    output logic                        mst_b_ready_o,
    input  logic                        mst_b_valid_i
);

    // Declarations of Signals and Types

    logic [AXI_ID_WIDTH-1:0]        art_check_id,
                                    art_set_id,
                                    w_id_d,                     w_id_q;

    logic [AXI_ADDR_WIDTH-1:0]      art_check_addr,
                                    art_clr_addr,
                                    art_set_addr,
                                    rd_clr_addr,
                                    wr_clr_addr,
                                    w_addr_d,                   w_addr_q;

    logic                           art_check_req,              art_check_gnt,
                                    art_clr_req,                art_clr_gnt,
                                    art_set_req,                art_set_gnt,
                                    rd_clr_req,                 rd_clr_gnt,
                                    wr_clr_req,                 wr_clr_gnt;

    logic                           art_check_res;

    logic                           b_excl_d,                   b_excl_q,
                                    r_excl_d,                   r_excl_q;

    typedef enum logic [1:0]    {R_IDLE, R_WAIT_AR, R_WAIT_R} r_state_t;
    r_state_t                       r_state_d,                  r_state_q;

    typedef enum logic [2:0]    {AW_IDLE, W_FORWARD, W_BYPASS, W_WAIT_ART_CLR, W_DROP, B_FORWARD,
                                B_INJECT} w_state_t;
    w_state_t                       w_state_d,                  w_state_q;

    // AR and R Channel

    // Time-Invariant Signal Assignments
    assign mst_ar_addr_o      = slv_ar_addr_i;
    assign mst_ar_prot_o      = slv_ar_prot_i;
    assign mst_ar_region_o    = slv_ar_region_i;
    assign mst_ar_len_o       = slv_ar_len_i;
    assign mst_ar_size_o      = slv_ar_size_i;
    assign mst_ar_burst_o     = slv_ar_burst_i;
    assign mst_ar_lock_o      = 1'b0;
    assign mst_ar_cache_o     = slv_ar_cache_i;
    assign mst_ar_qos_o       = slv_ar_qos_i;
    assign mst_ar_id_o        = slv_ar_id_i;
    assign mst_ar_user_o      = slv_ar_user_i;
    assign slv_r_data_o       = mst_r_data_i;
    assign slv_r_last_o       = mst_r_last_i;
    assign slv_r_id_o         = mst_r_id_i;
    assign slv_r_user_o       = mst_r_user_i;

    // FSM for Time-Variant Signal Assignments
    always_comb begin
        mst_ar_valid_o  = 1'b0;
        slv_ar_ready_o  = 1'b0;
        mst_r_ready_o   = 1'b0;
        slv_r_valid_o   = 1'b0;
        slv_r_resp_o    = '0;
        art_set_addr    = '0;
        art_set_id      = '0;
        art_set_req     = 1'b0;
        rd_clr_addr     = '0;
        rd_clr_req      = 1'b0;
        r_excl_d        = r_excl_q;
        r_state_d       = r_state_q;

        case (r_state_q)

            R_IDLE: begin
                if (slv_ar_valid_i) begin
                    if (slv_ar_addr_i >= ADDR_BEGIN && slv_ar_addr_i <= ADDR_END && slv_ar_lock_i &&
                            slv_ar_len_i == 8'h00) begin
                        // Inside exclusively-accessible address range and exclusive access and no
                        // burst
                        art_set_addr    = slv_ar_addr_i;
                        art_set_id      = slv_ar_id_i;
                        art_set_req     = 1'b1;
                        r_excl_d        = 1'b1;
                        if (art_set_gnt) begin
                            mst_ar_valid_o = 1'b1;
                            if (mst_ar_ready_i) begin
                                slv_ar_ready_o = 1'b1;
                                r_state_d = R_WAIT_R;
                            end else begin
                                r_state_d = R_WAIT_AR;
                            end
                        end
                    end else begin
                        // Outside exclusively-accessible address range or regular access or burst
                        r_excl_d = 1'b0;
                        mst_ar_valid_o = 1'b1;
                        if (mst_ar_ready_i) begin
                            slv_ar_ready_o = 1'b1;
                            r_state_d = R_WAIT_R;
                        end else begin
                            r_state_d = R_WAIT_AR;
                        end
                    end
                end
            end

            R_WAIT_AR: begin
                mst_ar_valid_o = slv_ar_valid_i;
                slv_ar_ready_o = mst_ar_ready_i;
                if (mst_ar_ready_i && mst_ar_valid_o) begin
                    r_state_d = R_WAIT_R;
                end
            end

            R_WAIT_R: begin
                mst_r_ready_o = slv_r_ready_i;
                slv_r_valid_o = mst_r_valid_i;
                if (mst_r_resp_i[1] == 1'b0) begin
                    slv_r_resp_o = {1'b0, r_excl_q};
                end else begin
                    slv_r_resp_o = mst_r_resp_i;
                end
                if (mst_r_valid_i && mst_r_ready_o && mst_r_last_i) begin
                    r_excl_d    = 1'b0;
                    r_state_d   = R_IDLE;
                end
            end

            default: begin
                r_state_d = R_IDLE;
            end
        endcase
    end

    // AW, W and B Channel

    // Time-Invariant Signal Assignments
    assign mst_aw_addr_o    = slv_aw_addr_i;
    assign mst_aw_prot_o    = slv_aw_prot_i;
    assign mst_aw_region_o  = slv_aw_region_i;
    assign mst_aw_atop_o    = slv_aw_atop_i;
    assign mst_aw_len_o     = slv_aw_len_i;
    assign mst_aw_size_o    = slv_aw_size_i;
    assign mst_aw_burst_o   = slv_aw_burst_i;
    assign mst_aw_lock_o    = 1'b0;
    assign mst_aw_cache_o   = slv_aw_cache_i;
    assign mst_aw_qos_o     = slv_aw_qos_i;
    assign mst_aw_id_o      = slv_aw_id_i;
    assign mst_aw_user_o    = slv_aw_user_i;
    assign mst_w_data_o     = slv_w_data_i;
    assign mst_w_strb_o     = slv_w_strb_i;
    assign mst_w_user_o     = slv_w_user_i;
    assign mst_w_last_o     = slv_w_last_i;

    always_comb begin
        w_addr_d    = w_addr_q;
        w_id_d      = w_id_q;
        if (slv_aw_valid_i && slv_aw_ready_o) begin
            w_addr_d    = slv_aw_addr_i;
            w_id_d      = slv_aw_id_i;
        end
    end

    // FSM for Time-Variant Signal Assignments
    always_comb begin
        mst_aw_valid_o  = 1'b0;
        slv_aw_ready_o  = 1'b0;
        mst_w_valid_o   = 1'b0;
        slv_w_ready_o   = 1'b0;
        slv_b_valid_o   = 1'b0;
        mst_b_ready_o   = 1'b0;
        slv_b_resp_o    = '0;
        slv_b_id_o      = '0;
        slv_b_user_o    = '0;
        art_check_addr  = '0;
        art_check_id    = '0;
        art_check_req   = 1'b0;
        wr_clr_addr     = '0;
        wr_clr_req      = 1'b0;
        b_excl_d        = b_excl_q;
        w_state_d       = w_state_q;

        case (w_state_q)

            AW_IDLE: begin
                if (slv_aw_valid_i) begin
                    // New AW, and W channel is idle
                    if (slv_aw_addr_i >= ADDR_BEGIN && slv_aw_addr_i <= ADDR_END) begin
                        // Inside exclusively-accessible address range
                        if (slv_aw_lock_i && slv_aw_len_i == 8'h00) begin
                            // Exclusive access and no burst, so check if reservation exists
                            art_check_addr  = slv_aw_addr_i;
                            art_check_id    = slv_aw_id_i;
                            art_check_req   = 1'b1;
                            if (art_check_gnt) begin
                                if (art_check_res) begin
                                    // Yes, so forward downstream
                                    mst_aw_valid_o = 1'b1;
                                    if (mst_aw_ready_i) begin
                                        slv_aw_ready_o    = 1'b1;
                                        b_excl_d        = 1'b1;
                                        w_state_d       = W_FORWARD;
                                    end
                                end else begin
                                    // No, drop in W channel.
                                    slv_aw_ready_o    = 1'b1;
                                    w_state_d       = W_DROP;
                                end
                            end
                        end else begin
                            // Non-exclusive access or burst, so forward downstream
                            mst_aw_valid_o = 1'b1;
                            if (mst_aw_ready_i) begin
                                slv_aw_ready_o    = 1'b1;
                                w_state_d       = W_FORWARD;
                            end
                        end
                    end else begin
                        // Outside exclusively-accessible address range, so bypass any
                        // modifications.
                        mst_aw_valid_o = 1'b1;
                        slv_aw_ready_o = mst_aw_ready_i;
                        if (slv_aw_ready_o) begin
                            w_state_d = W_BYPASS;
                        end
                    end
                end
            end

            W_FORWARD: begin
                mst_w_valid_o = slv_w_valid_i;
                slv_w_ready_o = mst_w_ready_i;
                if (slv_w_valid_i && slv_w_ready_o && slv_w_last_i) begin
                    wr_clr_addr = w_addr_q;
                    wr_clr_req  = 1'b1;
                    if (wr_clr_gnt) begin
                        w_state_d = B_FORWARD;
                    end else begin
                        w_state_d = W_WAIT_ART_CLR;
                    end
                end
            end

            W_BYPASS: begin
                mst_w_valid_o = slv_w_valid_i;
                slv_w_ready_o = mst_w_ready_i;
                if (slv_w_valid_i && slv_w_ready_o && slv_w_last_i) begin
                    w_state_d = B_FORWARD;
                end
            end

            W_WAIT_ART_CLR: begin
                wr_clr_addr = w_addr_q;
                wr_clr_req  = 1'b1;
                if (wr_clr_gnt) begin
                    w_state_d = B_FORWARD;
                end
            end

            W_DROP: begin
                slv_w_ready_o = 1'b1;
                if (slv_w_valid_i && slv_w_last_i) begin
                    w_state_d = B_INJECT;
                end
            end

            B_FORWARD: begin
                mst_b_ready_o   = slv_b_ready_i;
                slv_b_valid_o   = mst_b_valid_i;
                slv_b_resp_o[1] = mst_b_resp_i[1];
                slv_b_resp_o[0] = (mst_b_resp_i[1] == 1'b0) ? b_excl_q : mst_b_resp_i[0];
                slv_b_user_o    = mst_b_user_i;
                slv_b_id_o      = mst_b_id_i;
                if (slv_b_valid_o && slv_b_ready_i) begin
                    b_excl_d    = 1'b0;
                    w_state_d   = AW_IDLE;
                end
            end

            B_INJECT: begin
                slv_b_id_o = w_id_q;
                slv_b_resp_o = 2'b00;
                slv_b_valid_o = 1'b1;
                if (slv_b_ready_i) begin
                    w_state_d = AW_IDLE;
                end
            end

            default: begin
                w_state_d = AW_IDLE;
            end
        endcase
    end

    // AXI Reservation Table
    axi_res_tbl #(
        .AXI_ADDR_WIDTH (AXI_ADDR_WIDTH),
        .AXI_ID_WIDTH   (AXI_ID_WIDTH)
    ) i_art (
        .clk_i                  (clk_i),
        .rst_ni                 (rst_ni),
        .clr_addr_i             (art_clr_addr),
        .clr_req_i              (art_clr_req),
        .clr_gnt_o              (art_clr_gnt),
        .set_addr_i             (art_set_addr),
        .set_id_i               (art_set_id),
        .set_req_i              (art_set_req),
        .set_gnt_o              (art_set_gnt),
        .check_addr_i           (art_check_addr),
        .check_id_i             (art_check_id),
        .check_res_o            (art_check_res),
        .check_req_i            (art_check_req),
        .check_gnt_o            (art_check_gnt)
    );

    // ART Clear Arbiter
    stream_arbiter #(
        .DATA_T     (logic[AXI_ADDR_WIDTH-1:0]),
        .N_INP      (2)
    ) i_non_excl_acc_arb (
        .clk_i          (clk_i),
        .rst_ni         (rst_ni),
        .inp_data_i     ({rd_clr_addr,  wr_clr_addr}),
        .inp_valid_i    ({rd_clr_req,   wr_clr_req}),
        .inp_ready_o    ({rd_clr_gnt,   wr_clr_gnt}),
        .oup_data_o     (art_clr_addr),
        .oup_valid_o    (art_clr_req),
        .oup_ready_i    (art_clr_gnt)
    );

    // Registers
    always_ff @(posedge clk_i, negedge rst_ni) begin
        if (~rst_ni) begin
            b_excl_q    <= 1'b0;
            r_excl_q    <= 1'b0;
            r_state_q   <= R_IDLE;
            w_addr_q    <= '0;
            w_id_q      <= '0;
            w_state_q   <= AW_IDLE;
        end else begin
            b_excl_q    <= b_excl_d;
            r_excl_q    <= r_excl_d;
            r_state_q   <= r_state_d;
            w_addr_q    <= w_addr_d;
            w_id_q      <= w_id_d;
            w_state_q   <= w_state_d;
        end
    end

    // Validate parameters.
// pragma translate_off
`ifndef VERILATOR
    initial begin: validate_params
        assert (ADDR_END > ADDR_BEGIN)
            else $fatal(1, "ADDR_END must be greater than ADDR_BEGIN!");
        assert (AXI_ADDR_WIDTH > 0)
            else $fatal(1, "AXI_ADDR_WIDTH must be greater than 0!");
        assert (AXI_DATA_WIDTH > 0)
            else $fatal(1, "AXI_DATA_WIDTH must be greater than 0!");
        assert (AXI_ID_WIDTH > 0)
            else $fatal(1, "AXI_ID_WIDTH must be greater than 0!");
    end
`endif
// pragma translate_on

endmodule

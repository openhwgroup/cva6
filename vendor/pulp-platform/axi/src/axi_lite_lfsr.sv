// Copyright 2022 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// Authors:
// - Thomas Benz <tbenz@iis.ee.ethz.ch>

`include "common_cells/registers.svh"

/// AXI4 Lite LFSR Subordinate device. Responds with a pseudo random answer. Serial interface to
/// set the internal state.
module axi_lite_lfsr #(
    /// AXI4 Lite Data Width
    parameter int unsigned DataWidth = 32'd0,
    /// AXI4 Lite request struct definition
    parameter type axi_lite_req_t    = logic,
    /// AXI4 Lite response struct definition
    parameter type axi_lite_rsp_t    = logic
)(
    /// Rising-edge clock
    input  logic          clk_i,
    /// Active-low reset
    input  logic          rst_ni,
    /// Testmode
    input  logic          testmode_i,
    /// AXI4 Lite request struct
    input  axi_lite_req_t req_i,
    /// AXI4 Lite response struct
    output axi_lite_rsp_t rsp_o,
    /// Serial shift data in (write)
    input  logic          w_ser_data_i,
    /// Serial shift data out (write)
    output logic          w_ser_data_o,
    /// Serial shift enable (write)
    input  logic          w_ser_en_i,
    /// Serial shift data in (read)
    input  logic          r_ser_data_i,
    /// Serial shift data out (read)
    output logic          r_ser_data_o,
    /// Serial shift enable (read)
    input  logic          r_ser_en_i
);

    /// AXI4 Strobe Width
    localparam int unsigned StrbWidth = DataWidth / 8;

    logic w_lfsr_en;
    logic r_lfsr_en;

    logic w_b_fifo_ready;

    // LFSR outputs
    logic [DataWidth-1:0] w_data_in, w_data_out;

    // AW (ignored)
    assign rsp_o.aw_ready = !w_ser_en_i;

    // W
    axi_opt_lfsr #(
        .Width ( DataWidth )
    ) i_axi_opt_lfsr_w (
        .clk_i,
        .rst_ni,
        .en_i        ( w_lfsr_en    ),
        .ser_data_i  ( w_ser_data_i ),
        .ser_data_o  ( w_ser_data_o ),
        .ser_en_i    ( w_ser_en_i   ),
        .inp_en_i    ( w_lfsr_en    ),
        .data_i      ( w_data_in    ),
        .data_o      ( w_data_out   )
    );
    assign w_lfsr_en     = req_i.w_valid & rsp_o.w_ready;
    assign rsp_o.w_ready = !w_ser_en_i & w_b_fifo_ready;

    // only write bytes with strobe signal enabled
    always_comb begin : gen_data_strb_connect
        for (int unsigned i = 0; i < StrbWidth; i++) begin : gen_strb_en
            if (req_i.w.strb[i] == 1'b0) begin
                w_data_in[i*8+:8] = w_data_out[i*8+:8];
            end else if (req_i.w.strb[i] == 1'b1) begin
                w_data_in[i*8+:8] = req_i.w.data[i*8+:8];
            end else begin
                w_data_in[i*8+:8] = 'x;
            end
        end
    end

    // B
    stream_fifo #(
        .FALL_THROUGH ( 1'b0 ),
        .DATA_WIDTH   ( 'd1  ),
        .DEPTH        ( 'd2  )
    ) i_stream_fifo_w_b (
        .clk_i,
        .rst_ni,
        .testmode_i,
        .flush_i    ( 1'b0                ),
        .usage_o    ( /* NOT CONNECTED */ ),
        .data_i     ( 1'b0                ),
        .valid_i    ( req_i.w_valid       ),
        .ready_o    ( w_b_fifo_ready      ),
        .data_o     ( /* NOT CONNECTED */ ),
        .valid_o    ( w_b_fifo_valid      ),
        .ready_i    ( req_i.b_ready       )
    );
    assign rsp_o.b.resp  = axi_pkg::RESP_OKAY;
    assign rsp_o.b_valid = w_b_fifo_valid;

    // AR (ignored)
    assign rsp_o.ar_ready = !w_ser_en_i;

    // R
    axi_opt_lfsr #(
        .Width ( DataWidth )
    ) i_axi_opt_lfsr_r (
        .clk_i,
        .rst_ni,
        .en_i        ( r_lfsr_en           ),
        .ser_data_i  ( r_ser_data_i        ),
        .ser_data_o  ( r_ser_data_o        ),
        .ser_en_i    ( r_ser_en_i          ),
        .inp_en_i    ( 1'b0                ),
        .data_i      ( /* NOT CONNECTED */ ),
        .data_o      ( rsp_o.r.data        )
    );
    assign rsp_o.r.resp  = axi_pkg::RESP_OKAY;
    assign r_lfsr_en     = req_i.r_ready & rsp_o.r_valid;
    assign rsp_o.r_valid = !r_ser_en_i;

endmodule : axi_lite_lfsr


/// XOR LFSR with tabs based on the [lfsr_table](https://datacipy.cz/lfsr_table.pdf). LFSR has
/// a serial interface to set the initial state
module axi_opt_lfsr #(
    parameter int unsigned Width = 32'd0
) (
    /// Rising-edge clock
    input  logic clk_i,
    /// Active-low reset
    input  logic rst_ni,
    input  logic en_i,
    input  logic ser_data_i,
    output logic ser_data_o,
    input  logic ser_en_i,
    input  logic inp_en_i,
    input  logic [Width-1:0] data_i,
    output logic [Width-1:0] data_o
);

    /// Number of bits required to hold the LFSR tab configuration
    localparam int unsigned LfsrIdxWidth = cf_math_pkg::idx_width(Width);
    /// Maximum number of tabs
    localparam int unsigned MaxNumTabs = 4;

    /// Type specifying the tap positions
    typedef logic [LfsrIdxWidth:0] xnor_entry_t [MaxNumTabs-1:0];
    xnor_entry_t XnorFeedback;

    // the shift register
    logic [Width-1:0] reg_d, reg_q;

    // the feedback signal
    logic xnor_feedback;

    always_comb begin : gen_register

        // get the parameters
        case (Width)
            'd8     : XnorFeedback = { 'd8,    'd6,    'd5,    'd4    };
            'd16    : XnorFeedback = { 'd16,   'd14,   'd13,   'd11   };
            'd32    : XnorFeedback = { 'd32,   'd30,   'd26,   'd25   };
            'd64    : XnorFeedback = { 'd64,   'd63,   'd61,   'd60   };
            'd128   : XnorFeedback = { 'd128,  'd127,  'd126,  'd119  };
            'd256   : XnorFeedback = { 'd256,  'd256,  'd521,  'd246  };
            'd512   : XnorFeedback = { 'd512,  'd510,  'd507,  'd504  };
            'd1024  : XnorFeedback = { 'd1024, 'd1015, 'd1002, 'd1001 };
            default : XnorFeedback = { 'x,     'x,     'x,     'x     };
        endcase

        // shift register functionality
        // compression mode
        if (inp_en_i) begin
            for (int unsigned i = 0; i < Width - 1; i++) begin : gen_comp_conection
                reg_d[i] = reg_q[i+1] ^ data_i[i];
            end
        // generation mode
        end else begin
            for (int unsigned i = 0; i < Width - 1; i++) begin : gen_gen_conection
                reg_d[i] = reg_q[i+1];
            end
        end
        // serial access mode
        if (ser_en_i) begin
            // new head element
            reg_d[Width-1] = ser_data_i;
        // LFSR mode
        end else begin
            xnor_feedback = reg_q[XnorFeedback[MaxNumTabs-1]-1];
            for (int unsigned t = 0; t < MaxNumTabs - 1; t++) begin : gen_feedback_path
                xnor_feedback = xnor_feedback;
                if (XnorFeedback[t] != 0) begin
                    xnor_feedback = xnor_feedback ^ reg_q[XnorFeedback[t]-1];
                end
            end
            reg_d[Width-1] = inp_en_i ? xnor_feedback ^ data_i[Width-1] : xnor_feedback;
        end
    end

    // connect outputs
    assign ser_data_o = reg_q[0];
    assign data_o     = reg_q;

    // state
    `FFL(reg_q, reg_d, en_i | ser_en_i, '1, clk_i, rst_ni)

endmodule : axi_opt_lfsr

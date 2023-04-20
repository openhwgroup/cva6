// Copyright 2022 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51
//
// Authors:
// - Thomas Benz <tbenz@iis.ee.ethz.ch>

/// Throttles an AXI4+ATOP bus. The maximum number of outstanding transfers have to
/// be set as a compile-time parameter, whereas the number of outstanding transfers can be set
/// during runtime. This module assumes either in-order processing of the requests or
/// indistinguishability of the request/responses (all ARs and AWs have the same ID respectively).
module axi_throttle #(
    /// The maximum amount of allowable outstanding write requests
    parameter int unsigned MaxNumAwPending = 1,
    /// The maximum amount of allowable outstanding read requests
    parameter int unsigned MaxNumArPending = 1,
    /// AXI4+ATOP request type
    parameter type axi_req_t = logic,
    /// AXI4+ATOP response type
    parameter type axi_rsp_t = logic,
    /// The width of the write credit counter (*DO NOT OVERWRITE*)
    parameter int unsigned WCntWidth = cf_math_pkg::idx_width(MaxNumAwPending),
    /// The width of the read credit counter (*DO NOT OVERWRITE*)
    parameter int unsigned RCntWidth = cf_math_pkg::idx_width(MaxNumArPending),
    /// The type of the write credit counter (*DO NOT OVERWRITE*)
    parameter type w_credit_t = logic [WCntWidth-1:0],
    /// The type of the read credit counter (*DO NOT OVERWRITE*)
    parameter type r_credit_t = logic [RCntWidth-1:0]
) (
    /// Clock
    input  logic clk_i,
    /// Asynchronous reset, active low
    input  logic rst_ni,

    /// AXI4+ATOP request in
    input  axi_req_t req_i,
    /// AXI4+ATOP response out
    output axi_rsp_t rsp_o,
    /// AXI4+ATOP request out
    output axi_req_t req_o,
    /// AXI4+ATOP response in
    input  axi_rsp_t rsp_i,

    /// Amount of write credit (number of outstanding write transfers)
    input  w_credit_t w_credit_i,
    /// Amount of read credit (number of outstanding read transfers)
    input  r_credit_t r_credit_i
);

    // ax throttled valids
    logic throttled_aw_valid;
    logic throttled_ar_valid;

    // ax throttled readies
    logic throttled_aw_ready;
    logic throttled_ar_ready;

    // limit Aw requests -> wait for b
    stream_throttle #(
        .MaxNumPending ( MaxNumAwPending  )
    ) i_stream_throttle_aw (
        .clk_i,
        .rst_ni,
        .req_valid_i ( req_i.aw_valid     ),
        .req_valid_o ( throttled_aw_valid ),
        .req_ready_i ( rsp_i.aw_ready     ),
        .req_ready_o ( throttled_aw_ready ),
        .rsp_valid_i ( rsp_i.b_valid      ),
        .rsp_ready_i ( req_i.b_ready      ),
        .credit_i    ( w_credit_i         )
    );

    // limit Ar requests -> wait for r.last
    stream_throttle #(
        .MaxNumPending ( MaxNumArPending  )
    ) i_stream_throttle_ar (
        .clk_i,
        .rst_ni,
        .req_valid_i ( req_i.ar_valid               ),
        .req_valid_o ( throttled_ar_valid           ),
        .req_ready_i ( rsp_i.ar_ready               ),
        .req_ready_o ( throttled_ar_ready           ),
        .rsp_valid_i ( rsp_i.r_valid & rsp_i.r.last ),
        .rsp_ready_i ( req_i.r_ready                ),
        .credit_i    ( r_credit_i                   )
    );

    // connect the throttled request bus (its a through connection - except for the ax valids)
    always_comb begin : gen_throttled_req_conn
        req_o          = req_i;
        req_o.aw_valid = throttled_aw_valid;
        req_o.ar_valid = throttled_ar_valid;
    end

    // connect the throttled response bus (its a through connection - except for the ax readies)
    always_comb begin : gen_throttled_rsp_conn
        rsp_o          = rsp_i;
        rsp_o.aw_ready = throttled_aw_ready;
        rsp_o.ar_ready = throttled_ar_ready;
    end

endmodule : axi_throttle

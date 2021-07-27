// Copyright (c) 2014-2018 ETH Zurich, University of Bologna
//
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// Florian Zaruba <zarubaf@iis.ee.ethz.ch>

/// Change the AXI ID width.
///
/// This module instantiates a downsizer if the outgoing ID is smaller than the
/// incoming ID. Otherwise instantiates a joiner, which implicitly expands AXI
/// IDs.
module axi_id_resize #(
    parameter int ADDR_WIDTH   = -1,
    parameter int DATA_WIDTH   = -1,
    parameter int USER_WIDTH   = -1,
    parameter int ID_WIDTH_IN  = -1,
    parameter int ID_WIDTH_OUT = -1,
    parameter int TABLE_SIZE   = 1
)(
    input logic     clk_i,
    input logic     rst_ni,
    AXI_BUS.Slave   in,
    AXI_BUS.Master  out
);

    // Instantiate a downsizer if the outgoing ID is smaller, otherwise simply
    // instantiate a connecor which implicitly extends the ID width.
    if (ID_WIDTH_IN > ID_WIDTH_OUT) begin : g_remap
        axi_id_downsize #(
            .ADDR_WIDTH   ( ADDR_WIDTH   ),
            .DATA_WIDTH   ( DATA_WIDTH   ),
            .USER_WIDTH   ( USER_WIDTH   ),
            .ID_WIDTH_IN  ( ID_WIDTH_IN  ),
            .ID_WIDTH_OUT ( ID_WIDTH_OUT ),
            .TABLE_SIZE   ( TABLE_SIZE   )
        ) i_downsize (
            .clk_i  ( clk_i  ),
            .rst_ni ( rst_ni ),
            .in     ( in     ),
            .out    ( out    )
        );
    end else begin : g_remap
        axi_join i_join (in, out);
    end

endmodule


/// Re-allocate AXI IDs.
module axi_id_remap #(
    parameter int ADDR_WIDTH    = -1,
    parameter int DATA_WIDTH    = -1,
    parameter int USER_WIDTH    = -1,
    parameter int ID_WIDTH_IN   = -1,
    parameter int ID_WIDTH_OUT  = -1,
    parameter int TABLE_SIZE    = 1
)(
    input logic     clk_i,
    input logic     rst_ni,
    AXI_BUS.Slave   in,
    AXI_BUS.Master  out
);

    logic full_id_aw_b;
    logic empty_id_aw_b;
    logic full_id_ar_r;
    logic empty_id_ar_r;

    // Check the invariants.
    `ifndef SYNTHESIS
    initial begin
    assert(ADDR_WIDTH >= 0);
    assert(DATA_WIDTH >= 0);
    assert(ID_WIDTH_IN >= 0);
    assert(ID_WIDTH_OUT >= 0);
    assert(USER_WIDTH >= 0);
    assert(in.AXI_ADDR_WIDTH == ADDR_WIDTH);
    assert(in.AXI_DATA_WIDTH == DATA_WIDTH);
    assert(in.AXI_ID_WIDTH == ID_WIDTH_IN);
    assert(in.AXI_USER_WIDTH == USER_WIDTH);
    assert(out.AXI_ADDR_WIDTH == ADDR_WIDTH);
    assert(out.AXI_DATA_WIDTH == DATA_WIDTH);
    assert(out.AXI_ID_WIDTH == ID_WIDTH_OUT);
    assert(out.AXI_USER_WIDTH == USER_WIDTH);
    end
    `endif
    // pass through data signals
    assign out.aw_addr   = in.aw_addr;
    assign out.aw_len    = in.aw_len;
    assign out.aw_size   = in.aw_size;
    assign out.aw_burst  = in.aw_burst;
    assign out.aw_lock   = in.aw_lock;
    assign out.aw_cache  = in.aw_cache;
    assign out.aw_prot   = in.aw_prot;
    assign out.aw_qos    = in.aw_qos;
    assign out.aw_region = in.aw_region;
    assign out.aw_atop   = in.aw_atop;
    assign out.aw_user   = in.aw_user;

    assign out.ar_addr   = in.ar_addr;
    assign out.ar_len    = in.ar_len;
    assign out.ar_size   = in.ar_size;
    assign out.ar_burst  = in.ar_burst;
    assign out.ar_lock   = in.ar_lock;
    assign out.ar_cache  = in.ar_cache;
    assign out.ar_prot   = in.ar_prot;
    assign out.ar_qos    = in.ar_qos;
    assign out.ar_region = in.ar_region;
    assign out.ar_user   = in.ar_user;

    assign out.w_data    =  in.w_data;
    assign out.w_strb    =  in.w_strb;
    assign out.w_last    =  in.w_last;
    assign out.w_user    =  in.w_user;
    assign out.w_valid   =  in.w_valid;
    assign in.w_ready    =  out.w_ready;

    assign in.r_data     = out.r_data;
    assign in.r_resp     = out.r_resp;
    assign in.r_last     = out.r_last;
    assign in.r_user     = out.r_user;

    assign in.b_resp     =  out.b_resp;
    assign in.b_user     =  out.b_user;

    assign in.aw_ready   = out.aw_ready & ~full_id_aw_b;
    assign out.aw_valid  = in.aw_valid & ~full_id_aw_b;
    assign in.b_valid    = out.b_valid & ~empty_id_aw_b;
    assign out.b_ready   = in.b_ready & ~empty_id_aw_b;

    assign in.ar_ready   = out.ar_ready & ~full_id_ar_r;
    assign out.ar_valid  = in.ar_valid & ~full_id_ar_r;
    assign in.r_valid    = out.r_valid & ~empty_id_ar_r;
    assign out.r_ready   = in.r_ready & ~empty_id_ar_r;

    axi_remap_table #(
        .ID_WIDTH_IN  ( ID_WIDTH_IN  ),
        .ID_WIDTH_OUT ( ID_WIDTH_OUT ),
        .TABLE_SIZE   ( TABLE_SIZE   )
    ) i_aw_b_remap (
        .clk_i        ( clk_i                                      ),
        .rst_ni       ( rst_ni                                     ),
        .incr_i       ( in.aw_valid & ~full_id_aw_b & out.aw_ready ),
        .full_o       ( full_id_aw_b                               ),
        .id_i         ( in.aw_id                                   ),
        .id_o         ( out.aw_id                                  ),
        .release_id_i ( out.b_valid & in.b_ready & ~empty_id_aw_b  ),
        .rel_id_i     ( out.b_id                                   ),
        .rel_id_o     ( in.b_id                                    ),
        .empty_o      ( empty_id_aw_b                              )
    );

    axi_remap_table #(
        .ID_WIDTH_IN  ( ID_WIDTH_IN  ),
        .ID_WIDTH_OUT ( ID_WIDTH_OUT ),
        .TABLE_SIZE   ( TABLE_SIZE   )
    ) i_ar_r_remap (
        .clk_i        ( clk_i                                                  ),
        .rst_ni       ( rst_ni                                                 ),
        .incr_i       ( in.ar_valid & ~full_id_ar_r & out.ar_ready             ),
        .full_o       ( full_id_ar_r                                           ),
        .id_i         ( in.ar_id                                               ),
        .id_o         ( out.ar_id                                              ),
        .release_id_i ( out.r_valid & in.r_ready & out.r_last & ~empty_id_ar_r ),
        .rel_id_i     ( out.r_id                                               ),
        .rel_id_o     ( in.r_id                                                ),
        .empty_o      ( empty_id_ar_r                                          )
    );


endmodule


module axi_remap_table #(
    parameter int          ID_WIDTH_IN  = -1,
    parameter int          ID_WIDTH_OUT = -1,
    parameter int unsigned TABLE_SIZE   =  1
)(
    input logic                     clk_i,
    input logic                     rst_ni,

    input  logic                    incr_i,
    output logic                    full_o,
    input  logic [ID_WIDTH_IN-1:0]  id_i,
    output logic [ID_WIDTH_OUT-1:0] id_o,

    input  logic                    release_id_i,
    input  logic [ID_WIDTH_OUT-1:0] rel_id_i,
    output logic [ID_WIDTH_IN-1:0]  rel_id_o,
    output logic                    empty_o
);

    struct packed {
        logic                   valid;
        logic [ID_WIDTH_IN-1:0] id;
    } remap_table_d[TABLE_SIZE-1:0], remap_table_q[TABLE_SIZE-1:0], id;

    logic [TABLE_SIZE-1:0] valid;
    logic [$clog2(TABLE_SIZE):0] current_index;

    // generate valid signals
    for (genvar i = 0; i < TABLE_SIZE; i++) begin
        assign valid[i] = remap_table_q[i].valid;
    end

    assign empty_o = ~(|valid);
    assign full_o = id.valid;

    generate
        if (ID_WIDTH_OUT <= $clog2(TABLE_SIZE))
            assign id_o = current_index;
        else
            assign id_o = {{{ID_WIDTH_OUT-$clog2(TABLE_SIZE)}{1'b0}}, current_index};
    endgenerate

    assign rel_id_o = remap_table_q[rel_id_i].id;

    always_comb begin
        current_index = 0;

        remap_table_d = remap_table_q;

        // get the topmost bit
        for (int unsigned i = 0; i < TABLE_SIZE; i++) begin
            if (!valid[i]) begin
                current_index = i;
                break;
            end
        end

        id = remap_table_q[current_index];

        // store another element
        if (incr_i) begin
            remap_table_d[current_index].valid = 1'b1;
            remap_table_d[current_index].id = id_i;
        end

        if (release_id_i) begin
            remap_table_d[rel_id_i[$clog2(TABLE_SIZE)-1:0]].valid = 1'b0;
        end
    end
    // -- Registers
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (~rst_ni) begin
            for (int i = 0; i < TABLE_SIZE; i++)
                remap_table_q[i] <= '0;
        end else begin
            remap_table_q <= remap_table_d;
        end
    end
endmodule

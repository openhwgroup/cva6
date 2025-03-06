// Copyright 2019 ETH Zurich
// Fabian Schuiki <fschuiki@iis.ee.ethz.ch>
// Florian Zaruba <zarubaf@iis.ee.ethz.ch>

/// A protocol converter from AXI4-Lite to a register interface.
module axi_lite_to_reg #(
  /// The width of the address.
  parameter int ADDR_WIDTH = -1,
  /// The width of the data.
  parameter int DATA_WIDTH = -1,
  /// Buffer depth (how many outstanding transactions do we allow)
  parameter int BUFFER_DEPTH = 2,
  /// Whether the AXI-Lite W channel should be decoupled with a register. This
  /// can help break long paths at the expense of registers.
  parameter bit DECOUPLE_W = 1,
  /// AXI-Lite request struct type.
  parameter type axi_lite_req_t = logic,
  /// AXI-Lite response struct type.
  parameter type axi_lite_rsp_t = logic,
  /// Regbus request struct type.
  parameter type reg_req_t = logic,
  /// Regbus response struct type.
  parameter type reg_rsp_t = logic
) (
  input  logic           clk_i         ,
  input  logic           rst_ni        ,
  input  axi_lite_req_t  axi_lite_req_i,
  output axi_lite_rsp_t  axi_lite_rsp_o,
  output reg_req_t       reg_req_o     ,
  input  reg_rsp_t       reg_rsp_i
);

  `ifndef SYNTHESIS
  initial begin
    assert(BUFFER_DEPTH > 0);
    assert(ADDR_WIDTH > 0);
    assert(DATA_WIDTH > 0);
  end
  `endif

  typedef struct packed {
    logic [ADDR_WIDTH-1:0]   addr;
    logic [DATA_WIDTH-1:0]   data;
    logic [DATA_WIDTH/8-1:0] strb; // byte-wise strobe
  } write_t;

  typedef struct packed {
    logic [ADDR_WIDTH-1:0] addr;
    logic write;
  } req_t;

  typedef struct packed {
    logic [DATA_WIDTH-1:0] data;
    logic error;
  } resp_t;

  logic   write_fifo_full, write_fifo_empty;
  write_t write_fifo_in,   write_fifo_out;
  logic   write_fifo_push, write_fifo_pop;

  logic   write_resp_fifo_full, write_resp_fifo_empty;
  logic   write_resp_fifo_in,   write_resp_fifo_out;
  logic   write_resp_fifo_push, write_resp_fifo_pop;

  logic   read_fifo_full, read_fifo_empty;
  logic [ADDR_WIDTH-1:0]  read_fifo_in,   read_fifo_out;
  logic   read_fifo_push, read_fifo_pop;

  logic   read_resp_fifo_full, read_resp_fifo_empty;
  resp_t  read_resp_fifo_in,   read_resp_fifo_out;
  logic   read_resp_fifo_push, read_resp_fifo_pop;

  req_t read_req, write_req, arb_req;
  logic read_valid, write_valid;
  logic read_ready, write_ready;

  // Combine AW/W Channel
  fifo_v3 #(
    .FALL_THROUGH ( !DECOUPLE_W  ),
    .DEPTH        ( BUFFER_DEPTH ),
    .dtype        ( write_t      )
  ) i_fifo_write_req (
    .clk_i,
    .rst_ni,
    .flush_i    ( 1'b0             ),
    .testmode_i ( 1'b0             ),
    .full_o     ( write_fifo_full  ),
    .empty_o    ( write_fifo_empty ),
    .usage_o    ( /* open */       ),
    .data_i     ( write_fifo_in    ),
    .push_i     ( write_fifo_push  ),
    .data_o     ( write_fifo_out   ),
    .pop_i      ( write_fifo_pop   )
  );

  assign axi_lite_rsp_o.aw_ready = write_fifo_push;
  assign axi_lite_rsp_o.w_ready = write_fifo_push;
  assign write_fifo_push = axi_lite_req_i.aw_valid & axi_lite_req_i.w_valid & ~write_fifo_full;
  assign write_fifo_in.addr = axi_lite_req_i.aw.addr;
  assign write_fifo_in.data = axi_lite_req_i.w.data;
  assign write_fifo_in.strb = axi_lite_req_i.w.strb;
  assign write_fifo_pop = write_valid & write_ready;

  //  B Channel
  fifo_v3 #(
    .DEPTH        ( BUFFER_DEPTH ),
    .dtype        ( logic        )
  ) i_fifo_write_resp (
    .clk_i,
    .rst_ni,
    .flush_i    ( 1'b0                  ),
    .testmode_i ( 1'b0                  ),
    .full_o     ( write_resp_fifo_full  ),
    .empty_o    ( write_resp_fifo_empty ),
    .usage_o    ( /* open */            ),
    .data_i     ( write_resp_fifo_in    ),
    .push_i     ( write_resp_fifo_push  ),
    .data_o     ( write_resp_fifo_out   ),
    .pop_i      ( write_resp_fifo_pop   )
  );

  assign axi_lite_rsp_o.b_valid = ~write_resp_fifo_empty;
  assign axi_lite_rsp_o.b.resp = write_resp_fifo_out ? axi_pkg::RESP_SLVERR : axi_pkg::RESP_OKAY;
  assign write_resp_fifo_in = reg_rsp_i.error;
  assign write_resp_fifo_push = reg_req_o.valid & reg_rsp_i.ready & reg_req_o.write;
  assign write_resp_fifo_pop = axi_lite_rsp_o.b_valid & axi_lite_req_i.b_ready;

  // AR Channel
  fifo_v3 #(
    .DEPTH        ( BUFFER_DEPTH ),
    .DATA_WIDTH   ( ADDR_WIDTH   )
  ) i_fifo_read (
    .clk_i,
    .rst_ni,
    .flush_i    ( 1'b0            ),
    .testmode_i ( 1'b0            ),
    .full_o     ( read_fifo_full  ),
    .empty_o    ( read_fifo_empty ),
    .usage_o    ( /* open */      ),
    .data_i     ( read_fifo_in    ),
    .push_i     ( read_fifo_push  ),
    .data_o     ( read_fifo_out   ),
    .pop_i      ( read_fifo_pop   )
  );

  assign read_fifo_pop = read_valid && read_ready;
  assign axi_lite_rsp_o.ar_ready = ~read_fifo_full;
  assign read_fifo_push = axi_lite_rsp_o.ar_ready & axi_lite_req_i.ar_valid;
  assign read_fifo_in = axi_lite_req_i.ar.addr;

  // R Channel
  fifo_v3 #(
    .DEPTH        ( BUFFER_DEPTH ),
    .dtype        ( resp_t       )
  ) i_fifo_read_resp (
    .clk_i,
    .rst_ni,
    .flush_i    ( 1'b0                 ),
    .testmode_i ( 1'b0                 ),
    .full_o     ( read_resp_fifo_full  ),
    .empty_o    ( read_resp_fifo_empty ),
    .usage_o    ( /* open */           ),
    .data_i     ( read_resp_fifo_in    ),
    .push_i     ( read_resp_fifo_push  ),
    .data_o     ( read_resp_fifo_out   ),
    .pop_i      ( read_resp_fifo_pop   )
  );

  assign axi_lite_rsp_o.r.data = read_resp_fifo_out.data;
  assign axi_lite_rsp_o.r.resp = read_resp_fifo_out.error ? axi_pkg::RESP_SLVERR : axi_pkg::RESP_OKAY;
  assign axi_lite_rsp_o.r_valid = ~read_resp_fifo_empty;
  assign read_resp_fifo_pop = axi_lite_rsp_o.r_valid & axi_lite_req_i.r_ready;
  assign read_resp_fifo_push = reg_req_o.valid & reg_rsp_i.ready & ~reg_req_o.write;
  assign read_resp_fifo_in.data = reg_rsp_i.rdata;
  assign read_resp_fifo_in.error = reg_rsp_i.error;

  // Make sure we can capture the responses (e.g. have enough fifo space)
  assign read_valid = ~read_fifo_empty & ~read_resp_fifo_full;
  assign write_valid = ~write_fifo_empty & ~write_resp_fifo_full;

  // Arbitrate between read/write
  assign read_req.addr = read_fifo_out;
  assign read_req.write = 1'b0;
  assign write_req.addr = write_fifo_out.addr;
  assign write_req.write = 1'b1;

  stream_arbiter #(
    .DATA_T  ( req_t ),
    .N_INP   ( 2     ),
    .ARBITER ( "rr"  )
  ) i_stream_arbiter (
    .clk_i,
    .rst_ni,
    .inp_data_i  ( {read_req,   write_req}   ),
    .inp_valid_i ( {read_valid, write_valid} ),
    .inp_ready_o ( {read_ready, write_ready} ),
    .oup_data_o  ( arb_req     ),
    .oup_valid_o ( reg_req_o.valid ),
    .oup_ready_i ( reg_rsp_i.ready )
  );

  assign reg_req_o.addr = arb_req.addr;
  assign reg_req_o.write = arb_req.write;
  assign reg_req_o.wdata = write_fifo_out.data;
  assign reg_req_o.wstrb = write_fifo_out.strb;

endmodule



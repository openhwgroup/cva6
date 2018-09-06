/* Copyright 2018 ETH Zurich and University of Bologna.
 * Copyright and related rights are licensed under the Solderpad Hardware
 * License, Version 0.51 (the “License”); you may not use this file except in
 * compliance with the License.  You may obtain a copy of the License at
 * http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
 * or agreed to in writing, software, hardware and materials distributed under
 * this License is distributed on an “AS IS” BASIS, WITHOUT WARRANTIES OR
 * CONDITIONS OF ANY KIND, either express or implied. See the License for the
 * specific language governing permissions and limitations under the License.
 *
 * File:   axi_riscv_debug_module.sv
 * Author: Andreas Traber <atraber@iis.ee.ethz.ch>
 * Author: Florian Zaruba <zarubaf@iis.ee.ethz.ch>
 *
 * Description: Clock domain crossings for JTAG to DMI very heavily based
 *              on previous work by Andreas Traber for the PULP project.
 *              This is mainly a wrapper around the existing CDCs.
 */
module dmi_cdc (
    // JTAG side (master side)
    input  logic                    tck_i,
    input  logic                    trst_ni,

    input  logic                    mem_valid_i,
    output logic                    mem_gnt_o,
    input  logic [6:0]              mem_addr_i,
    input  logic                    mem_we_i,
    input  logic [31:0]             mem_wdata_i,
    output logic [31:0]             mem_rdata_o,
    output logic                    mem_rvalid_o,

    // Memory -> Slave side
    input  logic                    clk_i,
    input  logic                    rst_ni,

    output logic                    dmi_req_valid_o,
    input  logic                    dmi_req_ready_i,

    output logic [ 6:0]             dmi_req_bits_addr_o,
    output logic [ 1:0]             dmi_req_bits_op_o,
    output logic [31:0]             dmi_req_bits_data_o,

    input  logic                    dmi_resp_valid_i,
    output logic                    dmi_resp_ready_o,
    input  logic [ 1:0]             dmi_resp_bits_resp_i,
    input  logic [31:0]             dmi_resp_bits_data_i
);

    logic mem_we;
    // we will always be ready to receive the request we made
    assign dmi_resp_ready_o = 1'b1;
    // very "cheap" protocol conversion
    assign dmi_req_bits_op_o = (mem_we) ? dm::DTM_WRITE : dm::DTM_READ;

    localparam int unsigned AddrWidth = 7;
    localparam int unsigned DataWidth = 32;

    logic                    cdc_req_a;
    logic                    cdc_ack_a;
    logic [AddrWidth-1:0]    cdc_addr_a;
    logic                    cdc_we_a;
    logic [DataWidth/8-1:0]  cdc_be_a;
    logic [DataWidth-1:0]    cdc_wdata_a;
    logic                    cdc_clear_a;
    logic                    cdc_rreq_a;
    logic                    cdc_rack_a;
    logic [DataWidth-1:0]    cdc_rdata_a;
    logic                    cdc_rerror_a;

    // lets re-use most of the debug facilities which are already in PULP
    dmi_cdc_jtag #(
        .ADDR_WIDTH (AddrWidth),
        .DATA_WIDTH (DataWidth)
    ) i_dmi_cdc_jtag (
        .tck_i,
        .trst_ni,
        .mem_req_i      ( mem_valid_i   ),
        .mem_gnt_o,
        .mem_addr_i,
        .mem_we_i,
        .mem_be_i       ( '1            ),
        .mem_wdata_i,
        .mem_rdata_o,
        .mem_rvalid_o,
        // we are not managing any errors here
        // a more elaborate implementation should probably handle this more gracefully
        .mem_rerror_o   (               ),
        .mem_clear_i    ( 1'b0          ),
        .cdc_req_ao     ( cdc_req_a     ),
        .cdc_ack_ai     ( cdc_ack_a     ),
        .cdc_addr_ao    ( cdc_addr_a    ),
        .cdc_we_ao      ( cdc_we_a      ),
        .cdc_be_ao      ( cdc_be_a      ),
        .cdc_wdata_ao   ( cdc_wdata_a   ),
        .cdc_clear_ao   ( cdc_clear_a   ),
        .cdc_rreq_ai    ( cdc_rreq_a    ),
        .cdc_rack_ao    ( cdc_rack_a    ),
        .cdc_rdata_ai   ( cdc_rdata_a   ),
        .cdc_rerror_ai  ( cdc_rerror_a  )
    );

    dmi_cdc_mem #(
        .ADDR_WIDTH (AddrWidth),
        .DATA_WIDTH (DataWidth)
    ) i_dmi_cdc_mem (
        .clk_i,
        .rst_ni,
        .mem_req_o      ( dmi_req_valid_o      ),
        .mem_gnt_i      ( dmi_req_ready_i      ),
        .mem_addr_o     ( dmi_req_bits_addr_o  ),
        .mem_we_o       ( mem_we               ),
        // don't care we always write whole words
        .mem_be_o       (                      ),
        .mem_wdata_o    ( dmi_req_bits_data_o  ),
        .mem_rdata_i    ( dmi_resp_bits_data_i ),
        .mem_rvalid_i   ( dmi_resp_valid_i     ),
        // don't care about clearing an error flag
        // that is handled differently in the RISC-V implementation
        .mem_rerror_i   ( 1'b0                 ),
        .mem_clear_o    (                      ),
        .cdc_req_ai     ( cdc_req_a            ),
        .cdc_ack_ao     ( cdc_ack_a            ),
        .cdc_addr_ai    ( cdc_addr_a           ),
        .cdc_we_ai      ( cdc_we_a             ),
        .cdc_be_ai      ( cdc_be_a             ),
        .cdc_wdata_ai   ( cdc_wdata_a          ),
        .cdc_clear_ai   ( cdc_clear_a          ),
        .cdc_rreq_ao    ( cdc_rreq_a           ),
        .cdc_rack_ai    ( cdc_rack_a           ),
        .cdc_rdata_ao   ( cdc_rdata_a          ),
        .cdc_rerror_ao  ( cdc_rerror_a         )
    );
endmodule

module dmi_cdc_jtag #(
    parameter int unsigned ADDR_WIDTH = 32,
    parameter int unsigned DATA_WIDTH = 64
)(
    // JTAG side
    input  logic                    tck_i,
    input  logic                    trst_ni,

    input  logic                    mem_req_i,
    output logic                    mem_gnt_o,
    input  logic [ADDR_WIDTH-1:0]   mem_addr_i,
    input  logic                    mem_we_i,
    input  logic [DATA_WIDTH/8-1:0] mem_be_i,
    input  logic [DATA_WIDTH-1:0]   mem_wdata_i,
    output logic [DATA_WIDTH-1:0]   mem_rdata_o,
    output logic                    mem_rvalid_o,
    output logic                    mem_rerror_o,

    input  logic                    mem_clear_i,

    // CDC side
    output logic                    cdc_req_ao,
    input  logic                    cdc_ack_ai,
    output logic [ADDR_WIDTH-1:0]   cdc_addr_ao,
    output logic                    cdc_we_ao,
    output logic [DATA_WIDTH/8-1:0] cdc_be_ao,
    output logic [DATA_WIDTH-1:0]   cdc_wdata_ao,
    output logic                    cdc_clear_ao,
    input  logic                    cdc_rreq_ai,
    output logic                    cdc_rack_ao,
    input  logic [DATA_WIDTH-1:0]   cdc_rdata_ai,
    input  logic                    cdc_rerror_ai
  );

  enum logic [1:0] { IDLE, WAIT_ACK_LOW, WAIT_ACK_HIGH, READY_ACK_LOW } req_state_p, req_state_n;
  enum logic [0:0] { RIDLE, WAIT_REQ_LOW } resp_state_p, resp_state_n;

  logic [ADDR_WIDTH-1:0]   cdc_addr_p;
  logic                    cdc_we_p;
  logic [DATA_WIDTH/8-1:0] cdc_be_p;
  logic [DATA_WIDTH-1:0]   cdc_wdata_p;

  logic                    cdc_req_n;

  logic                    cdc_clear_p;

  logic                    cdc_ack;
  logic                    cdc_rreq;

  always_comb
  begin
    req_state_n = req_state_p;

    mem_gnt_o   = 1'b0;
    cdc_req_n   = 1'b0;

    unique case (req_state_p)
      IDLE: begin
        if (mem_req_i) begin
          req_state_n = WAIT_ACK_HIGH;

          mem_gnt_o = 1'b1;
        end
      end

      WAIT_ACK_HIGH: begin
        cdc_req_n  = 1'b1;

        if (cdc_ack) begin
          req_state_n = WAIT_ACK_LOW;
        end
      end

      WAIT_ACK_LOW: begin
        if (mem_req_i)
          mem_gnt_o = 1'b1;

        if (~cdc_ack) begin
          if (mem_req_i)
            req_state_n = WAIT_ACK_HIGH;
          else
            req_state_n = IDLE;
        end else begin
          if (mem_req_i)
            req_state_n = READY_ACK_LOW;
        end
      end

      READY_ACK_LOW: begin
        if (~cdc_ack) begin
          req_state_n = WAIT_ACK_HIGH;
        end
      end

      default:; // make unique case happy during reset
    endcase
  end

  always_comb
  begin
    resp_state_n = resp_state_p;

    mem_rvalid_o = 1'b0;
    cdc_rack_ao  = 1'b0;

    unique case (resp_state_p)
      RIDLE: begin
        if (cdc_rreq) begin
          resp_state_n = WAIT_REQ_LOW;
          mem_rvalid_o = 1'b1;
        end
      end

      WAIT_REQ_LOW: begin
        cdc_rack_ao = 1'b1;

        if (~cdc_rreq) begin
          resp_state_n = RIDLE;
        end
      end

      default:; // make unique case happy during reset
    endcase
  end

  always_ff @(posedge tck_i, negedge trst_ni) begin
    if (~trst_ni) begin
      req_state_p  <= IDLE;
      resp_state_p <= RIDLE;

      cdc_addr_p   <= '0;
      cdc_we_p     <= '0;
      cdc_be_p     <= '0;
      cdc_wdata_p  <= '0;
      cdc_clear_p  <= '0;
      cdc_req_ao   <= 1'b0;
    end else begin
      req_state_p  <= req_state_n;
      resp_state_p <= resp_state_n;
      cdc_req_ao   <= cdc_req_n;

      if (mem_gnt_o) begin
        cdc_addr_p  <= mem_addr_i;
        cdc_we_p    <= mem_we_i;
        cdc_be_p    <= mem_be_i;
        cdc_wdata_p <= mem_wdata_i;
        cdc_clear_p <= mem_clear_i;
      end
    end
  end

  assign cdc_addr_ao  = cdc_addr_p;
  assign cdc_we_ao    = cdc_we_p;
  assign cdc_be_ao    = cdc_be_p;
  assign cdc_wdata_ao = cdc_wdata_p;
  assign cdc_clear_ao = cdc_clear_p;

  (* ASYNC_REG = "TRUE" *)
  sync i_sync_ack (
      .clk_i     ( tck_i        ),
      .rst_ni    ( trst_ni      ) ,
      .serial_i  ( cdc_ack_ai   ),
      .serial_o  ( cdc_ack      )
  );

  (* ASYNC_REG = "TRUE" *)
  sync i_sync_rreq (
      .clk_i     ( tck_i        ),
      .rst_ni    ( trst_ni      ) ,
      .serial_i  ( cdc_rreq_ai  ),
      .serial_o  ( cdc_rreq     )
  );

  assign mem_rerror_o = cdc_rerror_ai;
  assign mem_rdata_o  = cdc_rdata_ai;

endmodule

module dmi_cdc_mem #(
    parameter int unsigned ADDR_WIDTH = 32,
    parameter int unsigned DATA_WIDTH = 64
)(
    // mem side
    input  logic                    clk_i,
    input  logic                    rst_ni,

    output logic                    mem_req_o,
    input  logic                    mem_gnt_i,
    output logic [ADDR_WIDTH-1:0]   mem_addr_o,
    output logic                    mem_we_o,
    output logic [DATA_WIDTH/8-1:0] mem_be_o,
    output logic [DATA_WIDTH-1:0]   mem_wdata_o,
    input  logic [DATA_WIDTH-1:0]   mem_rdata_i,
    input  logic                    mem_rvalid_i,
    input  logic                    mem_rerror_i,
    output logic                    mem_clear_o,

    // CDC side
    input  logic                    cdc_req_ai,
    output logic                    cdc_ack_ao,
    input  logic [ADDR_WIDTH-1:0]   cdc_addr_ai,
    input  logic                    cdc_we_ai,
    input  logic [DATA_WIDTH/8-1:0] cdc_be_ai,
    input  logic [DATA_WIDTH-1:0]   cdc_wdata_ai,
    input  logic                    cdc_clear_ai,

    output logic                    cdc_rreq_ao,
    input  logic                    cdc_rack_ai,
    output logic [DATA_WIDTH-1:0]   cdc_rdata_ao,
    output logic                    cdc_rerror_ao
  );

  enum logic [1:0] { IDLE, REQUEST, WAIT_REQ_LOW } req_state_p,  req_state_n;
  enum logic [1:0] { RIDLE, WAIT_ACK_HIGH, WAIT_ACK_LOW } resp_state_p, resp_state_n;

  logic [ADDR_WIDTH-1:0]   mem_addr_p;
  logic                    mem_we_p;
  logic [DATA_WIDTH/8-1:0] mem_be_p;
  logic [DATA_WIDTH-1:0]   mem_wdata_p;
  logic                    mem_clear_p;

  logic                    cdc_req;
  logic                    cdc_clear;
  logic                    cdc_sample;

  logic                    cdc_rack;
  logic [DATA_WIDTH-1:0]   cdc_rdata_p;
  logic                    cdc_rerror_p;

  logic                    cdc_rreq_n;
  logic                    cdc_ack_n;

  always_comb begin
    req_state_n = req_state_p;

    cdc_ack_n   = 1'b0;
    cdc_sample  = 1'b0;

    mem_req_o   = 1'b0;

    unique case (req_state_p)
      IDLE: begin
        if (cdc_req) begin
          req_state_n = REQUEST;
          cdc_sample  = 1'b1;
        end
      end

      REQUEST: begin
        mem_req_o  = 1'b1;
        cdc_ack_n  = 1'b1;

        if (mem_gnt_i) begin
          req_state_n = WAIT_REQ_LOW;
        end
      end

      WAIT_REQ_LOW: begin
        cdc_ack_n  = 1'b1;

        if (~cdc_req) begin
          req_state_n = IDLE;
        end
      end

      default:; // make unique case happy during reset
    endcase

    if (cdc_clear)
      req_state_n = IDLE;
  end

  always_comb begin
    resp_state_n = resp_state_p;
    cdc_rreq_n  = 1'b0;

    unique case (resp_state_p)
      RIDLE: begin
        if (mem_rvalid_i) begin
          resp_state_n = WAIT_ACK_HIGH;
        end
      end

      WAIT_ACK_HIGH: begin
        cdc_rreq_n = 1'b1;

        if (cdc_rack) begin
          resp_state_n = WAIT_ACK_LOW;
        end
      end

      WAIT_ACK_LOW: begin
        cdc_rreq_n = 1'b0;

        if (~cdc_rack) begin
          resp_state_n = RIDLE;
        end
      end

      default:; // make unique case happy during reset
    endcase

    if (cdc_clear)
      resp_state_n = RIDLE;
  end

  always_ff @(posedge clk_i, negedge rst_ni) begin
    if (~rst_ni) begin
      req_state_p  <= IDLE;
      resp_state_p <= RIDLE;

      mem_addr_p   <= '0;
      mem_we_p     <= '0;
      mem_be_p     <= '0;
      mem_wdata_p  <= '0;
      mem_clear_p  <= '0;

      cdc_rdata_p  <= '0;
      cdc_rerror_p <= '0;
      cdc_rreq_ao  <= 1'b0;
      cdc_ack_ao   <= 1'b0;
    end else begin
      req_state_p  <= req_state_n;
      resp_state_p <= resp_state_n;
      cdc_rreq_ao  <= cdc_rreq_n;
      cdc_ack_ao   <= cdc_ack_n;

      if (cdc_sample) begin
        mem_addr_p  <= cdc_addr_ai;
        mem_we_p    <= cdc_we_ai;
        mem_be_p    <= cdc_be_ai;
        mem_wdata_p <= cdc_wdata_ai;
        mem_clear_p <= cdc_clear_ai;
      end else begin
        mem_clear_p <= '0;
      end

      if (mem_rvalid_i) begin
        cdc_rdata_p  <= mem_rdata_i;
        cdc_rerror_p <= mem_rerror_i;
      end
    end
  end

  assign mem_addr_o  = mem_addr_p;
  assign mem_we_o    = mem_we_p;
  assign mem_be_o    = mem_be_p;
  assign mem_wdata_o = mem_wdata_p;
  assign mem_clear_o = mem_clear_p;

  assign cdc_rdata_ao  = cdc_rdata_p;
  assign cdc_rerror_ao = cdc_rerror_p;

  (* ASYNC_REG = "TRUE" *)
  sync i_sync_req (
      .clk_i     ( clk_i      ),
      .rst_ni    ( rst_ni     ) ,
      .serial_i  ( cdc_req_ai ),
      .serial_o  ( cdc_req    )
  );

  (* ASYNC_REG = "TRUE" *)
  sync i_sync_clear (
      .clk_i     ( clk_i        ),
      .rst_ni    ( rst_ni       ),
      .serial_i  ( cdc_clear_ai ),
      .serial_o  ( cdc_clear    )
  );

  (* ASYNC_REG = "TRUE" *)
  sync i_sync_rack (
      .clk_i     ( clk_i        ),
      .rst_ni    ( rst_ni       ) ,
      .serial_i  ( cdc_rack_ai  ),
      .serial_o  ( cdc_rack     )
  );

  //----------------------------------------------------------------------------
  // Assertions
  //----------------------------------------------------------------------------

`ifndef SYNTHESIS
`ifndef verilator
  assert property (
    @(posedge clk_i) (mem_req_o) |-> (!$isunknown(mem_addr_o) && !$isunknown(mem_we_o)
      && !$isunknown(mem_be_o) && !$isunknown(mem_wdata_o)))
      else $warning("mem request data may never be unknown");

  assert property (
    @(posedge clk_i) (!$isunknown(mem_gnt_i))) else $warning("memory grant may never be unknown");
`endif
`endif
endmodule

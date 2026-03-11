// Copyright 2025 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51
//
// Authors:
// - Enrico Zelioli <ezelioli@iis.ee.ethz.ch>

package cva6tb_rtc_timer_reg_pkg;

  // Internal address width. We only need 5 bits to
  // store the offsets of the registers implemented.
  localparam int unsigned IntAddrWidth = 5;

  // Register offsets
  parameter logic [IntAddrWidth-1:0] CVA6TB_RTC_TIMER_COUNT_LO_OFFSET   = 5'h00;
  parameter logic [IntAddrWidth-1:0] CVA6TB_RTC_TIMER_COUNT_HI_OFFSET   = 5'h04;
  parameter logic [IntAddrWidth-1:0] CVA6TB_RTC_TIMER_COMPARE_LO_OFFSET = 5'h08;
  parameter logic [IntAddrWidth-1:0] CVA6TB_RTC_TIMER_COMPARE_HI_OFFSET = 5'h0C;

endpackage

module cva6tb_rtc_timer #(
  parameter type   reg_req_t = logic,
  parameter type   reg_rsp_t = logic,
  parameter string LOG_FILE  = "timer_events.log"
) (
  input  logic     clk_i,
  input  logic     rst_ni,
  input  logic     rtc_i,
  input  reg_req_t reg_req_i,
  output reg_rsp_t reg_rsp_o,
  output logic [63:0] time_o,
  output logic     irq_o
);

  import cva6tb_rtc_timer_reg_pkg::*;

  // Registers
  logic [63:0]   count_d,    count_q;
  logic [63:0] compare_d,  compare_q;
  logic       rtc_sync_d, rtc_sync_q;

  // Internal signals
  logic        inc;
  logic        error;
  logic [31:0] rdata;

  // bit enable mask: defines which bits are written to by wdata of the reg request
  logic [31:0] be_mask;
  for (genvar i = 0; unsigned'(i) < 32/8; ++i ) begin : gen_write_mask
    assign be_mask[8*i +: 8] = {8{reg_req_i.wstrb[i]}};
  end

  // Assignments
  assign inc    = rtc_sync_d & ~rtc_sync_q;
  assign irq_o  = count_q >= compare_q;
  assign time_o = count_q;

  // Log timer events to a CSV file: time_ns,event,value
  // Events: compare_set (new compare value), expired (count reached compare)
  initial begin : timer_logger
    static int unsigned log_fd;
    static logic [63:0] prev_compare = '1; // matches reset value of compare_q
    static logic        prev_irq     = '0;

    log_fd = $fopen(LOG_FILE, "w");
    $fwrite(log_fd, "time_ns,event,value\n");

    wait (rst_ni == 1'b1);
    forever @(posedge clk_i) begin
      if (compare_q !== prev_compare) begin
        $fwrite(log_fd, "%0.0f,compare_set,%0d\n", $realtime, compare_q);
        $display("@%t | [TMR] Timer compare set to %0d", $realtime, compare_q);
      end
      if (irq_o && !prev_irq) begin
        $fwrite(log_fd, "%0.0f,expired,%0d\n", $realtime, count_q);
        $display("@%t | [TMR] Timer expired at count %0d", $realtime, count_q);
      end
      prev_compare = compare_q;
      prev_irq     = irq_o;
    end
  end

  // Sync the RTC signal through a classic multi-stage edge-triggered synchronizer
  sync #(
    .STAGES   ( 2          )
  ) i_sync (
    .clk_i    ( clk_i      ),
    .rst_ni   ( rst_ni     ),
    .serial_i ( rtc_i      ),
    .serial_o ( rtc_sync_d )
  );

  always_comb begin : reg_response
    reg_rsp_o        = '0;
    reg_rsp_o.ready  = 1'b1;
    reg_rsp_o.error  = error;
    reg_rsp_o.rdata  = rdata;
  end

  always_comb begin
    error              = '0;
    rdata              = '0;
    count_d            = count_q;
    compare_d          = compare_q;

    // Reset count when timer expires
    if (inc) count_d = count_q + 1;

    if (reg_req_i.valid) begin

      if (reg_req_i.write) begin : write
        unique case ({reg_req_i.addr[IntAddrWidth-1:2], 2'b00})
          CVA6TB_RTC_TIMER_COMPARE_LO_OFFSET: begin
            compare_d[31:0] = (compare_q[31:0] & ~be_mask) | (reg_req_i.wdata & be_mask);
          end
          CVA6TB_RTC_TIMER_COMPARE_HI_OFFSET: begin
            compare_d[63:32] = (compare_q[63:32] & ~be_mask) | (reg_req_i.wdata & be_mask);
          end
          default: begin
            error = 1'b1;
          end
        endcase

      end else begin : read
        unique case ({reg_req_i.addr[IntAddrWidth-1:2], 2'b00})
          CVA6TB_RTC_TIMER_COUNT_LO_OFFSET: begin
            rdata = count_q[31:0];
          end
          CVA6TB_RTC_TIMER_COUNT_HI_OFFSET: begin
            rdata = count_q[63:32];
          end
          CVA6TB_RTC_TIMER_COMPARE_LO_OFFSET: begin
            rdata = compare_q[31:0];
          end
          CVA6TB_RTC_TIMER_COMPARE_HI_OFFSET: begin
            rdata = compare_q[63:32];
          end
          default: begin
            rdata = 32'hBADCAB1E;
            error = 1'b1;
          end
        endcase
      end

    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (~rst_ni) begin
      count_q    <= '0;
      compare_q  <= '1;
      rtc_sync_q <= '0;
    end else begin
      count_q    <= count_d;
      compare_q  <= compare_d;
      rtc_sync_q <= rtc_sync_d;
    end
  end

endmodule

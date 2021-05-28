// Copyright 2018 ETH Zurich and University of Bologna.
//
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// Fabian Schuiki <fschuiki@iis.ee.ethz.ch>

timeunit 0.1ns/1ps;

module cdc_2phase_tb;

  parameter int UNTIL = 100000;
  parameter bit INJECT_DELAYS = 1;
  parameter bit POST_SYNTHESIS = 0;

  time tck_src = 10ns;
  time tck_dst = 10ns;
  bit src_done = 0;
  bit dst_done = 0;
  bit done;
  assign done = src_done & dst_done;

  // Signals of the design under test.
  logic        src_rst_ni  = 1;
  logic        src_clk_i   = 0;
  logic [31:0] src_data_i  = 0;
  logic        src_valid_i = 0;
  logic        src_ready_o;

  logic        dst_rst_ni  = 1;
  logic        dst_clk_i   = 0;
  logic [31:0] dst_data_o;
  logic        dst_valid_o;
  logic        dst_ready_i = 0;

  // Instantiate the design under test.
  if (POST_SYNTHESIS) begin : g_dut
    cdc_2phase_synth i_dut (.*);
  end else if (INJECT_DELAYS) begin : g_dut
    cdc_2phase_tb_delay_injector #(0.8ns) i_dut (.*);
  end else begin : g_dut
    cdc_2phase #(logic [31:0]) i_dut (.*);
  end

  // Mailbox with expected items on destination side.
  mailbox #(int) dst_mbox = new();
  int num_sent = 0;
  int num_received = 0;
  int num_failed = 0;

  // Clock generators.
  initial begin
    static int num_items, num_clks;
    num_items = 10;
    num_clks = 0;
    #10ns;
    src_rst_ni = 0;
    #10ns;
    src_rst_ni = 1;
    #10ns;
    while (!done) begin
      src_clk_i = 1;
      #(tck_src/2);
      src_clk_i = 0;
      #(tck_src/2);

      // Modulate the clock frequency.
      num_clks++;
      if (num_sent >= num_items && num_clks > 10) begin
        num_items = num_sent + 10;
        num_clks = 0;
        tck_src = $urandom_range(1000, 10000) * 1ps;
        assert(tck_src > 0);
      end
    end
  end

  initial begin
    static int num_items, num_clks;
    num_items = 10;
    num_clks = 0;
    #10ns;
    dst_rst_ni = 0;
    #10ns;
    dst_rst_ni = 1;
    #10ns;
    while (!done) begin
      dst_clk_i = 1;
      #(tck_dst/2);
      dst_clk_i = 0;
      #(tck_dst/2);

      // Modulate the clock frequency.
      num_clks++;
      if (num_received >= num_items && num_clks > 10) begin
        num_items = num_received + 10;
        num_clks = 0;
        tck_dst = $urandom_range(1000, 10000) * 1ps;
        assert(tck_dst > 0);
      end
    end
  end

  // Source side sender.
  task src_cycle_start;
    #(tck_src*0.8);
  endtask

  task src_cycle_end;
    @(posedge src_clk_i);
  endtask

  initial begin
    @(negedge src_rst_ni);
    @(posedge src_rst_ni);
    repeat(3) @(posedge src_clk_i);
    for (int i = 0; i < UNTIL; i++) begin
      static integer stimulus;
      stimulus = $random();
      src_data_i  <= #(tck_src*0.2) stimulus;
      src_valid_i <= #(tck_src*0.2) 1;
      dst_mbox.put(stimulus);
      num_sent++;
      src_cycle_start();
      while (!src_ready_o) begin
        src_cycle_end();
        src_cycle_start();
      end
      src_cycle_end();
      src_valid_i <= #(tck_src*0.2) 0;
    end
    src_done = 1;
  end

  // Destination side receiver.
  task dst_cycle_start;
    #(tck_dst*0.8);
  endtask

  task dst_cycle_end;
    @(posedge dst_clk_i);
  endtask

  initial begin
    @(negedge dst_rst_ni);
    @(posedge dst_rst_ni);
    repeat(3) @(posedge dst_clk_i);
    while (!src_done || dst_mbox.num() > 0) begin
      static integer expected, actual;
      static int cooldown;
      dst_ready_i <= #(tck_dst*0.2) 1;
      dst_cycle_start();
      while (!dst_valid_o) begin
        dst_cycle_end();
        dst_cycle_start();
      end
      actual = dst_data_o;
      num_received++;
      if (dst_mbox.num() == 0) begin
        $error("unexpected transaction: data=%0h", actual);
        num_failed++;
      end else begin
        dst_mbox.get(expected);
        if (actual != expected) begin
          $error("transaction mismatch: exp=%0h, act=%0h", expected, actual);
          num_failed++;
        end
      end
      dst_cycle_end();
      dst_ready_i <= #(tck_dst*0.2) 0;

      // Insert a random cooldown period.
      cooldown = $urandom_range(0, 40);
      if (cooldown < 20) repeat(cooldown) @(posedge dst_clk_i);
    end

    if (num_sent != num_received) begin
      $error("%0d items sent, but %0d items received", num_sent, num_received);
    end
    if (num_failed > 0) begin
      $error("%0d/%0d items mismatched", num_failed, num_sent);
    end else begin
      $info("%0d items passed", num_sent);
    end

    dst_done = 1;
  end

endmodule


module cdc_2phase_tb_delay_injector #(
  parameter time MAX_DELAY = 0ns
)(
  input  logic        src_rst_ni,
  input  logic        src_clk_i,
  input  logic [31:0] src_data_i,
  input  logic        src_valid_i,
  output logic        src_ready_o,

  input  logic        dst_rst_ni,
  input  logic        dst_clk_i,
  output logic [31:0] dst_data_o,
  output logic        dst_valid_o,
  input  logic        dst_ready_i
);

  logic async_req_o, async_req_i;
  logic async_ack_o, async_ack_i;
  logic [31:0] async_data_o, async_data_i;

  always @(async_req_o) begin
    automatic time d = $urandom_range(0, MAX_DELAY);
    async_req_i <= #d async_req_o;
  end

  always @(async_ack_o) begin
    automatic time d = $urandom_range(0, MAX_DELAY);
    async_ack_i <= #d async_ack_o;
  end

  for (genvar i = 0; i < 32; i++) begin
    always @(async_data_o[i]) begin
      automatic time d = $urandom_range(0, MAX_DELAY);
      async_data_i[i] <= #d async_data_o[i];
    end
  end

  cdc_2phase_src #(logic [31:0]) i_src (
    .rst_ni       ( src_rst_ni   ),
    .clk_i        ( src_clk_i    ),
    .data_i       ( src_data_i   ),
    .valid_i      ( src_valid_i  ),
    .ready_o      ( src_ready_o  ),
    .async_req_o  ( async_req_o  ),
    .async_ack_i  ( async_ack_i  ),
    .async_data_o ( async_data_o )
  );

  cdc_2phase_dst #(logic [31:0]) i_dst (
    .rst_ni       ( dst_rst_ni   ),
    .clk_i        ( dst_clk_i    ),
    .data_o       ( dst_data_o   ),
    .valid_o      ( dst_valid_o  ),
    .ready_i      ( dst_ready_i  ),
    .async_req_i  ( async_req_i  ),
    .async_ack_o  ( async_ack_o  ),
    .async_data_i ( async_data_i )
  );

endmodule

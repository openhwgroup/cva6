// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// Fabian Schuiki <fschuiki@iis.ee.ethz.ch>

`include "axi/assign.svh"

module tb_axi_lite_xbar;

  parameter AW = 32;
  parameter DW = 32;
  parameter IW = 8;
  parameter UW = 8;

  parameter NUM_MASTER       = 2;
  parameter NUM_SLAVE        = 2;
  parameter NUM_TRANSACTIONS = 1000;

  localparam tCK = 1ns;

  logic clk = 0;
  logic rst = 1;

  AXI_LITE_DV #(
    .AXI_ADDR_WIDTH(AW),
    .AXI_DATA_WIDTH(DW)
  ) master_dv [0:NUM_MASTER-1](clk);

  AXI_LITE #(
    .AXI_ADDR_WIDTH(AW),
    .AXI_DATA_WIDTH(DW)
  ) master [0:NUM_MASTER-1]();

  for (genvar i = 0; i < NUM_MASTER; i++) begin: gen_conn_dv_masters
    `AXI_LITE_ASSIGN(master[i], master_dv[i]);
  end

  AXI_LITE_DV #(
    .AXI_ADDR_WIDTH(AW),
    .AXI_DATA_WIDTH(DW)
  ) slave_dv [0:NUM_SLAVE-1](clk);

  AXI_LITE #(
    .AXI_ADDR_WIDTH(AW),
    .AXI_DATA_WIDTH(DW)
  ) slave [0:NUM_SLAVE-1]();

  for (genvar i = 0; i < NUM_SLAVE; i++) begin: gen_conn_dv_slaves
    `AXI_LITE_ASSIGN(slave_dv[i], slave[i]);
  end

  AXI_ROUTING_RULES #(
    .AXI_ADDR_WIDTH(AW),
    .NUM_SLAVE(NUM_SLAVE),
    .NUM_RULES(1)
  ) routing();

  localparam int SLAVE_SHIFT = (AW-$clog2(NUM_SLAVE));
  for (genvar i = 0; i < NUM_SLAVE; i++) begin
    logic [AW-1:0] addr = i;
    assign routing.rules[i][0].enabled = 1;
    assign routing.rules[i][0].mask    = '1 << SLAVE_SHIFT;
    assign routing.rules[i][0].base    = addr << SLAVE_SHIFT;
  end

  axi_lite_xbar #(
    .ADDR_WIDTH(AW),
    .DATA_WIDTH(DW),
    .NUM_MASTER(NUM_MASTER),
    .NUM_SLAVE(NUM_SLAVE),
    .NUM_RULES(1)
  ) i_dut (
    .clk_i  ( clk     ),
    .rst_ni ( rst     ),
    .master ( master  ),
    .slave  ( slave   ),
    .rules  ( routing )
  );

  // Define the transaction queues.
  class transaction_t;
    rand logic [AW-1:0] addr;
    rand logic [DW-1:0] data;
    rand logic [DW/8-1:0] strb;
    axi_pkg::resp_t resp;
  endclass

  typedef axi_test::axi_lite_driver #(
    .AW(AW),
    .DW(DW),
    .TA(0.2*tCK),
    .TT(0.8*tCK)
  ) driver_t;

  // Randomly block for a few clock cycles.
  task random_delay;
    automatic int i;
    i = $urandom_range(0, 50);
    if (i > 5) return;
    repeat (i) @(posedge clk);
  endtask

  // Setup a queue for reads and writes for each slave.
  transaction_t queue_rd [NUM_SLAVE][$];
  transaction_t queue_wr [NUM_SLAVE][$];
  mailbox mailbox_rd [NUM_SLAVE];
  mailbox mailbox_wr [NUM_SLAVE];
  int tests_total = 0;
  int tests_failed = 0;

  // Initialize the master driver processes.
  logic [NUM_MASTER-1:0] master_done = '0;
  assign done = &master_done;
  for (genvar i = 0; i < NUM_MASTER; i++) initial begin : g_master
    // Initialize and reset the driver.
    static driver_t drv = new(master_dv[i]);
    drv.reset_master();
    repeat(2) @(posedge clk);

    // Fork off multiple processes that will issue transactions on the read
    // and write paths.
    fork
      for (int k = 0; k < NUM_TRANSACTIONS; k++) begin : t_read
        static transaction_t t;
        static logic [DW-1:0] data;
        static axi_pkg::resp_t resp;
        t = new();
        do begin
          automatic int rand_success = t.randomize();
          assert(rand_success);
        end while ((t.addr >> SLAVE_SHIFT) >= NUM_SLAVE);
        t.resp = axi_pkg::RESP_OKAY;
        random_delay();
        drv.send_ar(t.addr);
        // queue_rd[t.addr >> SLAVE_SHIFT].push_back(t);
        mailbox_rd[t.addr >> SLAVE_SHIFT].put(t);
        random_delay();
        drv.recv_r(data, resp);
        tests_total++;
        if (t.data != data || t.resp != resp) begin
          tests_failed++;
          $info("MISMATCH: master [%0d] read, data exp=%h act=%h, resp exp=%h act=%h",
            i, t.data, data, t.resp, resp
          );
        end
      end
      for (int k = 0; k < NUM_TRANSACTIONS; k++) begin : t_write
        static transaction_t t;
        static axi_pkg::resp_t resp;
        t = new();
        do begin
          automatic int rand_success = t.randomize();
          assert(rand_success);
        end while ((t.addr >> SLAVE_SHIFT) >= NUM_SLAVE);
        t.resp = axi_pkg::RESP_OKAY;
        random_delay();
        drv.send_aw(t.addr);
        // queue_wr[t.addr >> SLAVE_SHIFT].push_back(t);
        mailbox_wr[t.addr >> SLAVE_SHIFT].put(t);
        random_delay();
        drv.send_w(t.data, t.strb);
        random_delay();
        drv.recv_b(resp);
        tests_total++;
        if (t.resp != resp) begin
          tests_failed++;
          $info("MISMATCH: master [%0d] write, resp exp=%h act=%h",
            i, t.resp, resp
          );
        end
      end
    join

    repeat(2) @(posedge clk);
    master_done[i] = 1;
  end

  // Initialize the slave driver processes.
  for (genvar i = 0; i < NUM_SLAVE; i++) initial begin : g_slave
    // Initialize and reset the driver.
    static driver_t drv = new(slave_dv[i]);
    drv.reset_slave();
    mailbox_rd[i] = new();
    mailbox_wr[i] = new();
    @(posedge clk);

    // Fork off mulitple processes that will respond to transactions on the read
    // and write paths.
    fork
      while (!done) begin : t_read
        static transaction_t t;
        static logic [AW-1:0] addr;
        random_delay();
        drv.recv_ar(addr);
        // t = queue_rd[i].pop_front();
        mailbox_rd[i].get(t);
        random_delay();
        drv.send_r(t.data, t.resp);
        tests_total++;
        if (t.addr != addr) begin
          tests_failed++;
          $info("MISMATCH: slave [%0d] read, addr exp=%h act=%h",
            i, t.addr, addr
          );
        end
      end
      while (!done) begin : t_write
        static transaction_t t;
        static logic [AW-1:0] addr;
        static logic [DW-1:0] data;
        static logic [DW/8-1:0] strb;
        random_delay();
        drv.recv_aw(addr);
        // t = queue_wr[i].pop_front();
        mailbox_wr[i].get(t);
        random_delay();
        drv.recv_w(data, strb);
        random_delay();
        drv.send_b(t.resp);
        tests_total++;
        if (t.addr != addr || t.data != data || t.strb != strb) begin
          tests_failed++;
          $info("MISMATCH: slave [%0d] write, addr exp=%h act=%h, data exp=%h act=%h, strb exp=%h act=%h",
            i, t.addr, addr, t.data, data, t.strb, strb
          );
        end
      end
    join
  end

  // Clock and reset generator.
  initial begin
    static int cycle = 0;
    #tCK;
    rst <= 0;
    #tCK;
    rst <= 1;
    #tCK;
    while (!done) begin
      clk <= 1;
      #(tCK/2);
      clk <= 0;
      #(tCK/2);
      if (cycle >= 1000000)
        $fatal(1, "timeout at %t", $time);
      cycle++;
    end

    if (tests_failed == 0)
      $info("ALL %0d TESTS PASSED", tests_total);
    else
      $error("%0d / %0d TESTS FAILED", tests_failed, tests_total);
  end

endmodule

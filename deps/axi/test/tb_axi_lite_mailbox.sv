// Copyright (c) 2020 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Author: Wolfgang Roenninger <wroennin@ethz.ch>

// Directed Verification Testbench for `axi_lite_mailbox`.
// - On port 0 all registers get read and the expected results asserted.
// - Read from an empty read FIFO on Port 0 and clear its interrupt
// - Request some data from the other port.
//    - Port 0 sends one data_t to the other and sets its read threshold and waits until
//      port 1 fills the FIFO to a certain value. Port one waits for its interrupt, sets a
//      write threshold and fills the FIFO, until it reaches it. While the FIFO is filling,
//      port 0 starts emptying the read FIFO, however is slower than port 1 pushing, as port
//      0 checks if the FIFO is empty. Port 1 stops sending, when the interrupt for its write
//      threshold is recieved. Port 0 empties the FIFO completely and resets its read interrupt.
// - Port 0 flushes both FIFOs
// - Port 0 enables error interrupt and pushes data until the FIFO errors, then clears it by
//   flushing the FIFOs and reading the `ERROR` register.
// - Port 0 makes an unmapped read and write access, and some targeted accesses to get the branch
//   coverage to 96.25%, the not taken branches have to do with the stalling
//   capabilities of the slave, when the response path is not ready.
// Each of these tests has the respective AXI Lite transaction asserted in the expected output.
// Simulation end tells the number of failed assertions.

`include "axi/typedef.svh"
`include "axi/assign.svh"

module tb_axi_lite_mailbox;
  // timing parameters
  localparam time CyclTime = 10ns;
  localparam time ApplTime =  2ns;
  localparam time TestTime =  8ns;
  // axi configuration
  localparam int unsigned AxiAddrWidth      =  32'd32;    // Axi Address Width
  localparam int unsigned AxiDataWidth      =  32'd64;    // Axi Data Width

  // mailbox params
  localparam int unsigned MailboxDepth = 32'd16;

  typedef logic [AxiAddrWidth-1:0] addr_t; // for sign extension
  typedef logic [AxiDataWidth-1:0] data_t; // for sign extension

  typedef enum addr_t {
    MBOXW  = addr_t'(0 * AxiDataWidth/8),
    MBOXR  = addr_t'(1 * AxiDataWidth/8),
    STATUS = addr_t'(2 * AxiDataWidth/8),
    ERROR  = addr_t'(3 * AxiDataWidth/8),
    WIRQT  = addr_t'(4 * AxiDataWidth/8),
    RIRQT  = addr_t'(5 * AxiDataWidth/8),
    IRQS   = addr_t'(6 * AxiDataWidth/8),
    IRQEN  = addr_t'(7 * AxiDataWidth/8),
    IRQP   = addr_t'(8 * AxiDataWidth/8),
    CTRL   = addr_t'(9 * AxiDataWidth/8)
  } reg_addr_e;

  typedef axi_test::rand_axi_lite_master #(
    // AXI interface parameters
    .AW ( AxiAddrWidth        ),
    .DW ( AxiDataWidth        ),
    // Stimuli application and test time
    .TA ( ApplTime            ),
    .TT ( TestTime            ),
    .MIN_ADDR ( 32'h0000_0000 ),
    .MAX_ADDR ( 32'h0001_3000 ),
    .MAX_READ_TXNS  ( 10 ),
    .MAX_WRITE_TXNS ( 10 )
  ) rand_lite_master_t;

  // -------------
  // DUT signals
  // -------------
  logic       clk;
  // DUT signals
  logic       rst_n;
  logic [1:0] end_of_sim;

  logic [1:0] irq;

  int unsigned test_failed [1:0];

  // -------------------------------
  // AXI Interfaces
  // -------------------------------
  AXI_LITE #(
    .AXI_ADDR_WIDTH ( AxiAddrWidth      ),
    .AXI_DATA_WIDTH ( AxiDataWidth      )
  ) master [1:0] ();
  AXI_LITE_DV #(
    .AXI_ADDR_WIDTH ( AxiAddrWidth      ),
    .AXI_DATA_WIDTH ( AxiDataWidth      )
  ) master_dv [1:0] (clk);
  for (genvar i = 0; i < 2; i++) begin : gen_conn_dv_masters
    `AXI_LITE_ASSIGN           ( master[i],      master_dv[i]    )
  end

  // Masters control simulation run time
  initial begin : proc_master_0
    automatic rand_lite_master_t lite_axi_master = new ( master_dv[0], "MST_0");
    automatic data_t          data = '0;
    automatic axi_pkg::resp_t resp = axi_pkg::RESP_SLVERR;
    // automatic int unsigned    test_failed[0] = 0;
    automatic int unsigned    loop        = 0;
    end_of_sim[0] <= 1'b0;
    lite_axi_master.reset();
    @(posedge rst_n);

    // -------------------------------
    // Read all registers anf compare their results
    // -------------------------------
    $info("Initial test by reading each register");
    $display("%0t MST_0> Read register MBOXW ", $time());
    lite_axi_master.read(MBOXW, data, resp);
    assert (data == data_t'(32'hFEEDC0DE)) else begin test_failed[0]++; $error("Unexpected result"); end
    assert (resp == axi_pkg::RESP_OKAY) else begin test_failed[0]++; $error("Unexpected result"); end

    $display("%0t MST_0> Read register MBOXR, this generates an error ", $time());
    lite_axi_master.read(MBOXR, data, resp);
    assert (data == data_t'(32'hFEEDDEAD)) else begin test_failed[0]++; $error("Unexpected result"); end
    assert (resp == axi_pkg::RESP_SLVERR) else begin test_failed[0]++; $error("Unexpected result"); end

    $display("%0t MST_0> Read register STATUS", $time());
    lite_axi_master.read(STATUS, data, resp);
    assert (data == data_t'(1)) else begin test_failed[0]++; $error("Unexpected result"); end
    assert (resp == axi_pkg::RESP_OKAY) else begin test_failed[0]++; $error("Unexpected result"); end

    $display("%0t MST_0> Read register ERROR ", $time());
    lite_axi_master.read(ERROR, data, resp);
    assert (data == data_t'(1)) else begin test_failed[0]++; $error("Unexpected result"); end
    assert (resp == axi_pkg::RESP_OKAY) else begin test_failed[0]++; $error("Unexpected result"); end

    $display("%0t MST_0> Read register WIRQT ", $time());
    lite_axi_master.read(WIRQT, data, resp);
    assert (data == data_t'(0)) else begin test_failed[0]++; $error("Unexpected result"); end
    assert (resp == axi_pkg::RESP_OKAY) else begin test_failed[0]++; $error("Unexpected result"); end

    $display("%0t MST_0> Read register RIRQT ", $time());
    lite_axi_master.read(RIRQT, data, resp);
    assert (data == data_t'(0)) else begin test_failed[0]++; $error("Unexpected result"); end
    assert (resp == axi_pkg::RESP_OKAY) else begin test_failed[0]++; $error("Unexpected result"); end

    $display("%0t MST_0> Read register IRQS  ", $time());
    lite_axi_master.read(IRQS, data, resp);
    assert (data == data_t'(3'b100)) else begin test_failed[0]++; $error("Unexpected result"); end
    assert (resp == axi_pkg::RESP_OKAY) else begin test_failed[0]++; $error("Unexpected result"); end

    $display("%0t MST_0> Acknowledge Error by writing to IRQS", $time());
    lite_axi_master.write(IRQS, 64'h4, 8'hFF, resp);
    assert (resp == axi_pkg::RESP_OKAY) else begin test_failed[0]++; $error("Unexpected result"); end

    $display("%0t MST_0> Read register IRQEN ", $time());
    lite_axi_master.read(IRQEN, data, resp);
    assert (data == data_t'(0)) else begin test_failed[0]++; $error("Unexpected result"); end
    assert (resp == axi_pkg::RESP_OKAY) else begin test_failed[0]++; $error("Unexpected result"); end

    $display("%0t MST_0> Read register IRQP  ", $time());
    lite_axi_master.read(IRQP, data, resp);
    assert (data == data_t'(0)) else begin test_failed[0]++; $error("Unexpected result"); end
    assert (resp == axi_pkg::RESP_OKAY) else begin test_failed[0]++; $error("Unexpected result"); end

    $display("%0t MST_0> Read register CTRL  ", $time());
    lite_axi_master.read(CTRL, data, resp);
    assert (data == data_t'(0)) else begin test_failed[0]++; $error("Unexpected result"); end
    assert (resp == axi_pkg::RESP_OKAY) else begin test_failed[0]++; $error("Unexpected result"); end

    // -------------------------------
    // Test Read error interrupt on port 0
    // -------------------------------
    repeat (50) @(posedge clk);
    $info("Test error interrupt");
    $display("%0t MST_0> Enable Error interrupt  ", $time());
    lite_axi_master.write(IRQEN, data_t'(3'b100), 8'hFF, resp);
    assert (resp == axi_pkg::RESP_OKAY) else begin test_failed[0]++; $error("Unexpected result"); end

    $display("%0t MST_0> Read register MBOXR, this generates an error ", $time());
    lite_axi_master.read(MBOXR, data, resp);
    assert (data == data_t'(32'hFEEDDEAD)) else begin test_failed[0]++; $error("Unexpected result"); end
    assert (resp == axi_pkg::RESP_SLVERR) else begin test_failed[0]++; $error("Unexpected result"); end

    $display("%0t MST_0> Read register ERROR ", $time());
    lite_axi_master.read(ERROR, data, resp);
    assert (data == data_t'(1)) else begin test_failed[0]++; $error("Unexpected result"); end
    assert (resp == axi_pkg::RESP_OKAY) else begin test_failed[0]++; $error("Unexpected result"); end

    $display("%0t MST_0> Acknowledge Error by writing to IRQS", $time());
    lite_axi_master.write(IRQS, data_t'(3'b100), 8'hFF, resp);
    assert (resp == axi_pkg::RESP_OKAY) else begin test_failed[0]++; $error("Unexpected result"); end

    $display("%0t MST_0> Disable interrupt", $time());
    lite_axi_master.write(IRQEN, data_t'(0), 8'hFF, resp);
    assert (resp == axi_pkg::RESP_OKAY) else begin test_failed[0]++; $error("Unexpected result"); end

    // -------------------------------
    // Send data to the other port, and enable interrupt for recieving
    // -------------------------------
    repeat (50) @(posedge clk);
    $info("Test sending data from one to the other slave interface");
    $display("%0t MST_0> Set write threshold to 100, truncates to depth ", $time());
    lite_axi_master.write(WIRQT, 64'd100, 8'hFF, resp);
    assert (resp == axi_pkg::RESP_OKAY) else begin test_failed[0]++; $error("Unexpected result"); end

    $display("%0t MST_0> Read out write threshold ", $time());
    lite_axi_master.read(WIRQT, data, resp);
    assert (data == data_t'(MailboxDepth - 1)) else begin test_failed[0]++; $error("Unexpected result"); end
    assert (resp == axi_pkg::RESP_OKAY) else begin test_failed[0]++; $error("Unexpected result"); end

    $display("%0t MST_0> Set write threshold to 0", $time());
    lite_axi_master.write(WIRQT, 64'd0, 8'hFF, resp);
    assert (resp == axi_pkg::RESP_OKAY) else begin test_failed[0]++; $error("Unexpected result"); end


    $display("%0t MST_0> Set Read threshold to 100, truncates to depth ", $time());
    lite_axi_master.write(RIRQT, 64'd100, 8'hFF, resp);
    assert (resp == axi_pkg::RESP_OKAY) else begin test_failed[0]++; $error("Unexpected result"); end

    $display("%0t MST_0> Read out read threshold ", $time());
    lite_axi_master.read(RIRQT, data, resp);
    assert (data == data_t'(MailboxDepth - 1)) else begin test_failed[0]++; $error("Unexpected result"); end
    assert (resp == axi_pkg::RESP_OKAY) else begin test_failed[0]++; $error("Unexpected result"); end

    $display("%0t MST_0> Set Read threshold to 64'd2 ", $time());
    lite_axi_master.write(RIRQT, 64'd2, 8'hFF, resp);
    assert (resp == axi_pkg::RESP_OKAY) else begin test_failed[0]++; $error("Unexpected result"); end

    $display("%0t MST_0> Enable Read threshold interrupt  ", $time());
    lite_axi_master.write(IRQEN, 64'h2, 8'hFF, resp);
    assert (resp == axi_pkg::RESP_OKAY) else begin test_failed[0]++; $error("Unexpected result"); end

    $display("%0t MST_0> Send to slave 1 data  ", $time());
    lite_axi_master.write(MBOXW, data_t'(32'hFEEDFEED), 8'hFF, resp);
    assert (resp == axi_pkg::RESP_OKAY) else begin test_failed[0]++; $error("Unexpected result"); end

    // wait for interrupt
    wait (irq[0]);
    $display("%0t MST_0> interrupt recieved, test that it is the expected one  ", $time());
    lite_axi_master.read(IRQP, data, resp);
    assert (data == data_t'(3'b010)) else begin test_failed[0]++; $error("Unexpected result"); end
    assert (resp == axi_pkg::RESP_OKAY) else begin test_failed[0]++; $error("Unexpected result"); end
    lite_axi_master.read(STATUS, data, resp);
    assert (data == data_t'(4'b1000)) else begin test_failed[0]++; $error("Unexpected result"); end
    assert (resp == axi_pkg::RESP_OKAY) else begin test_failed[0]++; $error("Unexpected result"); end
    $display("%0t MST_0> empty data from port  ", $time());
    while (!data[0]) begin
      lite_axi_master.read(MBOXR, data, resp);
      assert (data == data_t'(loop)) else begin test_failed[0]++; $error("Unexpected result"); end
      assert (resp == axi_pkg::RESP_OKAY) else begin test_failed[0]++; $error("Unexpected result"); end
      loop ++;
      lite_axi_master.read(STATUS, data, resp);
    end
    $display("%0t MST_0> FIFO is now empty, clear interrupt and disable it  ", $time());
    lite_axi_master.write(IRQS, data_t'(3'b111), 8'hFF, resp);
    lite_axi_master.write(IRQEN, data_t'(0), 8'hFF, resp);
    lite_axi_master.write(RIRQT, data_t'(0), 8'hFF, resp);

    // -------------------------------
    // Test Flush
    // -------------------------------
    repeat (50) @(posedge clk);
    $info("%0t MST_0> Test Flush all FIFOs  ", $time());
    lite_axi_master.write(CTRL, data_t'('1), 8'h00, resp);
    assert (resp == axi_pkg::RESP_OKAY) else begin test_failed[0]++; $error("Unexpected result"); end

    lite_axi_master.write(CTRL, data_t'('1), 8'hFF, resp);
    assert (resp == axi_pkg::RESP_OKAY) else begin test_failed[0]++; $error("Unexpected result"); end

    // -------------------------------
    // Fill the write FIFO, until write error interrupt, then flush and clear interrupt
    // -------------------------------
    repeat (50) @(posedge clk);
    $info("%0t MST_0> Test Write error interrupt  ", $time());
    lite_axi_master.write(IRQEN, data_t'(3'b100), 8'hFF, resp);
    loop = 0;
    while (!irq[0]) begin
      lite_axi_master.write(MBOXW, data_t'(loop), 8'hFF, resp);
    end
    lite_axi_master.read(IRQP, data, resp);
    assert (data == data_t'(3'b100)) else begin test_failed[0]++; $error("Unexpected result"); end
    assert (resp == axi_pkg::RESP_OKAY) else begin test_failed[0]++; $error("Unexpected result"); end
    lite_axi_master.read(ERROR, data, resp);
    assert (data == data_t'(2'b10)) else begin test_failed[0]++; $error("Unexpected result"); end
    assert (resp == axi_pkg::RESP_OKAY) else begin test_failed[0]++; $error("Unexpected result"); end
    lite_axi_master.write(CTRL, data_t'(2'b01), 8'h01, resp);
    assert (resp == axi_pkg::RESP_OKAY) else begin test_failed[0]++; $error("Unexpected result"); end
    lite_axi_master.write(IRQS, data_t'(3'b111), 8'h01, resp);
    assert (resp == axi_pkg::RESP_OKAY) else begin test_failed[0]++; $error("Unexpected result"); end
    lite_axi_master.read(STATUS, data, resp);
    assert (data == data_t'(4'b0001)) else begin test_failed[0]++; $error("Unexpected result"); end
    assert (resp == axi_pkg::RESP_OKAY) else begin test_failed[0]++; $error("Unexpected result"); end

    // -------------------------------
    // Make an unmapped read and write access
    // -------------------------------
    repeat (50) @(posedge clk);
    $info("%0t MST_0> Make an unmapped access read and write ", $time());
    lite_axi_master.read(addr_t'(16'hDEAD), data, resp);
    assert (resp == axi_pkg::RESP_SLVERR) else begin test_failed[0]++; $error("Unexpected result"); end
    lite_axi_master.write(addr_t'(16'hDEAD), data_t'(16'hDEAD), 8'hFF, resp);
    assert (resp == axi_pkg::RESP_SLVERR) else begin test_failed[0]++; $error("Unexpected result"); end
    lite_axi_master.write(ERROR, data_t'(16'hDEAD), 8'hFF, resp);
    assert (resp == axi_pkg::RESP_SLVERR) else begin test_failed[0]++; $error("Unexpected result"); end
    lite_axi_master.write(IRQEN, data_t'(16'hDEAD), 8'h00, resp);
    assert (resp == axi_pkg::RESP_OKAY) else begin test_failed[0]++; $error("Unexpected result"); end
    lite_axi_master.write(IRQS, data_t'(16'hDEAD), 8'h00, resp);
    assert (resp == axi_pkg::RESP_OKAY) else begin test_failed[0]++; $error("Unexpected result"); end
    lite_axi_master.write(WIRQT, data_t'('1), 8'h00, resp);
    assert (resp == axi_pkg::RESP_OKAY) else begin test_failed[0]++; $error("Unexpected result"); end
    lite_axi_master.write(WIRQT, data_t'('1), 8'hFF, resp);
    assert (resp == axi_pkg::RESP_OKAY) else begin test_failed[0]++; $error("Unexpected result"); end
    lite_axi_master.write(WIRQT, data_t'('0), 8'hFF, resp);
    assert (resp == axi_pkg::RESP_OKAY) else begin test_failed[0]++; $error("Unexpected result"); end
    lite_axi_master.write(RIRQT, data_t'('1), 8'h00, resp);
    assert (resp == axi_pkg::RESP_OKAY) else begin test_failed[0]++; $error("Unexpected result"); end
    lite_axi_master.write(RIRQT, data_t'('1), 8'hFF, resp);
    assert (resp == axi_pkg::RESP_OKAY) else begin test_failed[0]++; $error("Unexpected result"); end
    lite_axi_master.write(WIRQT, data_t'('0), 8'hFF, resp);
    assert (resp == axi_pkg::RESP_OKAY) else begin test_failed[0]++; $error("Unexpected result"); end

    end_of_sim[0] <= 1'b1;
  end

  initial begin : proc_master_1
    automatic rand_lite_master_t lite_axi_master = new ( master_dv[1], "MST_1");
    //automatic int unsigned    test_failed = 0;
    automatic data_t          data        = '0;
    automatic axi_pkg::resp_t resp        = axi_pkg::RESP_SLVERR;
    automatic int unsigned    loop        = 0;
    end_of_sim[1] <= 1'b0;
    lite_axi_master.reset();
    @(posedge rst_n);

    // -------------------------------
    // Test Flush seperately
    // -------------------------------
    $display("%0t MST_1> Flush Read MBOX ", $time());
    lite_axi_master.write(CTRL, data_t'(2'b10), 8'hFF, resp);
    assert (resp == axi_pkg::RESP_OKAY) else begin test_failed[1]++; $error("Unexpected result"); end

    $display("%0t MST_1> Flush Write MBOX ", $time());
    lite_axi_master.write(CTRL, data_t'(2'b01), 8'hFF, resp);
    assert (resp == axi_pkg::RESP_OKAY) else begin test_failed[1]++; $error("Unexpected result"); end

    // -------------------------------
    // Set read and write thresholds, wait for reflect some data
    // -------------------------------
    $display("%0t MST_1> Set Read threshold to 64'd0 ", $time());
    lite_axi_master.write(RIRQT, data_t'(0), 8'hFF, resp);
    assert (resp == axi_pkg::RESP_OKAY) else begin test_failed[1]++; $error("Unexpected result"); end

    $display("%0t MST_1> Enable Read threshold interrupt  ", $time());
    lite_axi_master.write(IRQEN, data_t'(2), 8'hFF, resp);
    assert (resp == axi_pkg::RESP_OKAY) else begin test_failed[1]++; $error("Unexpected result"); end

    $display("%0t MST_1> Wait for Read threshold interrupt  ", $time());
    wait (irq[1]);
    $display("%0t MST_1> Interrupt Recieved, read pending register and Acknowledge irq ", $time());
    lite_axi_master.read(IRQP, data, resp);
    assert (data == data_t'(2)) else begin test_failed[1]++; $error("Unexpected result"); end
    assert (resp == axi_pkg::RESP_OKAY) else begin test_failed[1]++; $error("Unexpected result"); end
    lite_axi_master.read(IRQS, data, resp);
    assert (data == data_t'(2)) else begin test_failed[1]++; $error("Unexpected result"); end
    assert (resp == axi_pkg::RESP_OKAY) else begin test_failed[1]++; $error("Unexpected result"); end
    lite_axi_master.read(MBOXR, data, resp);
    assert (data == data_t'(32'hFEEDFEED)) else begin test_failed[1]++; $error("Unexpected result"); end
    assert (resp == axi_pkg::RESP_OKAY) else begin test_failed[1]++; $error("Unexpected result"); end
    lite_axi_master.write(IRQS, data_t'(2), 8'h1, resp);
    assert (resp == axi_pkg::RESP_OKAY) else begin test_failed[1]++; $error("Unexpected result"); end

    $display("%0t MST_1> Enable write threshold interrupt ", $time());
    lite_axi_master.write(WIRQT, 32'h8, 8'h1, resp);
    assert (resp == axi_pkg::RESP_OKAY) else begin test_failed[1]++; $error("Unexpected result"); end
    lite_axi_master.write(IRQEN, data_t'(1), 8'hFF, resp);
    assert (resp == axi_pkg::RESP_OKAY) else begin test_failed[1]++; $error("Unexpected result"); end

    $display("%0t MST_1> Write back looping answer ", $time());
    while (!irq[1]) begin
      lite_axi_master.write(MBOXW, data_t'(loop), 8'hFF, resp);
      assert (resp == axi_pkg::RESP_OKAY) else begin test_failed[1]++; $error("Unexpected result"); end
      loop++;
    end
    $display("%0t MST_1> Stop looping answer and clear interrupt", $time());
    lite_axi_master.read(IRQP, data, resp);
    assert (data == data_t'(1)) else begin test_failed[1]++; $error("Unexpected result"); end
    assert (resp == axi_pkg::RESP_OKAY) else begin test_failed[1]++; $error("Unexpected result"); end
    lite_axi_master.read(IRQS, data, resp);
    assert (data == data_t'(1)) else begin test_failed[1]++; $error("Unexpected result"); end
    assert (resp == axi_pkg::RESP_OKAY) else begin test_failed[1]++; $error("Unexpected result"); end
    // clear the interrupt, if the Write FIFO is status reg is below threshold
    lite_axi_master.read(STATUS, data, resp);
    while (data[3]) begin
      repeat (10) @(posedge clk);
      lite_axi_master.read(STATUS, data, resp);
      assert (resp == axi_pkg::RESP_OKAY) else begin test_failed[1]++; $error("Unexpected result"); end
    end
    lite_axi_master.write(IRQS, data_t'(2), 8'h1, resp);
    assert (resp == axi_pkg::RESP_OKAY) else begin test_failed[1]++; $error("Unexpected result"); end
    lite_axi_master.write(IRQEN, data_t'(0), 8'h1, resp);
    assert (resp == axi_pkg::RESP_OKAY) else begin test_failed[1]++; $error("Unexpected result"); end

    end_of_sim[1] <= 1'b1;
  end

  initial begin : proc_monitor_irq_0
    forever begin
      @(posedge irq[0]);
      $info("Recieved interrupt from slave port 0");
    end
  end

  initial begin : proc_monitor_irq_1
    forever begin
      @(posedge irq[1]);
      $info("Recieved interrupt from slave port 1");
    end
  end

  initial begin : proc_stop_sim
    wait (&end_of_sim);
    repeat (50) @(posedge clk);
    $display("Slave port 0 failed tests: %0d", test_failed[0]);
    $display("Slave port 1 failed tests: %0d", test_failed[1]);
    if (test_failed[0] > 0 || test_failed[1] > 0) begin
        $fatal(1, "Simulation stopped as assertion errors have been encountered, Failure!!!");
    end else begin
        $info("Simulation stopped as all Masters transferred their data, Success.",);
    end
    $stop();
  end

  //-----------------------------------
  // Clock generator
  //-----------------------------------
  clk_rst_gen #(
    .CLK_PERIOD    ( CyclTime ),
    .RST_CLK_CYCLES( 5        )
  ) i_clk_gen (
    .clk_o (clk),
    .rst_no(rst_n)
  );

  //-----------------------------------
  // DUT
  //-----------------------------------
  axi_lite_mailbox_intf #(
    .MAILBOX_DEPTH  ( MailboxDepth ),
    .IRQ_EDGE_TRIG  ( 1'b0         ),
    .IRQ_ACT_HIGH   ( 1'b1         ),
    .AXI_ADDR_WIDTH ( AxiAddrWidth ),
    .AXI_DATA_WIDTH ( AxiDataWidth )
  ) i_mailbox_dut (
    .clk_i       ( clk       ),
    .rst_ni      ( rst_n     ),
    .test_i      ( 1'b0      ),
    .slv         ( master    ),
    .irq_o       ( irq       ),
    .base_addr_i ( '0        ) // set base address to '0
  );
endmodule

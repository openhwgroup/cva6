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

/// A set of testbench utilities for AXI interfaces.
package reg_test;

  /// A driver for AXI4-Lite interface.
  class reg_driver #(
    parameter int  AW     ,
    parameter int  DW     ,
    parameter time TA = 0 , // stimuli application time
    parameter time TT = 0   // stimuli test time
  );
    virtual REG_BUS #(
      .ADDR_WIDTH(AW),
      .DATA_WIDTH(DW)
    ) bus;

    function new(
      virtual REG_BUS #(
        .ADDR_WIDTH(AW),
        .DATA_WIDTH(DW)
      ) bus
    );
      this.bus = bus;
    endfunction

    task reset_master;
      bus.addr  <= '0;
      bus.write <= '0;
      bus.wdata <= '0;
      bus.wstrb <= '0;
      bus.valid <= '0;
    endtask

    task reset_slave;
      bus.rdata <= '0;
      bus.error <= '0;
      bus.ready <= '0;
    endtask

    task cycle_start;
      #TT;
    endtask

    task cycle_end;
      @(posedge bus.clk_i);
    endtask

    /// Issue a write transaction.
    task send_write (
      input  logic [AW-1:0] addr,
      input  logic [DW-1:0] data,
      input  logic [DW/8-1:0] strb,
      output logic error
    );
      bus.addr  <= #TA addr;
      bus.write <= #TA 1;
      bus.wdata <= #TA data;
      bus.wstrb <= #TA strb;
      bus.valid <= #TA 1;
      cycle_start();
      while (bus.ready != 1) begin cycle_end(); cycle_start(); end
      error = bus.error;
      cycle_end();
      bus.addr  <= #TA '0;
      bus.write <= #TA 0;
      bus.wdata <= #TA '0;
      bus.wstrb <= #TA '0;
      bus.valid <= #TA 0;
    endtask

    /// Issue a read transaction.
    task send_read (
      input  logic [AW-1:0] addr,
      output logic [DW-1:0] data,
      output logic error
    );
      bus.addr  <= #TA addr;
      bus.write <= #TA 0;
      bus.valid <= #TA 1;
      cycle_start();
      while (bus.ready != 1) begin cycle_end(); cycle_start(); end
      data  = bus.rdata;
      error = bus.error;
      cycle_end();
      bus.addr  <= #TA '0;
      bus.write <= #TA 0;
      bus.valid <= #TA 0;
    endtask

  endclass

endpackage

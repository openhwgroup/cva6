///////////////////////////////////////////////////////////////////////////////
//
// Copyright 2021 OpenHW Group
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     https://solderpad.org/licenses/
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
//
///////////////////////////////////////////////////////////////////////////////
//
// Testharness for the CVA6 core.
//
///////////////////////////////////////////////////////////////////////////////

`ifdef VERILATOR
  // VERILATOR uses tb/cva6_core_tb.cpp to drive the harness.
`else

module cva6_core_tb #(
  parameter int CLK_PERIOD   = 10,
                RESET_CYCLES =  5,
                CLOCK_CYCLES = 20
  )
  ();

  logic clk;
  logic reset_n;

  initial begin
    $timeformat(-9, 3, "ns", 8);
    //$dumpvars(0, cva6_core_tb);
    clk     = 1'b0;
    reset_n = 1'b0;
    fork
      begin
        forever #(CLK_PERIOD/2) clk = ~clk;
      end
      begin
        #0;
        $write("%m @ %0t: reset asserted\n", $time);
        repeat (RESET_CYCLES) @(negedge clk);
        $write("%m @ %0t: reset de-asserted\n", $time);
        reset_n = 1'b1;
      end
      begin
        $write("%m @ %0t: Run for %0d clock cycles\n", $time, CLOCK_CYCLES);
        repeat (CLOCK_CYCLES) @(posedge clk);
        $write("%m @ %0t: finish\n", $time);
        $finish;
      end
    join
  end

  cva6_testharness cva6_th_inst (
                                 .clk_i  (clk),
                                 .rst_ni (reset_n)
                                );
endmodule

`endif //VERILATOR

module cva6_testharness #(
  parameter int unsigned AXI_USER_WIDTH    = 1,
  parameter int unsigned AXI_ADDRESS_WIDTH = 64,
  parameter int unsigned AXI_DATA_WIDTH    = 64,
`ifdef DROMAJO
  parameter bit          InclSimDTM        = 1'b0,
`else
  parameter bit          InclSimDTM        = 1'b1,
`endif
  parameter int unsigned NUM_WORDS         = 2**25,         // memory size
  parameter bit          StallRandomOutput = 1'b0,
  parameter bit          StallRandomInput  = 1'b0
) (
  input  logic                           clk_i,
  input  logic                           rst_ni
//  output logic [31:0]                    exit_o
);

// FIXME: this code block to be removed once the harness is able to drive
//        exit_o and thereby signal to cva6_core_tb (both cpp and sv versions)
//        that the simulation should be terminated.
`ifdef VERILATOR
  integer cnt;

  initial begin
    $write("%m @ %0t: Run for 20 clock cycles\n", $time);
  end

  always @(posedge clk_i) begin
    if (!rst_ni) begin
      cnt <= 0;
    end
    else begin
      cnt <= cnt+1;
      if (cnt > 20) begin
        $write("%m @ %0t: finish\n", $time);
        $finish;
      end
    end
  end
`endif


  // ---------------
  // Core
  // ---------------
  ariane_axi::req_t    axi_cva6_req;
  ariane_axi::resp_t   axi_cva6_resp;

  ariane #(
    .ArianeCfg  ( ariane_soc::ArianeSocCfg )
  ) cv64a6_inst (
    .clk_i                ( clk_i               ),
    .rst_ni               ( rst_ni              ),
    .boot_addr_i          ( ariane_soc::ROMBase ), // start fetching from ROM
    .hart_id_i            ( '0                  ),
    .irq_i                ( 2'b00/*irqs*/       ),
    .ipi_i                ( 1'b0 /*ipi */       ),
    .time_irq_i           ( 1'b0 /*timer_irq*/  ),
    .debug_req_i          ( 1'b0                ),
    .axi_req_o            ( axi_cva6_req      ),
    .axi_resp_i           ( axi_cva6_resp     )
  );

endmodule: cva6_testharness

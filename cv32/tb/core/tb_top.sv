// Copyright 2017 Embecosm Limited <www.embecosm.com>
// Copyright 2018 Robert Balas <balasr@student.ethz.ch>
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Top level wrapper for a RI5CY testbench
// Contributor: Robert Balas <balasr@student.ethz.ch>
//              Jeremy Bennett <jeremy.bennett@embecosm.com>

`define TB_CORE

module tb_top
    #(parameter INSTR_RDATA_WIDTH = 32,
      parameter RAM_ADDR_WIDTH = 22,
      parameter BOOT_ADDR  = 'h80);

    // comment to record execution trace
    //`define TRACE_EXECUTION

    const time CLK_PHASE_HI       = 5ns;
    const time CLK_PHASE_LO       = 5ns;
    const time CLK_PERIOD         = CLK_PHASE_HI + CLK_PHASE_LO;
    const time STIM_APPLICATION_DEL = CLK_PERIOD * 0.1;
    const time RESP_ACQUISITION_DEL = CLK_PERIOD * 0.9;
    const time RESET_DEL = STIM_APPLICATION_DEL;
    const int  RESET_WAIT_CYCLES  = 4;


    // clock and reset for tb
    logic                   core_clk;
    logic                   iss_clk;
    logic                   core_rst_n;

    // cycle counter
    int unsigned            cycle_cnt_q;

    // testbench result
    logic                   tests_passed;
    logic                   tests_failed;
    logic                   exit_valid;
    logic [31:0]            exit_value;

    // signals for ri5cy
    logic                   fetch_enable;

    // make the core start fetching instruction immediately
    assign fetch_enable = '1;

    // allow vcd dump
    initial begin
        if ($test$plusargs("vcd")) begin
            $dumpfile("riscy_tb.vcd");
            $dumpvars(0, tb_top);
        end
    end

    // we either load the provided firmware or execute a small test program that
    // doesn't do more than an infinite loop with some I/O
    initial begin: load_prog
        automatic string firmware;
        automatic int prog_size = 6;

        if($value$plusargs("firmware=%s", firmware)) begin
            if($test$plusargs("verbose"))
                $display("[TESTBENCH] @ t=%0t: loading firmware %0s",
                         $time, firmware);
            $readmemh(firmware, cv32e40p_tb_wrapper_i.ram_i.dp_ram_i.mem);
        end else begin
            $display("No firmware specified");
            $finish;
        end
    end

    initial begin: clock_gen
        forever begin
            #CLK_PHASE_HI core_clk = 1'b0;
            #CLK_PHASE_LO core_clk = 1'b1;
        end
    end: clock_gen
   

    // timing format, reset generation and parameter check
    initial begin
        $timeformat(-9, 0, "ns", 9);
        core_rst_n = 1'b0;

        // wait a few cycles
        repeat (RESET_WAIT_CYCLES) begin
            @(posedge core_clk); //TODO: was posedge, see below
        end

        // start running
        #RESET_DEL core_rst_n = 1'b1;

        repeat (3) @(negedge core_clk);
        core_rst_n = 1'b1;

        if($test$plusargs("verbose")) begin
            $display("reset deasserted", $time);
        end

        if ( !( (INSTR_RDATA_WIDTH == 128) || (INSTR_RDATA_WIDTH == 32) ) ) begin
         $fatal(2, "invalid INSTR_RDATA_WIDTH, choose 32 or 128");
        end
    end

    // abort after n cycles, if we want to
    always_ff @(posedge core_clk, negedge core_rst_n) begin
        automatic int maxcycles;
        if($value$plusargs("maxcycles=%d", maxcycles)) begin
            if (~core_rst_n) begin
                cycle_cnt_q <= 0;
            end else begin
                cycle_cnt_q     <= cycle_cnt_q + 1;
                if (cycle_cnt_q >= maxcycles) begin
                    $fatal(2, "Simulation aborted due to maximum cycle limit");
                end
            end
        end
    end

    // check if we succeded
    always_ff @(posedge core_clk, negedge core_rst_n) begin
        if (tests_passed) begin
            $display("ALL TESTS PASSED");
            $finish;
        end
        if (tests_failed) begin
            $display("TEST(S) FAILED!");
            $finish;
        end
        if (exit_valid) begin
            if (exit_value == 0)
                $display("%m @ %0t: EXIT SUCCESS", $time);
            else
                $display("%m @ %0t: EXIT FAILURE: %d", exit_value, $time);
            $finish;
        end
    end

    // wrapper for CV32E40P, the memory system and stdout peripheral
    cv32e40p_tb_wrapper
        #(
          .INSTR_RDATA_WIDTH (INSTR_RDATA_WIDTH),
          .RAM_ADDR_WIDTH    (RAM_ADDR_WIDTH),
          .BOOT_ADDR         (BOOT_ADDR)
         )
    cv32e40p_tb_wrapper_i
        (
         .clk_i          ( core_clk     ),
         .rst_ni         ( core_rst_n   ),
         .fetch_enable_i ( fetch_enable ),
         .tests_passed_o ( tests_passed ),
         .tests_failed_o ( tests_failed ),
         .exit_valid_o   ( exit_valid   ),
         .exit_value_o   ( exit_value   )
        );

endmodule // tb_top

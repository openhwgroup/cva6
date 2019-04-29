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
// Author: Florian Zaruba, ETH Zurich
// Date: 3/11/2018
// Description: Wrapped Spike Model for Tandem Verification

import uvm_pkg::*;

`include "uvm_macros.svh"

import "DPI-C" function int spike_create(string filename, longint unsigned dram_base, int unsigned size);
import "DPI-C" function void spike_tick(output riscv::commit_log_t commit_log);
import "DPI-C" function void clint_tick();

module spike #(
    parameter longint unsigned DramBase = 'h8000_0000,
    parameter int unsigned     Size     = 64 * 1024 * 1024 // 64 Mega Byte
)(
    input logic       clk_i,
    input logic       rst_ni,
    input logic       clint_tick_i,
    input ariane_pkg::scoreboard_entry_t [ariane_pkg::NR_COMMIT_PORTS-1:0] commit_instr_i,
    input logic [ariane_pkg::NR_COMMIT_PORTS-1:0]                          commit_ack_i,
    input ariane_pkg::exception_t                                          exception_i,
    input logic [ariane_pkg::NR_COMMIT_PORTS-1:0][4:0]                     waddr_i,
    input logic [ariane_pkg::NR_COMMIT_PORTS-1:0][63:0]                    wdata_i,
    input riscv::priv_lvl_t                                                priv_lvl_i
);
    static uvm_cmdline_processor uvcl = uvm_cmdline_processor::get_inst();

    string binary = "";

    logic fake_clk;

    logic clint_tick_q, clint_tick_qq, clint_tick_qqq, clint_tick_qqqq;

    initial begin
        void'(uvcl.get_arg_value("+PRELOAD=", binary));
        assert(binary != "") else $error("We need a preloaded binary for tandem verification");
        void'(spike_create(binary, DramBase, Size));
    end

    riscv::commit_log_t commit_log;
    logic [31:0] instr;

    always_ff @(posedge clk_i) begin
        if (rst_ni) begin

            for (int i = 0; i < ariane_pkg::NR_COMMIT_PORTS; i++) begin
                if ((commit_instr_i[i].valid && commit_ack_i[i]) || (commit_instr_i[i].valid && exception_i.valid)) begin
                    spike_tick(commit_log);
                    instr = (commit_log.instr[1:0] != 2'b11) ? {16'b0, commit_log.instr[15:0]} : commit_log.instr;
                    // $display("\x1B[32m%h %h\x1B[0m", commit_log.pc, instr);
                    // $display("%p", commit_log);
                    // $display("\x1B[37m%h %h\x1B[0m", commit_instr_i[i].pc, commit_instr_i[i].ex.tval[31:0]);
                    assert (commit_log.pc === commit_instr_i[i].pc) else begin
                        $warning("\x1B[33m[Tandem] PCs Mismatch\x1B[0m");
                        // $stop;
                    end
                    assert (commit_log.was_exception === exception_i.valid) else begin
                        $warning("\x1B[33m[Tandem] Exception not detected\x1B[0m");
                        // $stop;
                        $display("Spike: %p", commit_log);
                        $display("Ariane: %p", commit_instr_i[i]);
                    end
                    if (!exception_i.valid) begin
                        assert (commit_log.priv === priv_lvl_i) else begin
                            $warning("\x1B[33m[Tandem] Privilege level mismatches\x1B[0m");
                            // $stop;
                            $display("\x1B[37m %2d == %2d @ PC %h\x1B[0m", priv_lvl_i, commit_log.priv, commit_log.pc);
                        end
                        assert (instr === commit_instr_i[i].ex.tval) else begin
                            $warning("\x1B[33m[Tandem] Decoded instructions mismatch\x1B[0m");
                            // $stop;
                            $display("\x1B[37m%h === %h @ PC %h\x1B[0m", commit_instr_i[i].ex.tval, instr, commit_log.pc);
                        end
                        // TODO(zarubaf): Adapt for floating point instructions
                        if (commit_instr_i[i].rd != 0) begin
                            // check the return value
                            // $display("\x1B[37m%h === %h\x1B[0m", commit_instr_i[i].rd, commit_log.rd);
                            assert (waddr_i[i] === commit_log.rd) else begin
                                $warning("\x1B[33m[Tandem] Destination register mismatches\x1B[0m");
                                // $stop;
                            end
                            assert (wdata_i[i] === commit_log.data) else begin
                                $warning("\x1B[33m[Tandem] Write back data mismatches\x1B[0m");
                                $display("\x1B[37m%h === %h @ PC %h\x1B[0m", wdata_i[i], commit_log.data, commit_log.pc);
                            end
                        end
                    end
                end
            end
        end
    end

    // we want to schedule the timer increment at the end of this cycle
    assign #1ps fake_clk = clk_i;

    always_ff @(posedge fake_clk) begin
        clint_tick_q <= clint_tick_i;
        clint_tick_qq <= clint_tick_q;
        clint_tick_qqq <= clint_tick_qq;
        clint_tick_qqqq <= clint_tick_qqq;
    end

    always_ff @(posedge clint_tick_qqqq) begin
        if (rst_ni) begin
            void'(clint_tick());
        end
    end
endmodule

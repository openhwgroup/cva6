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

module spike #(
    parameter longint unsigned DramBase = 'h8000_0000,
    parameter int unsigned     Size     = 64 * 1024 * 1024 // 64 Mega Byte
)(
    input logic       clk_i,
    input logic       rst_ni,
    input logic       clint_tick_i,
    input ariane_pkg::scoreboard_entry_t [ariane_pkg::NR_COMMIT_PORTS-1:0] commit_instr_i,
    input logic [ariane_pkg::NR_COMMIT_PORTS-1:0] commit_ack_i
);
    // Create a spike simulation object with base at dram_base and size (in bytes).
    // Bytes must be page aligned.
    import "DPI-C" function int spike_create(string filename, longint unsigned dram_base, int unsigned size);
    import "DPI-C" function void spike_tick(output riscv::commit_log_t commit_log);
    import "DPI-C" function void clint_tick();

    initial begin
        void'(spike_create("/home/zarubaf/riscv/target/share/riscv-tests/benchmarks/dhrystone.riscv", DramBase, Size));
    end

    riscv::commit_log_t commit_log;
    logic [31:0] instr;
    always_ff @(posedge clk_i) begin
        if (rst_ni) begin
            for (int i = 0; i < ariane_pkg::NR_COMMIT_PORTS; i++) begin
                if (commit_instr_i[i].valid && commit_ack_i[i]) begin
                    spike_tick(commit_log);
                    instr = (commit_log.instr[1:0] != 2'b11) ? {16'b0, commit_log.instr[15:0]} : commit_log.instr;
                    $display("\x1B[32m%h %h\x1B[0m", commit_log.pc, instr);
                    $display("\x1B[37m%h %h\x1B[0m", commit_instr_i[i].pc, commit_instr_i[i].ex.tval[31:0]);
                end
            end
        end
    end

    always_ff @(posedge clint_tick_i) begin
        if (rst_ni) begin
            void'(clint_tick());
        end
    end
endmodule

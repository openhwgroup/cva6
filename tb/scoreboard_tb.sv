// Author: Florian Zaruba, ETH Zurich
// Date: 10/04/2017
// Description: Top level testbench module. Instantiates the top level DUT, configures
//              the virtual interfaces and starts the test passed by +UVM_TEST+
//
// Copyright (C) 2017 ETH Zurich, University of Bologna
// All rights reserved.
//
// TODO, test register read and clobber interface
module scoreboard_tb;

import uvm_pkg::*;
import ariane_pkg::*;

logic rst_ni, clk;
scoreboard_entry scoreboard_queue[$];
scoreboard_entry temp_scoreboard_entry;
scoreboard_entry comp;

integer unsigned pc = 0;

scoreboard_if scoreboard_if (clk);

scoreboard dut (
    .clk_i                ( clk                               ),
    .rst_ni               ( rst_ni                            ),
    .full_o               ( scoreboard_if.full                ),
    .flush_i              ( scoreboard_if.flush               ),
    .rd_clobber_o         ( scoreboard_if.rd_clobber          ),
    .rs1_i                ( scoreboard_if.rs1_address         ),
    .rs1_o                ( scoreboard_if.rs1                 ),
    .rs1_valid_o          ( scoreboard_if.rs1_valid           ),
    .rs2_i                ( scoreboard_if.rs2_address         ),
    .rs2_o                ( scoreboard_if.rs2                 ),
    .rs2_valid_o          ( scoreboard_if.rs2_valid           ),
    .commit_instr_o       ( scoreboard_if.commit_instr        ),
    .commit_ack_i         ( scoreboard_if.commit_ack          ),
    .decoded_instr_i      ( scoreboard_if.decoded_instr       ),
    .decoded_instr_valid_i( scoreboard_if.decoded_instr_valid ),
    .issue_instr_o        ( scoreboard_if.issue_instr         ),
    .issue_instr_valid_o  ( scoreboard_if.issue_instr_valid   ),
    .issue_ack_i          ( scoreboard_if.issue_ack           ),
    .pc_i                 ( scoreboard_if.pc                  ),
    .wdata_i              ( scoreboard_if.wdata               ),
    .wb_valid_i           ( scoreboard_if.wb_valid            )
);

    function automatic scoreboard_entry randomize_scoreboard();
        exception exception = { 64'h55, 63'h0, 1'b0};
        scoreboard_entry entry = {
            pc, ALU, ADD, 5'h5, 5'h5, 5'h5, 64'h0, 1'b0, 1'b0, exception
        };
        pc++;
        return entry;
    endfunction : randomize_scoreboard

    initial begin
    // register the scoreboard interface
    // uvm_config_db #(virtual scoreboard_if)::set(null, "uvm_test_top", "scoreboard_vif", scoreboard_if);
    end

    initial begin
        clk = 1'b0;
        rst_ni = 1'b0;
        repeat(8)
            #10ns clk = ~clk;

        rst_ni = 1'b1;
        forever
            #10ns clk = ~clk;
    end

    // push new decoded instructions
    initial begin
        wait(rst_ni == 1'b1);
        // load the scoreboard until it is full
        forever begin

            @(scoreboard_if.mck);
            // if we are not full load another instruction
            if (scoreboard_if.full == 1'b0) begin
                temp_scoreboard_entry = randomize_scoreboard();
                scoreboard_queue.push_back(temp_scoreboard_entry);

                scoreboard_if.mck.decoded_instr       <= temp_scoreboard_entry;
                scoreboard_if.mck.decoded_instr_valid <= 1'b1;
            end else begin
                scoreboard_if.mck.decoded_instr_valid <= 1'b0;
            end

        end
    end
    scoreboard_entry issue_instruction;
    // pull e.g. issue instructions
    initial begin
        wait(rst_ni == 1'b1);
        forever begin

            @(scoreboard_if.mck);
            scoreboard_if.mck.wb_valid <= 1'b0;
            // if we are not full then load another instruction
            if (scoreboard_if.issue_instr_valid == 1'b1) begin
                scoreboard_if.mck.issue_ack <= 1'b1;
                issue_instruction <= scoreboard_if.mck.issue_instr;
                @(scoreboard_if.mck)
                scoreboard_if.mck.issue_ack <= 1'b0;

                // generate a delay between 1 and 3 cycles for WB
                repeat ($urandom_range(0,3)) @(scoreboard_if.mck);
                scoreboard_if.mck.pc <= issue_instruction.pc;
                scoreboard_if.mck.wdata <= 64'h7777;
                scoreboard_if.mck.wb_valid <= 1'b1;
            end else begin
                scoreboard_if.mck.issue_ack <= 1'b0;
            end

        end
    end
    // commit instructions
    initial begin
        wait(rst_ni == 1'b1);
        forever begin
            repeat ($urandom_range(1,3)) @(scoreboard_if.mck);
            if (scoreboard_if.mck.commit_instr.valid == 1'b1) begin
                scoreboard_if.mck.commit_ack <= 1'b1;
                @(scoreboard_if.mck);
                scoreboard_if.mck.commit_ack <= 1'b0;
                repeat ($urandom_range(0,3)) @(scoreboard_if.mck);
            end else
                scoreboard_if.mck.commit_ack <= 1'b0;
        end
    end
    // commit checker e.g.: monitor
    initial begin
        wait(rst_ni == 1'b1);

        forever begin
            @(scoreboard_if.pck);
            if (scoreboard_if.pck.commit_ack == 1'b1) begin
                comp = scoreboard_queue.pop_front();
                assert (comp.pc === scoreboard_if.pck.commit_instr.pc) else $error($sformatf("Mismatch: Expected: %0h Got: %0h", comp.pc, scoreboard_if.pck.commit_instr.pc));
            end
        end
    end
endmodule
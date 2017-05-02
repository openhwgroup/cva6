// Author: Florian Zaruba, ETH Zurich
// Date: 10/04/2017
// Description: Top level testbench module. Instantiates the top level DUT, configures
//              the virtual interfaces and starts the test passed by +UVM_TEST+
//
// Copyright (C) 2017 ETH Zurich, University of Bologna
// All rights reserved.
//
// TODO, test register read and clobber interface, make a proper TB out of it

import uvm_pkg::*;
import ariane_pkg::*;

module scoreboard_tb;

    `include "models/scoreboard.sv"

    logic rst_ni, clk;
    scoreboard_if #(.NR_WB_PORTS(1) ) scoreboard_if (clk);

    scoreboard #(
        .NR_WB_PORTS          ( 1                                 ),
        .NR_ENTRIES           ( NR_SB_ENTRIES                     )
    )
    dut
    (
        .clk_i                ( clk                               ),
        .rst_ni               ( rst_ni                            ),
        .full_o               ( scoreboard_if.full                ),
        .flush_i              ( scoreboard_if.flush               ),
        .rd_clobber_o         ( fu_t'(scoreboard_if.rd_clobber)   ),
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
        .trans_id_i           ( scoreboard_if.trans_id            ),
        .wdata_i              ( scoreboard_if.wdata               ),
        .wb_valid_i           ( scoreboard_if.wb_valid            )
    );

    initial begin
        clk = 1'b0;
        rst_ni = 1'b0;
        repeat(8)
            #10ns clk = ~clk;

        rst_ni = 1'b1;
        forever
            #10ns clk = ~clk;
    end

    // simulator stopper, this is suboptimal better go for coverage
    initial begin
        #10000000ns
        $stop;
    end

    program testbench (scoreboard_if scoreboard_if);
        // variable declarations
        Scoreboard sb = new;
        semaphore wb_lock = new(1);
        logic[4:0] i = 0;
        assign scoreboard_if.flush = 1'b0;

        initial begin
        // register the scoreboard interface
        // uvm_config_db #(virtual scoreboard_if)::set(null, "uvm_test_top", "scoreboard_vif", scoreboard_if);
        end

        // push new decoded instructions
        initial begin
            scoreboard_if.mck.decoded_instr_valid <= 1'b0;
            wait(rst_ni == 1'b1);
            // load the scoreboard until it is full
            forever begin

                @(scoreboard_if.mck);
                // if we are not full load another instruction
                if (scoreboard_if.full == 1'b0) begin
                    scoreboard_if.mck.decoded_instr       <= Scoreboard::randomize_scoreboard();
                    scoreboard_if.mck.decoded_instr_valid <= 1'b1;
                end else begin
                    scoreboard_if.mck.decoded_instr_valid <= 1'b0;
                end

            end
        end

        scoreboard_entry issue_instruction;
        // pull e.g. issue instructions
        initial begin
            // reset values
            scoreboard_if.mck.trans_id <= 'b0;
            scoreboard_if.mck.wdata    <= 'b0;
            scoreboard_if.mck.wb_valid <= 1'b0;

            wait(rst_ni == 1'b1);

            forever begin

                @(scoreboard_if.mck);

                // if we are not full then load another instruction
                if (scoreboard_if.issue_instr_valid == 1'b1) begin
                    scoreboard_if.mck.issue_ack <= 1'b1;
                    issue_instruction <= scoreboard_if.mck.issue_instr;
                    // $display("Time: %t, Issuing: %0h, Valid: %h", $time, scoreboard_if.mck.issue_instr.pc, scoreboard_if.issue_instr_valid);
                    @(scoreboard_if.mck)
                    scoreboard_if.mck.issue_ack <= 1'b0;
                    // generate a delay between 0 and 3 cycles for WB, write-back out of order
                    fork
                        write_back: begin
                            automatic logic [TRANS_ID_BITS-1:0] trans_id = issue_instruction.trans_id;
                            automatic logic [63:0] random_data = $urandom_range(0, 2**31);
                            wb_lock.get(1);
                            repeat ($urandom_range(1,20)) @(scoreboard_if.mck);
                            // $display("Time: %t, Writing Back: %0h", $time, thread_copy.pc);
                            scoreboard_if.mck.trans_id <= trans_id;
                            scoreboard_if.mck.wdata    <= random_data;
                            scoreboard_if.mck.wb_valid <= 1'b1;
                            // $display("Write Back: %0h", random_data);
                            sb.write_back(trans_id, random_data);
                            @(scoreboard_if.mck);
                            scoreboard_if.mck.wb_valid <= 1'b0;
                            wb_lock.put(1);
                        end
                    join_none
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
                    // $display("Time: %t, Commiting: %0h", $time, scoreboard_if.mck.commit_instr.pc);
                    scoreboard_if.mck.commit_ack <= 1'b1;
                    @(scoreboard_if.mck);
                    scoreboard_if.mck.commit_ack <= 1'b0;
                    repeat ($urandom_range(0,3)) @(scoreboard_if.mck);
                end else
                    scoreboard_if.mck.commit_ack <= 1'b0;
            end
        end

        // ------------------
        // Monitor + Checker
        // ------------------
        initial begin
            wait(rst_ni == 1'b1);
            forever begin
                @(scoreboard_if.pck);
                if (scoreboard_if.pck.decoded_instr_valid == 1'b1) begin
                    sb.submit_instruction(scoreboard_if.pck.decoded_instr);
                end
            end
        end

        scoreboard_entry tmp_sbe;
        initial begin
            wait(rst_ni == 1'b1);
            forever begin
                @(scoreboard_if.pck);
                if (scoreboard_if.pck.issue_instr_valid == 1'b1 && scoreboard_if.pck.issue_ack) begin
                    tmp_sbe = sb.get_issue();
                    assert (tmp_sbe.trans_id == issue_instruction.trans_id) else $error("Issue instruction mismatch. Expected: %p Got: %p", tmp_sbe, issue_instruction);
                end
            end
        end
        // commit checker
        scoreboard_entry comp;
        initial begin
            wait(rst_ni == 1'b1);

            forever begin
                @(scoreboard_if.pck);
                if (scoreboard_if.pck.commit_ack == 1'b1) begin
                    comp = sb.commit();
                    assert (comp === scoreboard_if.pck.commit_instr) else $error($sformatf("Mismatch: \nExpected: %p \nGot: %p", comp, scoreboard_if.pck.commit_instr));
                end
            end
        end
    endprogram

    testbench tb(scoreboard_if);
endmodule
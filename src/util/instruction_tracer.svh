// Author: Florian Zaruba, ETH Zurich
// Date: 16.05.2017
// Description: Instruction Tracer Main Class
//
// Copyright (C) 2017 ETH Zurich, University of Bologna
// All rights reserved.
//
// This code is under development and not yet released to the public.
// Until it is released, the code is under the copyright of ETH Zurich and
// the University of Bologna, and may contain confidential and/or unpublished
// work. Any reuse/redistribution is strictly forbidden without written
// permission from ETH Zurich.
//
// Bug fixes and contributions will eventually be released under the
// SolderPad open hardware license in the context of the PULP platform
// (http://www.pulp-platform.org), under the copyright of ETH Zurich and the
// University of Bologna.
//

class instruction_tracer;

    // interface to the core
    virtual instruction_tracer_if tracer_if;
    // keep the decoded instructions in a queue
    fetch_entry decode_queue [$];
    // keep the issued instructions in a queue
    fetch_entry issue_queue [$];
    // issue scoreboard entries
    scoreboard_entry issue_sbe_queue [$];
    scoreboard_entry issue_sbe;

    // shadow copy of the register file
    logic [63:0] reg_file [32];
    // 64 bit clock tick count
    longint unsigned clk_ticks;

    function new(virtual instruction_tracer_if tracer_if);
        this.tracer_if = tracer_if;
    endfunction : new

    task trace();
        fetch_entry decode_instruction, issue_instruction, issue_commit_instruction;
        scoreboard_entry commit_instruction;

        // initialize register 0
        reg_file [0] = 0;

        forever begin
            // new cycle, we are only interested if reset is de-asserted
            @(tracer_if.pck iff tracer_if.pck.rstn);
            // increment clock tick
            clk_ticks++;

            // -------------------
            // Instruction Decode
            // -------------------
            // we are decoding an instruction
            if (tracer_if.pck.fetch_valid && tracer_if.pck.fetch_ack) begin
                decode_instruction = fetch_entry'(tracer_if.pck.fetch);
                decode_queue.push_back(decode_instruction);
            end

            // -------------------
            // Instruction Issue
            // -------------------
            // we got a new issue ack, so put the element from the decode queue to
            // the issue queue
            if (tracer_if.pck.issue_ack) begin
                issue_instruction = decode_queue.pop_front();
                issue_queue.push_back(issue_instruction);
                // also save the scoreboard entry to a separate issue queue
                issue_sbe_queue.push_back(scoreboard_entry'(tracer_if.pck.issue_sbe));
            end

            // -----------------
            // Physical Address
            // -----------------

            // -----------
            // Write Back
            // -----------
            // update shadow reg file here
            if (tracer_if.pck.we && tracer_if.pck.waddr != 5'b0) begin
                reg_file[tracer_if.pck.waddr] = tracer_if.pck.wdata;
            end

            // --------------
            //  Commit
            // --------------
            // we are committing an instruction
            if (tracer_if.pck.commit_ack) begin
                commit_instruction = scoreboard_entry'(tracer_if.pck.commit_instr);
                issue_commit_instruction = issue_queue.pop_front();
                issue_sbe = issue_sbe_queue.pop_front();
                // the scoreboards issue entry still contains the immediate value as a result
                printInstr(issue_sbe, issue_commit_instruction.instruction, tracer_if.pck.wdata);
            end

            // --------------
            // Flush Signals
            // --------------
            // flush un-issued instructions
            if (tracer_if.pck.flush_unissued) begin
                this.flushDecode();
            end
            // flush whole pipeline
            if (tracer_if.pck.flush) begin
                this.flush();
            end
        end

    endtask
    // flush all decoded instructions
    function void flushDecode ();
        decode_queue = {};
    endfunction;

    // flush everything, we took an exception/interrupt
    function void flush ();
        this.flushDecode();
        // clear all elements in the queue
        issue_queue = {};
        issue_sbe_queue = {};
    endfunction;

    function void printInstr(scoreboard_entry sbe, logic [63:0] instr, logic [63:0] result);
        instruction_trace_item iti = new ($time, clk_ticks, sbe, instr, this.reg_file, result);
        $display(iti.printInstr());
        // $display("Time: %t Cycle: %d PC: %h Instruction: %s", $time(), clk_ticks, sbe.pc, iti.printInstr());

    endfunction;

endclass : instruction_tracer
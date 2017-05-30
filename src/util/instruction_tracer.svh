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

// keep the instruction and scoreboard entry together
typedef struct {
    fetch_entry         fetch_entry;
    scoreboard_entry    sbe;
} issue_entry;

class instruction_tracer;

    // interface to the core
    virtual instruction_tracer_if tracer_if;
    // keep the decoded instructions in a queue
    fetch_entry decode_queue [$];
    // keep the issued instructions in a queue
    issue_entry issue_queue [$];
    // shadow copy of the register file
    logic [63:0] reg_file [31];
    // 64 bit clock tick count
    longint unsigned clk_ticks;

    function new(virtual instruction_tracer_if tracer_if);
        this.tracer_if = tracer_if;
    endfunction : new

    task trace();
        fetch_entry decode_instruction;
        issue_entry issue_instruction;

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
                issue_instruction.fetch_entry = decode_queue.pop_front();
                issue_instruction.sbe = scoreboard_entry'(tracer_if.pck.issue_sbe);
                issue_queue.push_back(issue_instruction);
                printInstr(issue_instruction.sbe.pc, issue_instruction.fetch_entry.instruction);
            end
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
                // printInstr(issue_instruction.instruction);
                // $display("Committing: %0h", tracer_if.pck.commit_instr);
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
        for (int i = 0; i < decode_queue.size(); i++) begin
            decode_queue.delete(i);
        end
    endfunction;

    // flush everything, we took an exception/interrupt
    function void flush ();
        this.flushDecode();
        for (int i = 0; i < issue_queue.size(); i++) begin
            issue_queue.delete(i);
        end
    endfunction;

    function void printInstr(logic [63:0] pc, logic [63:0] instr);
        instruction_trace_item iti = new;
        $display("Time: %t Cycle: %d PC: %h Instruction: %s Instr: %0h", $time(), clk_ticks, pc, iti.printInstr(instr), instr);

    endfunction;

endclass : instruction_tracer
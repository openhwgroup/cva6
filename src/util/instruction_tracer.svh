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
    // shadow copy of the register file
    logic [63:0] reg_file [31];
    // 64 bit clock tick count
    longint unsigned clk_ticks;

    function new(virtual instruction_tracer_if tracer_if);
        this.tracer_if = tracer_if;
    endfunction : new

    task trace();
        fetch_entry issue_instruction;
        forever begin
            // new cycle, we are only interested if reset is de-asserted
            @(tracer_if.pck iff tracer_if.pck.rstn);
            clk_ticks++;

            // We are decoding an instruction
            if (tracer_if.pck.fetch_valid && tracer_if.pck.fetch_ack) begin
                decode_queue.push_back(tracer_if.pck.fetch);
                issue_instruction = fetch_entry'(tracer_if.pck.fetch);
                printInstr(issue_instruction.instruction);
            end
            // we are committing an instruction

            // if (tracer_if.pck.commit_instr.valid) begin
            //     $display("Committing: %0h", tracer_if.pck.commit_instr);
            // end

            // write back
            if (tracer_if.pck.we && tracer_if.pck.waddr != 5'b0) begin
                reg_file[tracer_if.pck.waddr] = tracer_if.pck.wdata;
            end

        end

    endtask

    function void flushIssue ();

    endfunction;

    function void flush ();

    endfunction;

    function void printInstr(logic [63:0] instr);
        instruction_trace_item iti = new;
        $display(iti.printInstr(instr));

    endfunction;

endclass : instruction_tracer
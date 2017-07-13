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
    logic [31:0] decode_queue [$];
    // keep the issued instructions in a queue
    logic [31:0] issue_queue [$];
    // issue scoreboard entries
    scoreboard_entry issue_sbe_queue [$];
    scoreboard_entry issue_sbe;

    // shadow copy of the register file
    logic [63:0] reg_file [32];
    // 64 bit clock tick count
    longint unsigned clk_ticks;
    int f;
    // address mapping
    // contains mappings of the form vaddr <-> paddr
    // should it print the instructions to the console
    logic display_instructions;
    logic [63:0] store_mapping[$], load_mapping[$], address_mapping;

    static uvm_cmdline_processor uvcl = uvm_cmdline_processor::get_inst();


    function new(virtual instruction_tracer_if tracer_if, logic display_instructions);

        this.tracer_if = tracer_if;
        this.display_instructions = display_instructions;

    endfunction : new

    function void create_file(logic [5:0] cluster_id, logic [3:0] core_id);
        string fn;
        $sformat(fn, "trace_core_%h_%h.log", cluster_id, core_id);
        $display("[TRACER] Output filename is: %s", fn);

        this.f = $fopen(fn,"w");
    endfunction : create_file

    task trace();
        logic [31:0] decode_instruction, issue_instruction, issue_commit_instruction;
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
                decode_instruction = tracer_if.pck.instruction;
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

            // --------------------
            // Address Translation
            // --------------------
            if (tracer_if.pck.st_valid) begin
                store_mapping.push_back(tracer_if.pck.st_paddr);
            end

            if (tracer_if.pck.ld_valid && !tracer_if.pck.ld_kill) begin
                load_mapping.push_back(tracer_if.pck.ld_paddr);
            end
            // --------------
            //  Commit
            // --------------
            // we are committing an instruction
            if (tracer_if.pck.commit_ack) begin
                commit_instruction = scoreboard_entry'(tracer_if.pck.commit_instr);
                issue_commit_instruction = issue_queue.pop_front();
                issue_sbe = issue_sbe_queue.pop_front();
                // check if the instruction retiring is a load or store, get the physical address accordingly
                if (tracer_if.pck.commit_instr.fu == LOAD)
                    address_mapping = load_mapping.pop_front();
                else if (tracer_if.pck.commit_instr.fu == STORE)
                    address_mapping = store_mapping.pop_front();
                // the scoreboards issue entry still contains the immediate value as a result
                // check if the write back is valid, if not we need to source the result from the register file
                // as the most recent version of this register will be there.
                if (tracer_if.pck.we) begin
                    printInstr(issue_sbe, issue_commit_instruction, tracer_if.pck.wdata, address_mapping);
                end else
                    printInstr(issue_sbe, issue_commit_instruction, reg_file[commit_instruction.rd], address_mapping);
            end

            // --------------
            // Exceptions
            // --------------
            if (tracer_if.pck.exception.valid) begin
                // print exception
                printException(tracer_if.pck.commit_instr.pc, tracer_if.pck.exception.cause, tracer_if.pck.exception.tval);
            end
            // ----------------------
            // Commit Registers
            // ----------------------
            // update shadow reg file here
            if (tracer_if.pck.we && tracer_if.pck.waddr != 5'b0) begin
                reg_file[tracer_if.pck.waddr] = tracer_if.pck.wdata;
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
        issue_queue     = {};
        issue_sbe_queue = {};
        // also clear mappings
        store_mapping   = {};
        load_mapping    = {};
    endfunction;

    function void printInstr(scoreboard_entry sbe, logic [31:0] instr, logic [63:0] result, logic [63:0] paddr);
        instruction_trace_item iti = new ($time, clk_ticks, sbe, instr, this.reg_file, result, paddr);
        // print instruction to console
        string print_instr = iti.printInstr();
        `uvm_info( "Tracer",  print_instr, UVM_HIGH)
        $fwrite(this.f, {print_instr, "\n"});
    endfunction;

    function void printException(logic [63:0] pc, logic [63:0] cause, logic [63:0] tval);
        exception_trace_item eti = new (pc, cause, tval);
        string print_ex = eti.printException();
        `uvm_info( "Tracer",  print_ex, UVM_HIGH)
        $fwrite(this.f, {print_ex, "\n"});
    endfunction

    function void close();
        $fclose(this.f);
    endfunction

endclass : instruction_tracer

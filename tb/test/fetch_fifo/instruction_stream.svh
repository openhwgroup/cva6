// Author: Florian Zaruba, ETH Zurich
// Date: 14.5.2017
// Description: Random instruction class
//
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
class instruction;
    rand logic [31:0] instruction;
    rand bit          is_compressed;

    constraint compressed_constraint {
        (is_compressed) -> {
            instruction[1:0] != 2'b11;
        }
        (!is_compressed) -> {
            instruction[1:0] == 2'b11;
            instruction[4:2] != 3'b111;
        }
    }

    // Return readable representation
    function string convert2string();

        string s;
        $sformat(s, "Instruction: %0h\nCompressed: %h", instruction, is_compressed);
        return s;

    endfunction : convert2string
endclass : instruction

class instruction_stream;

    logic [63:0] address = 0;
    instruction  instr;
    logic [15:0] unaligned_part;
    int          is_unaligned = 0;
    // get an instruction stream of consecutive data
    function instruction_queue_entry_t get_instruction();

        branchpredict_sbe bp = '0;
        instruction_queue_entry_t return_entry;

        logic [31:0] return_instruction;
        // generate a new instruction
        if (is_unaligned == 0) begin
            instr = new;
            void'(randomize(instr));
            // we've generated a compressed instruction so generate another one
            if (instr.is_compressed) begin
                return_instruction [15:0] = instr.instruction[15:0];
                // get a new instruction
                instr = new;
                void'(randomize(instr));
                return_instruction[31:16] = instr.instruction[15:0];
                // $display("Instruction: [ c  | c  ]");
                // was this a compressed instruction as well?
                // if not than store that this was an unaligned access
                if (!instr.is_compressed) begin
                    // $display("Instruction: [ i0 | c  ]");
                    is_unaligned = 1;
                    unaligned_part = instr.instruction[31:16];
                end
            // normal instruction
            end else begin
                return_instruction = instr.instruction;
                // $display("Instruction: [    i    ]");
            end
        // the last generation iteration produced an outstanding instruction
        end else begin
            return_instruction [15:0] = unaligned_part;
            // generate a new isntruction
            instr = new;
            void'(randomize(instr));
            return_instruction [31:16] = instr.instruction[15:0];
            // was it compressed?
            if (instr.is_compressed) begin
                is_unaligned = 0;
                // $display("Instruction: [ c  | i1 ]");
            end else begin
                // again we have an unaligned instruction
                unaligned_part = instr.instruction[31:16];
                // $display("Instruction: [ i0 | i1 ]");
            end
        end
        return_entry.instr   = return_instruction;
        return_entry.bp      = bp;
        return_entry.address = address;

        address = address + 4;

        return return_entry;
    endfunction : get_instruction

endclass : instruction_stream
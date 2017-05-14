// Author: Florian Zaruba, ETH Zurich
// Date: 14.5.2017
// Description: Fetch FIFO Golden Model
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

// Read 32 bit instruction, separate and re-align them
typedef struct {
        logic [63:0] address;
        logic [31:0] instr;
        branchpredict_sbe bp;
} instruction_queue_entry_t;

class fetch_fifo_model;

    logic [15:0] unaligned_part;
    int          is_unaligned = 0;
    logic [63:0] unaligend_address;

    instruction_queue_entry_t instruction_queue[$];

    function void put(logic [63:0] address, logic [31:0] instr, branchpredict_sbe bp);
        instruction_queue_entry_t param;

        if (is_unaligned == 0) begin
            // we've got a compressed instruction
            if (instr[1:0] != 2'b11) begin
                param.address = address;
                param.instr   = {16'b0, instr[15:0]};
                param.bp      = bp;

                instruction_queue.push_back(param);
                // the upper part is a unaligned 32 bit instruction
                if (instr[17:16] == 2'b11) begin
                    unaligend_address = {address[63:2], 2'b10};
                    is_unaligned      = 1;
                    unaligned_part    = instr[31:16];
                // there is another compressed instruction
                // don't include if branch prediction predicted a compressed
                // branch in the first instruction part
                end else if (!(bp.predict_taken && bp.valid && bp.is_lower_16)) begin
                    param.address = {address[63:2], 2'b10};
                    param.instr   = instr[31:16];
                    param.bp      = bp;
                    instruction_queue.push_back(param);
                end
            // normal instruction
            end else begin
                param.address = address;
                param.instr   = instr;
                param.bp      = bp;
                instruction_queue.push_back(param);
            end
        // the last generation iteration produced an outstanding instruction
        end else begin
            param.address = unaligend_address;
            param.instr   = {instr[15:0], unaligned_part};
            param.bp      = bp;
            instruction_queue.push_back(param);
            // there is another compressed instruction
            // don't include if branch prediction predicted a compressed
            // branch in the first instruction part
            if (instr[17:16] != 2'b11) begin
                if (!(bp.predict_taken && bp.valid && bp.is_lower_16)) begin
                    param.address = {address[63:2], 2'b10};
                    param.instr   = instr[31:16];
                    param.bp      = bp;
                    instruction_queue.push_back(param);
                end
                is_unaligned = 0;
            end else begin
                // again we have an unaligned instruction
                param.address = {address[63:2], 2'b10};
                is_unaligned = 1;
                unaligned_part = instr[31:16];
            end
        end
    endfunction : put

    function instruction_queue_entry_t pull();
        return instruction_queue.pop_front();
    endfunction : pull

    function flush();
        for (int i = 0; i < instruction_queue.size(); i++) begin
            instruction_queue.delete(i);
        end
    endfunction : flush

endclass : fetch_fifo_model
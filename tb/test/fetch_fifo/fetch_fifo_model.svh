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
class fetch_fifo_model;

    logic [15:0] unaligned_part;
    int          is_unaligned = 0;

    logic [31:0] instruction_queue[$];

    function void put(logic [31:0] instr);

        if (is_unaligned == 0) begin
            // we've generated a compressed instruction so generate another one
            if (instr[1:0] != 2'b11) begin
                instruction_queue.push_back({16'b0, instr[15:0]});

                if (instr[17:16] == 2'b11) begin
                    is_unaligned = 1;
                    unaligned_part = instr[31:16];
                end
            // normal instruction
            end else begin
                instruction_queue.push_back(instr);
            end
        // the last generation iteration produced an outstanding instruction
        end else begin
            instruction_queue.push_back({instr[15:0], unaligned_part});

            if (instr[17:16] != 2'b11) begin
                instruction_queue.push_back({16'b0, instr[31:16]});
                is_unaligned = 0;
            end else begin
                // again we have an unaligned instruction
                is_unaligned = 1;
                unaligned_part = instr[31:16];
            end
        end
    endfunction : put

    function logic [31:0] pull();
        return instruction_queue.pop_front();
    endfunction : pull

    function flush();
        for (int i = 0; i < instruction_queue.size(); i++) begin
            instruction_queue.delete(i);
        end
    endfunction : flush

endclass : fetch_fifo_model
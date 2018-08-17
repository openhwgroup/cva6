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
// Date: 08.02.2018
// Description: Ariane Instruction Fetch Frontend


import ariane_pkg::*;

module frontend #(
    parameter int unsigned BTB_ENTRIES       = 8,
    parameter int unsigned BHT_ENTRIES       = 1024,
    parameter int unsigned RAS_DEPTH         = 4
)(
    input  logic               clk_i,              // Clock
    input  logic               rst_ni,             // Asynchronous reset active low
    input  logic               flush_i,            // flush request for PCGEN
    input  logic               flush_bp_i,         // flush branch prediction
    // global input
    input  logic [63:0]        boot_addr_i,
    input  logic               fetch_enable_i,     // start fetching instructions
    // Set a new PC
    // mispredict
    input  branchpredict_t     resolved_branch_i,  // from controller signaling a branch_predict -> update BTB
    // from commit, when flushing the whole pipeline
    input  logic               set_pc_commit_i,    // Take the PC from commit stage
    input  logic [63:0]        pc_commit_i,        // PC of instruction in commit stage
    // CSR input
    input  logic [63:0]        epc_i,              // exception PC which we need to return to
    input  logic               eret_i,             // return from exception
    input  logic [63:0]        trap_vector_base_i, // base of trap vector
    input  logic               ex_valid_i,         // exception is valid - from commit
    // Debug
    input  logic [63:0]        debug_pc_i,         // PC from debug stage
    input  logic               debug_set_pc_i,     // Set PC request from debug
    // Instruction Fetch
    input  icache_dreq_o_t     icache_dreq_i,         
    output icache_dreq_i_t     icache_dreq_o,       
    
    // instruction output port -> to processor back-end
    output fetch_entry_t       fetch_entry_o,       // fetch entry containing all relevant data for the ID stage
    output logic               fetch_entry_valid_o, // instruction in IF is valid
    input  logic               fetch_ack_i          // ID acknowledged this instruction
);
    // maximum instructions we can fetch on one request
    localparam int unsigned INSTR_PER_FETCH = FETCH_WIDTH/16;

    // Registers
    logic [31:0] icache_data_q;
    logic        icache_valid_q;
    exception_t  icache_ex_q;

    logic        instruction_valid;

    logic        icache_speculative_q;
    logic [63:0] icache_vaddr_q;

    // BHT, BTB and RAS prediction
    bht_prediction_t bht_prediction;
    btb_prediction_t btb_prediction;
    ras_t            ras_predict;
    bht_update_t     bht_update;
    btb_update_t     btb_update;
    logic            ras_push, ras_pop;
    logic [63:0]     ras_update;


    // instruction fetch is ready
    logic          if_ready;
    logic [63:0]   npc_d, npc_q; // next PC
    // -----------------------
    // Ctrl Flow Speculation
    // -----------------------
    // RVI ctrl flow prediction
    logic [INSTR_PER_FETCH-1:0]       rvi_return, rvi_call, rvi_branch,
                                      rvi_jalr, rvi_jump;
    logic [INSTR_PER_FETCH-1:0][63:0] rvi_imm;
    // RVC branching
    logic [INSTR_PER_FETCH-1:0]       is_rvc;
    logic [INSTR_PER_FETCH-1:0]       rvc_branch, rvc_jump, rvc_jr, rvc_return,
                                      rvc_jalr, rvc_call;
    logic [INSTR_PER_FETCH-1:0][63:0] rvc_imm;
    // re-aligned instruction and address (coming from cache - combinationally)
    logic [INSTR_PER_FETCH-1:0][31:0] instr;
    logic [INSTR_PER_FETCH-1:0][63:0] addr;

    logic [63:0]   bp_vaddr;
    logic          bp_valid; // we have a valid branch-prediction
    
    // branch-prediction which we inject into the pipeline
    branchpredict_sbe_t  bp_sbe;
    logic                fifo_valid, fifo_ready; // fetch FIFO

    // save the unaligned part of the instruction to this ff
    logic [15:0] unaligned_instr_d,   unaligned_instr_q;
    // the last instruction was unaligned
    logic        unaligned_d,         unaligned_q;
    // register to save the unaligned address
    logic [63:0] unaligned_address_d, unaligned_address_q;

    // TODO: generalize to arbitrary instruction fetch width
    always_comb begin : re_align
        unaligned_d = unaligned_q;
        unaligned_address_d = unaligned_address_q;
        unaligned_instr_d = unaligned_instr_q;
        instruction_valid = icache_valid_q;

        instr[1] = '0;
        instr[0] = icache_data_q;

        addr[1] = {icache_vaddr_q[63:2], 2'b10};
        addr[0] = icache_vaddr_q;

        if (icache_valid_q) begin
            // last instruction was unaligned
            if (unaligned_q) begin
                instr[0] = {icache_data_q[15:0], unaligned_instr_q};
                addr[0] = unaligned_address_q;
                unaligned_address_d = {icache_vaddr_q[63:2], 2'b10};
                unaligned_instr_d = icache_data_q[31:16]; // save the upper bits for next cycle
                // check if this is instruction is still unaligned e.g.: it is not compressed
                // if its compressed re-set unaligned flag
                if (icache_data_q[17:16] != 2'b11) begin
                    unaligned_d = 1'b0;
                    instr[1] = {16'b0, icache_data_q[31:16]};
                end
            end else if (is_rvc[0]) begin // instruction zero is RVC
                // is instruction 1 also compressed
                // yes? -> no problem, no -> we've got an unaligned instruction
                if (icache_data_q[17:16] != 2'b11) begin
                    instr[1] = {16'b0, icache_data_q[31:16]};
                end else begin
                    unaligned_instr_d = icache_data_q[31:16];
                    unaligned_address_d = {icache_vaddr_q[63:2], 2'b10};
                    unaligned_d = 1'b1;
                end
            end // else -> normal fetch
        end

        // we started to fetch on a unaligned boundary with a whole instruction -> wait until we've
        // received the next instruction
        if (icache_valid_q && icache_vaddr_q[1] && icache_data_q[17:16] == 2'b11) begin
            instruction_valid = 1'b0;
            unaligned_d = 1'b1;
            unaligned_address_d = {icache_vaddr_q[63:2], 2'b10};
            unaligned_instr_d = icache_data_q[31:16];
        end

        if (icache_dreq_o.kill_s2) begin
            unaligned_d = 1'b0;
        end
    end

    logic [INSTR_PER_FETCH:0] taken;
    // control front-end + branch-prediction
    always_comb begin : frontend_ctrl
        automatic logic take_rvi_cf; // take the control flow change (non-compressed)
        automatic logic take_rvc_cf; // take the control flow change (compressed)

        take_rvi_cf       = 1'b0;
        take_rvc_cf       = 1'b0;
        ras_pop           = 1'b0;
        ras_push          = 1'b0;
        ras_update        = '0;
        taken             = '0;
        take_rvi_cf       = 1'b0;
        if_ready          = icache_dreq_i.ready & fifo_ready;
        icache_dreq_o.req = fifo_ready;

        bp_vaddr          = '0;    // predicted address
        bp_valid          = 1'b0;  // prediction is valid

        bp_sbe.cf_type    = RAS;

        // only predict if the response is valid
        if (instruction_valid) begin
            // look at instruction 0, 1, 2,...
            for (int unsigned i = 0; i < INSTR_PER_FETCH; i++) begin
                // only speculate if the previous instruction was not taken
                if (!taken[i]) begin
                    // function call
                    ras_push = rvi_call[i] | rvc_call[i];
                    ras_update = addr[i] + (rvc_call[i] ? 2 : 4);

                    // Branch Prediction - **speculative**
                    if (rvi_branch[i] || rvc_branch[i]) begin
                        bp_sbe.cf_type = BHT;
                        // dynamic prediction valid?
                        if (bht_prediction.valid) begin
                            take_rvi_cf = rvi_branch[i] & (bht_prediction.taken | bht_prediction.strongly_taken);
                            take_rvc_cf = rvc_branch[i] & (bht_prediction.taken | bht_prediction.strongly_taken);
                        // default to static prediction
                        end else begin
                            // set if immediate is negative - static prediction
                            take_rvi_cf = rvi_branch[i] & rvi_imm[i][63];
                            take_rvc_cf = rvc_branch[i] & rvc_imm[i][63];
                        end
                    end

                    // unconditional jumps
                    if (rvi_jump[i] || rvc_jump[i]) begin
                        take_rvi_cf = rvi_jump[i];
                        take_rvc_cf = rvc_jump[i];
                    end

                    // to take this jump we need a valid prediction target **speculative**
                    if ((rvi_jalr[i] || rvc_jalr[i]) && btb_prediction.valid) begin
                        bp_vaddr = btb_prediction.target_address;
                        taken[i+1] = 1'b1;
                        bp_sbe.cf_type = BTB;
                    end

                    // is it a return and the RAS contains a valid prediction? **speculative**
                    if ((rvi_return[i] || rvc_return[i]) && ras_predict.valid) begin
                        bp_vaddr = ras_predict.ra;
                        ras_pop = 1'b1;
                        taken[i+1] = 1'b1;
                        bp_sbe.cf_type = RAS;
                    end

                    if (take_rvi_cf) begin
                        taken[i+1] = 1'b1;
                        bp_vaddr = addr[i] + rvi_imm[i];
                    end

                    if (take_rvc_cf) begin
                        taken[i+1] = 1'b1;
                        bp_vaddr = addr[i] + rvc_imm[i];
                    end

                    // we are not interested in the lower instruction
                    if (icache_vaddr_q[1]) begin
                        taken[1] = 1'b0;
                        ras_pop = 1'b0;
                        ras_push = 1'b0;
                    end
                end
            end
        end

        bp_valid = |taken;
        // assemble scoreboard entry
        bp_sbe.valid = bp_valid;
        bp_sbe.predict_address = bp_vaddr;
        bp_sbe.predict_taken = bp_valid;
        bp_sbe.is_lower_16 = taken[1]; // the branch is on the lower 16 (in a 32-bit setup)

    end

    logic is_mispredict;
    assign is_mispredict = resolved_branch_i.valid & resolved_branch_i.is_mispredict;

    always_comb begin : id_if
        icache_dreq_o.kill_s1 = 1'b0;
        icache_dreq_o.kill_s2 = 1'b0;

        // we mis-predicted so kill the icache request and the fetch queue
        if (is_mispredict || flush_i) begin
            icache_dreq_o.kill_s1 = 1'b1;
            icache_dreq_o.kill_s2 = 1'b1;
        end

        // if we have a valid branch-prediction we need to kill the last cache request
        if (bp_valid) begin
            icache_dreq_o.kill_s2 = 1'b1;
        end

        fifo_valid = icache_valid_q;
    end

    // ----------------------------------------
    // Update Control Flow Predictions
    // ----------------------------------------
    // BHT
    assign bht_update.valid = resolved_branch_i.valid & (resolved_branch_i.cf_type == BHT);
    assign bht_update.pc    = resolved_branch_i.pc;
    assign bht_update.mispredict = resolved_branch_i.is_mispredict;
    assign bht_update.taken = resolved_branch_i.is_taken;
    // BTB
    assign btb_update.valid = resolved_branch_i.valid & (resolved_branch_i.cf_type == BTB);
    assign btb_update.pc    = resolved_branch_i.pc;
    assign btb_update.target_address = resolved_branch_i.target_address;
    assign btb_update.is_lower_16 = resolved_branch_i.is_lower_16;
    assign btb_update.clear = resolved_branch_i.clear;

    // -------------------
    // Next PC
    // -------------------
    // next PC (NPC) can come from (in order of precedence):
    // 0. Default assignment
    // 1. Branch Predict taken
    // 2. Control flow change request (misprediction)
    // 3. Return from environment call
    // 4. Exception/Interrupt
    // 5. Pipeline Flush because of CSR side effects
    // 6. Debug
    // Mis-predict handling is a little bit different
    // select PC a.k.a PC Gen
    always_comb begin : npc_select
        automatic logic [63:0] fetch_address;

        icache_dreq_o.is_speculative = 1'b0;

        fetch_address    = npc_q;
        // keep stable by default
        npc_d            = npc_q;
        // -------------------------------
        // 1. Branch Prediction
        // -------------------------------
        if (bp_valid) begin
            icache_dreq_o.is_speculative = 1'b1;
            fetch_address = bp_vaddr;
            npc_d = bp_vaddr;
        end
        // -------------------------------
        // 0. Default assignment
        // -------------------------------
        if (if_ready && fetch_enable_i) begin
            npc_d = {fetch_address[63:2], 2'b0}  + 64'h4;
            icache_dreq_o.is_speculative = 1'b1;
        end
        // -------------------------------
        // 2. Control flow change request
        // -------------------------------
        if (is_mispredict) begin
            npc_d = resolved_branch_i.target_address;
        end
        // -------------------------------
        // 3. Return from environment call
        // -------------------------------
        if (eret_i) begin
            npc_d = epc_i;
        end
        // -------------------------------
        // 4. Exception/Interrupt
        // -------------------------------
        if (ex_valid_i) begin
            npc_d    = trap_vector_base_i;
        end
        // -----------------------------------------------
        // 5. Pipeline Flush because of CSR side effects
        // -----------------------------------------------
        // On a pipeline flush start fetching from the next address
        // of the instruction in the commit stage
        if (set_pc_commit_i) begin
            // we came here from a flush request of a CSR instruction,
            // as CSR instructions do not exist in a compressed form
            // we can unconditionally do PC + 4 here
            npc_d    = pc_commit_i + 64'h4;
        end

        // -------------------------------
        // 6. Debug
        // -------------------------------
        if (debug_set_pc_i) begin
            npc_d = debug_pc_i;
        end

        icache_dreq_o.vaddr = fetch_address;
    end

    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (~rst_ni) begin
            npc_q                <= boot_addr_i;
            icache_data_q        <= '0;
            icache_valid_q       <= 1'b0;
            icache_speculative_q <= 1'b0;
            icache_vaddr_q       <= 'b0;
            icache_ex_q          <= '0;
            unaligned_q          <= 1'b0;
            unaligned_address_q  <= '0;
            unaligned_instr_q    <= '0;
        end else begin
            npc_q                <= npc_d;
            icache_data_q        <= icache_dreq_i.data;
            icache_valid_q       <= icache_dreq_i.valid;
            icache_speculative_q <= icache_dreq_i.is_speculative;
            icache_vaddr_q       <= icache_dreq_i.vaddr;
            icache_ex_q          <= icache_dreq_i.ex;
            unaligned_q          <= unaligned_d;
            unaligned_address_q  <= unaligned_address_d;
            unaligned_instr_q    <= unaligned_instr_d;
        end
    end

    ras #(
        .DEPTH  ( RAS_DEPTH   )
    ) i_ras (
        .push_i ( ras_push    ),
        .pop_i  ( ras_pop     ),
        .data_i ( ras_update  ),
        .data_o ( ras_predict ),
        .*
    );

    btb #(
        .NR_ENTRIES       ( BTB_ENTRIES      )
    ) i_btb (
        .flush_i          ( flush_bp_i       ),
        .vpc_i            ( icache_vaddr_q   ),
        .btb_update_i     ( btb_update       ),
        .btb_prediction_o ( btb_prediction   ),
        .*
    );

    bht #(
        .NR_ENTRIES       ( BHT_ENTRIES      )
    ) i_bht (
        .flush_i          ( flush_bp_i       ),
        .vpc_i            ( icache_vaddr_q   ),
        .bht_update_i     ( bht_update       ),
        .bht_prediction_o ( bht_prediction   ),
        .*
    );



    for (genvar i = 0; i < INSTR_PER_FETCH; i++) begin
        instr_scan i_instr_scan (
            .instr_i      ( instr[i]      ),
            .is_rvc_o     ( is_rvc[i]     ),
            .rvi_return_o ( rvi_return[i] ),
            .rvi_call_o   ( rvi_call[i]   ),
            .rvi_branch_o ( rvi_branch[i] ),
            .rvi_jalr_o   ( rvi_jalr[i]   ),
            .rvi_jump_o   ( rvi_jump[i]   ),
            .rvi_imm_o    ( rvi_imm[i]    ),
            .rvc_branch_o ( rvc_branch[i] ),
            .rvc_jump_o   ( rvc_jump[i]   ),
            .rvc_jr_o     ( rvc_jr[i]     ),
            .rvc_return_o ( rvc_return[i] ),
            .rvc_jalr_o   ( rvc_jalr[i]   ),
            .rvc_call_o   ( rvc_call[i]   ),
            .rvc_imm_o    ( rvc_imm[i]    )
        );
    end

    fetch_fifo i_fetch_fifo (
        .flush_i            ( flush_i             ),
        .branch_predict_i   ( bp_sbe              ),
        .ex_i               ( icache_ex_q         ),
        .addr_i             ( icache_vaddr_q      ),
        .rdata_i            ( icache_data_q       ),
        .valid_i            ( fifo_valid          ),
        .ready_o            ( fifo_ready          ),
        .fetch_entry_o      ( fetch_entry_o       ),
        .fetch_entry_valid_o( fetch_entry_valid_o ),
        .fetch_ack_i        ( fetch_ack_i         ),
        .*
    );

endmodule

// ------------------------------
// Instruction Scanner
// ------------------------------
module instr_scan (
    input  logic [31:0] instr_i,        // expect aligned instruction, compressed or not
    output logic        is_rvc_o,
    output logic        rvi_return_o,
    output logic        rvi_call_o,
    output logic        rvi_branch_o,
    output logic        rvi_jalr_o,
    output logic        rvi_jump_o,
    output logic [63:0] rvi_imm_o,
    output logic        rvc_branch_o,
    output logic        rvc_jump_o,
    output logic        rvc_jr_o,
    output logic        rvc_return_o,
    output logic        rvc_jalr_o,
    output logic        rvc_call_o,
    output logic [63:0] rvc_imm_o
);
    assign is_rvc_o     = (instr_i[1:0] != 2'b11);
    // check that rs1 is either x1 or x5 and that rs1 is not x1 or x5, TODO: check the fact about bit 7
    assign rvi_return_o = rvi_jalr_o & ~instr_i[7] & ~instr_i[19] & ~instr_i[18] & ~instr_i[16] & instr_i[15];
    assign rvi_call_o   = (rvi_jalr_o | rvi_jump_o) & instr_i[7]; // TODO: check that this captures calls
    // differentiates between JAL and BRANCH opcode, JALR comes from BHT
    assign rvi_imm_o    = (instr_i[3]) ? uj_imm(instr_i) : sb_imm(instr_i);
    assign rvi_branch_o = (instr_i[6:0] == OPCODE_BRANCH) ? 1'b1 : 1'b0;
    assign rvi_jalr_o   = (instr_i[6:0] == OPCODE_JALR)   ? 1'b1 : 1'b0;
    assign rvi_jump_o   = (instr_i[6:0] == OPCODE_JAL)    ? 1'b1 : 1'b0;
    // opcode JAL
    assign rvc_jump_o   = (instr_i[15:13] == OPCODE_C_J) & is_rvc_o & (instr_i[1:0] == 2'b01);
    assign rvc_jr_o     = (instr_i[15:12] == 4'b1000) & (instr_i[6:2] == 5'b00000) & is_rvc_o & (instr_i[1:0] == 2'b10);
    assign rvc_branch_o = ((instr_i[15:13] == OPCODE_C_BEQZ) | (instr_i[15:13] == OPCODE_C_BNEZ)) & is_rvc_o & (instr_i[1:0] == 2'b01);
    // check that rs1 is x1 or x5
    assign rvc_return_o = rvc_jr_o & ~instr_i[11] & ~instr_i[10] & ~instr_i[8] & instr_i[7];
    assign rvc_jalr_o   = (instr_i[15:12] == 4'b1001) & (instr_i[6:2] == 5'b00000) & is_rvc_o;
    assign rvc_call_o   = rvc_jalr_o;  // TODO: check that this captures calls

    // // differentiates between JAL and BRANCH opcode, JALR comes from BHT
    assign rvc_imm_o    = (instr_i[14]) ? {{56{instr_i[12]}}, instr_i[6:5], instr_i[2], instr_i[11:10], instr_i[4:3], 1'b0}
                                       : {{53{instr_i[12]}}, instr_i[8], instr_i[10:9], instr_i[6], instr_i[7], instr_i[2], instr_i[11], instr_i[5:3], 1'b0};
endmodule

// ------------------------------
// Branch Prediction
// ------------------------------

// branch target buffer
module btb #(
    parameter int NR_ENTRIES = 8
)(
    input  logic               clk_i,           // Clock
    input  logic               rst_ni,          // Asynchronous reset active low
    input  logic               flush_i,         // flush the btb

    input  logic [63:0]        vpc_i,           // virtual PC from IF stage
    input  btb_update_t        btb_update_i,    // update btb with this information
    output btb_prediction_t    btb_prediction_o // prediction from btb
);
    // number of bits which are not used for indexing
    localparam OFFSET = 1; // we are using compressed instructions so do use the lower 2 bits for prediction
    localparam ANTIALIAS_BITS = 8;
    // number of bits we should use for prediction
    localparam PREDICTION_BITS = $clog2(NR_ENTRIES) + OFFSET;
    // typedef for all branch target entries
    // we may want to try to put a tag field that fills the rest of the PC in-order to mitigate aliasing effects
    btb_prediction_t btb_d [NR_ENTRIES-1:0], btb_q [NR_ENTRIES-1:0];
    logic [$clog2(NR_ENTRIES)-1:0]          index, update_pc;

    assign index     = vpc_i[PREDICTION_BITS - 1:OFFSET];
    assign update_pc = btb_update_i.pc[PREDICTION_BITS - 1:OFFSET];

    // output matching prediction
    assign btb_prediction_o = btb_q[index];

    // -------------------------
    // Update Branch Prediction
    // -------------------------
    // update on a mis-predict
    always_comb begin : update_branch_predict
        btb_d = btb_q;

        if (btb_update_i.valid) begin
            btb_d[update_pc].valid = 1'b1;
            // the target address is simply updated
            btb_d[update_pc].target_address = btb_update_i.target_address;
            // as is the information whether this was a compressed branch
            btb_d[update_pc].is_lower_16    = btb_update_i.is_lower_16;
            // check if we should invalidate this entry, this happens in case we predicted a branch
            // where actually none-is (aliasing)
            if (btb_update_i.clear) begin
                btb_d[update_pc].valid = 1'b0;
            end
        end
    end

    // sequential process
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (~rst_ni) begin
            // Bias the branches to be taken upon first arrival
            for (int i = 0; i < NR_ENTRIES; i++)
                btb_q[i] <= '{default: 0};
        end else begin
            // evict all entries
            if (flush_i) begin
                for (int i = 0; i < NR_ENTRIES; i++) begin
                    btb_q[i].valid <=  1'b0;
                end
            end else begin
                btb_q <=  btb_d;
            end
        end
    end
endmodule

// return address stack
module ras #(
    parameter int unsigned DEPTH = 2
)(
    input  logic        clk_i,
    input  logic        rst_ni,
    input  logic        push_i,
    input  logic        pop_i,
    input  logic [63:0] data_i,
    output ras_t        data_o
);

    ras_t [DEPTH-1:0] stack_d, stack_q;

    assign data_o = stack_q[0];

    always_comb begin
        stack_d = stack_q;

        // push on the stack
        if (push_i) begin
            stack_d[0].ra = data_i;
            // mark the new return address as valid
            stack_d[0].valid = 1'b1;
            stack_d[DEPTH-1:1] = stack_q[DEPTH-2:0];
        end

        if (pop_i) begin
            stack_d[DEPTH-2:0] = stack_q[DEPTH-1:1];
            // we popped the value so invalidate the end of the stack
            stack_d[DEPTH-1].valid = 1'b0;
            stack_d[DEPTH-1].ra = 'b0;
        end
    end

    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (~rst_ni) begin
            stack_q <= '0;
        end else begin
            stack_q <= stack_d;
        end
    end
endmodule

// branch history table - 2 bit saturation counter
module bht #(
    parameter int unsigned NR_ENTRIES = 1024
)(
    input  logic            clk_i,
    input  logic            rst_ni,
    input  logic            flush_i,
    input  logic [63:0]     vpc_i,
    input  bht_update_t     bht_update_i,
    output bht_prediction_t bht_prediction_o
);
    localparam OFFSET = 2; // we are using compressed instructions so do not use the lower 2 bits for prediction
    localparam ANTIALIAS_BITS = 8;
    // number of bits we should use for prediction
    localparam PREDICTION_BITS = $clog2(NR_ENTRIES) + OFFSET;

    struct packed {
        logic       valid;
        logic [1:0] saturation_counter;
    } bht_d[NR_ENTRIES-1:0], bht_q[NR_ENTRIES-1:0];

    logic [$clog2(NR_ENTRIES)-1:0]  index, update_pc;
    logic [1:0]                     saturation_counter;

    assign index     = vpc_i[PREDICTION_BITS - 1:OFFSET];
    assign update_pc = bht_update_i.pc[PREDICTION_BITS - 1:OFFSET];
    // prediction assignment
    assign bht_prediction_o.valid = bht_q[index].valid;
    assign bht_prediction_o.taken = bht_q[index].saturation_counter == 2'b10;
    assign bht_prediction_o.strongly_taken = (bht_q[index].saturation_counter == 2'b11);
    always_comb begin : update_bht
        bht_d = bht_q;
        saturation_counter = bht_q[update_pc].saturation_counter;

        if (bht_update_i.valid) begin
            bht_d[update_pc].valid = 1'b1;

            if (saturation_counter == 2'b11) begin
                // we can safely decrease it
                if (~bht_update_i.taken)
                    bht_d[update_pc].saturation_counter = saturation_counter - 1;
            // then check if it saturated in the negative regime e.g.: branch not taken
            end else if (saturation_counter == 2'b00) begin
                // we can safely increase it
                if (bht_update_i.taken)
                    bht_d[update_pc].saturation_counter = saturation_counter + 1;
            end else begin // otherwise we are not in any boundaries and can decrease or increase it
                if (bht_update_i.taken)
                    bht_d[update_pc].saturation_counter = saturation_counter + 1;
                else
                    bht_d[update_pc].saturation_counter = saturation_counter - 1;
            end
        end
    end

    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (~rst_ni) begin
            for (int unsigned i = 0; i < NR_ENTRIES; i++)
                bht_q[i] <= '0;
        end else begin
            // evict all entries
            if (flush_i) begin
                for (int i = 0; i < NR_ENTRIES; i++) begin
                    bht_q[i].valid <=  1'b0;
                    bht_q[i].saturation_counter <= 2'b10;
                end
            end else begin
                bht_q <= bht_d;
            end
        end
    end
endmodule

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

typedef struct packed {
    logic        valid;
    logic [63:0] pc;             // update at PC
    logic [63:0] target_address;
    logic        is_lower_16;
    logic        clear;
} btb_update_t;

typedef struct packed {
    logic        valid;
    logic [63:0] target_address;
    logic        is_lower_16;
} btb_prediction_t;

typedef struct packed {
    logic        valid;
    logic [63:0] ra;
} ras_t;

typedef struct packed {
    logic        valid;
    logic [63:0] pc;          // update at PC
    logic        mispredict;
    logic        taken;
} bht_update_t;

typedef struct packed {
    logic       valid;
    logic       taken;
    logic       strongly_taken;
    logic [1:0] saturation_counter;
} bht_prediction_t;

module frontend #(
    parameter int unsigned BTB_ENTRIES = 8,
    parameter int unsigned BHT_ENTRIES = 32,
    parameter int unsigned RAS_DEPTH   = 2
)(
    input  logic               clk_i,              // Clock
    input  logic               rst_ni,             // Asynchronous reset active low
    input  logic               flush_i,            // flush request for PCGEN
    input  logic               flush_bp_i,         // flush branch prediction
    input  logic               i_fence_i,          // instruction fence in
    input  logic               flush_itlb_i,       // flush itlb
    // global input
    input  logic [63:0]        boot_addr_i,
    input  logic               fetch_enable_i,     // start fetching instructions
    // Set a new PC
    // mispredict
    input  branchpredict_t     resolved_branch_i,  // from controller signaling a branch_predict -> update BTB
    // from commit, when flushing the whole pipeline
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
    AXI_BUS.Master             axi,
    output logic               l1_icache_miss_o,    // instruction cache missed
    //
    // instruction output port -> to processor back-end
    output fetch_entry_t       fetch_entry_o,       // fetch entry containing all relevant data for the ID stage
    output logic               fetch_entry_valid_o, // instruction in IF is valid
    input  logic               fetch_ack_i          // ID acknowledged this instruction
);

    logic push_i;
    logic pop_i;
    logic [63:0] data_i;
    ras_t data_o;
    bht_update_t bht_update_i;
    bht_prediction_t bht_prediction_o;
    logic [63:0] vpc_i;
    btb_update_t btb_update_i;
    btb_prediction_t btb_prediction_o;

    ras #(
        .DEPTH(RAS_DEPTH)
    ) i_ras (
        .clk_i  ( clk_i  ),
        .rst_ni ( rst_ni ),
        .push_i ( push_i ),
        .pop_i  ( pop_i  ),
        .data_i ( data_i ),
        .data_o ( data_o )
    );

    btb #(
        .NR_ENTRIES(BTB_ENTRIES)
    ) i_btb (
        .clk_i            ( clk_i            ),
        .rst_ni           ( rst_ni           ),
        .flush_i          ( flush_i          ),
        .vpc_i            ( vpc_i            ),
        .btb_update_i     ( btb_update_i     ),
        .btb_prediction_o ( btb_prediction_o )
    );

    bht #(
        .NR_ENTRIES(BHT_ENTRIES)
    ) i_bht (
        .clk_i            ( clk_i            ),
        .rst_ni           ( rst_ni           ),
        .flush_i          ( flush_i          ),
        .vpc_i            ( vpc_i            ),
        .bht_update_i     ( bht_update_i     ),
        .bht_prediction_o ( bht_prediction_o )
    );


    logic [11:0] index_i;
    logic [43:0] tag_i;
icache #(.SET_ASSOCIATIVITY(4)) i_icache (
    .clk_i  (clk_i  ),
    .rst_ni (rst_ni ),
    .flush_i( ),
    .index_i(index_i),
    .tag_i  (tag_i  ),
    .data_o (  ),
    .req_i  (),
    .kill_req_i (),
    .ready_o   (),
    .valid_o (),
    .axi       (axi),
    .miss_o    (l1_icache_miss_o)
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
    output logic        rvc_branch_o,
    output logic        rvc_jump_o,
    output logic        rvc_jr_o,
    output logic        rvc_return_o,
    output logic        rvc_jalr_o,
    output logic        rvc_call_o,
    output logic [63:0] rvi_imm_o,
    output logic [63:0] rvc_imm_o,
    output logic        rvi_branch_o,
    output logic        rvi_jalr_o,
    output logic        rvi_jump_o
);
    assign is_rvc_o     = (instr_i[1:0] != 2'b00);
    // check that rs1 is either x1 or x5 and that rs1 is not x1 or x5, TODO: check the fact about bit 7
    assign rvi_return_o = rvi_jalr_o & ~instr_i[7] & ~instr_i[19] & ~instr_i[18] & instr_i[17] & ~instr_i[15];
    assign rvi_call_o   = (rvi_jalr_o || rvi_jump_o) & instr_i[7]; // TODO: check that this captures calls
    assign rvc_branch_o = (instr_i[15:13] == OPCODE_C_BEQZ) | (instr_i[15:13] == OPCODE_C_BNEZ);
    // opcode JAL
    assign rvc_jump_o   = (instr_i[15:13] == OPCODE_C_J);
    assign rvc_jr_o     = (instr_i[15:12] == 4'b1000) & (instr_i[6:2] == 5'b00000);
    // check that rs1 is x1 or x5
    assign rvc_return_o = rvc_jr_o & ~instr_i[11] & ~instr_i[10] & ~instr_i[8] & ~instr_i[7];
    assign rvc_jalr_o   = (instr_i[15:12] == 4'b1001) & (instr_i[6:2] == 5'b00000);
    assign rvc_call_o   = rvc_jalr_o;  // TODO: check that this captures calls

    // differentiates between JAL and BRANCH opcode, JALR comes from BHT
    assign rvi_imm_o    = (instr_i[3]) ? uj_imm(instr_i) : sb_imm(instr_i);
    // // differentiates between JAL and BRANCH opcode, JALR comes from BHT
    assign rvc_imm_o    = (instr_i[14]) ? {{56{instr_i[12]}}, instr_i[6:5], instr_i[2], instr_i[11:10], instr_i[4:3], 1'b0}
                                       : {{53{instr_i[12]}}, instr_i[8], instr_i[10:9], instr_i[6], instr_i[7], instr_i[2], instr_i[11], instr_i[5:3], 1'b0};

    assign rvi_branch_o = (instr_i[6:0] == OPCODE_BRANCH) ? 1'b1 : 1'b0;
    assign rvi_jalr_o   = (instr_i[6:0] == OPCODE_JALR)   ? 1'b1 : 1'b0;
    assign rvi_jump_o   = (instr_i[6:0] == OPCODE_JAL)    ? 1'b1 : 1'b0;
endmodule

// ------------------------------
// Instruction Cache
// ------------------------------
module icache #(
        parameter int unsigned SET_ASSOCIATIVITY = 4,
        parameter int unsigned INDEX_WIDTH       = 12, // in bit
        parameter int unsigned TAG_WIDTH         = 44, // in bit
        parameter int unsigned CACHE_LINE_WIDTH  = 64, // in bit
        parameter int unsigned FETCH_WIDTH       = 32  // in bit
    )(
        input  logic                     clk_i,
        input  logic                     rst_ni,
        input  logic                     flush_i,    // flush the icache, flush and kill have to be asserted together
        input  logic                     req_i,      // we request a new word
        input  logic                     kill_req_i, // kill the current request
        output logic                     ready_o,    // icache is ready
        input  logic [INDEX_WIDTH-1:0]   index_i,    // 1st cycle: 12 bit index
        input  logic [TAG_WIDTH-1:0]     tag_i,      // 2nd cycle: physical tag
        output logic [FETCH_WIDTH-1:0]   data_o,     // 2+ cycle out: tag
        output logic                     valid_o,    // signals a valid read
        output logic                     miss_o,     // we missed on the cache
        AXI_BUS.Master                   axi
    );

    localparam BYTE_OFFSET = $clog2(CACHE_LINE_WIDTH/8); // 3
    localparam ICACHE_NUM_WORD = 2**(INDEX_WIDTH - BYTE_OFFSET);

    // registers
    enum logic [3:0] { FLUSH, IDLE, TAG_CMP, WAIT_AXI_R_RESP, WAIT_KILLED_REFILL, WAIT_KILLED_AXI_R_RESP,
                       REDO_REQ, WAIT_TAG_SAVED, REFILL
                     }                      state_d, state_q;
    logic [$clog2(ICACHE_NUM_WORD)-1:0]     cnt_d, cnt_q;
    logic [INDEX_WIDTH-1:0]                 index_d, index_q;
    logic [TAG_WIDTH-1:0]                   tag_d, tag_q;
    logic [SET_ASSOCIATIVITY-1:0]           evict_way_d, evict_way_q;
    logic                                   flushing_d, flushing_q;

    // signals
    logic [SET_ASSOCIATIVITY-1:0]         req;           // request to memory array
    logic [$clog2(ICACHE_NUM_WORD)-1:0]   addr;          // this is a cache-line address, to memory array
    logic                                 we;            // write enable to memory array
    logic [SET_ASSOCIATIVITY-1:0]         hit;           // hit from tag compare
    logic [BYTE_OFFSET-1:2]               idx;           // index in cache line
    logic                                 update_lfsr;   // shift the LFSR
    logic [SET_ASSOCIATIVITY-1:0]         random_way;    // random way select from LFSR
    logic [SET_ASSOCIATIVITY-1:0]         way_valid;     // bit string which contains the zapped valid bits
    logic [$clog2(SET_ASSOCIATIVITY)-1:0] repl_invalid;  // first non-valid encountered
    logic                                 repl_w_random; // we need to switch repl strategy since all are valid
    logic [TAG_WIDTH-1:0]                 tag;           // tag to do comparison with

    // tag + valid bit read/write data
    struct packed {
        logic                 valid;
        logic [TAG_WIDTH-1:0] tag;
    } tag_rdata [SET_ASSOCIATIVITY-1:0], tag_wdata;

    logic [CACHE_LINE_WIDTH-1:0] data_rdata [SET_ASSOCIATIVITY-1:0], data_wdata;

    for (genvar i = 0; i < SET_ASSOCIATIVITY; i++) begin : sram_block
        // ------------
        // Tag RAM
        // ------------
        sram #(
            // tag + valid bit
            .DATA_WIDTH ( TAG_WIDTH + 1   ),
            .NUM_WORDS  ( ICACHE_NUM_WORD )
        ) tag_sram (
            .clk_i     ( clk_i            ),
            .req_i     ( req[i]           ),
            .we_i      ( we               ),
            .addr_i    ( addr             ),
            .wdata_i   ( tag_wdata        ),
            .be_i      (  '1              ),
            .rdata_o   ( tag_rdata[i]     )
        );
        // ------------
        // Data RAM
        // ------------
        sram #(
            .DATA_WIDTH ( CACHE_LINE_WIDTH  ),
            .NUM_WORDS  ( ICACHE_NUM_WORD   )
        ) data_sram (
            .clk_i     ( clk_i              ),
            .req_i     ( req[i]             ),
            .we_i      ( we                 ),
            .addr_i    ( addr               ),
            .wdata_i   ( data_wdata         ),
            .be_i      ( '1                 ),
            .rdata_o   ( data_rdata[i]      )
        );
    end
    // --------------------
    // Tag Comparison
    // --------------------
    for (genvar i = 0; i < SET_ASSOCIATIVITY; i++) begin
        assign hit[i] = (tag_rdata[i].tag == tag) ? tag_rdata[i].valid : 1'b0;
    end

    `ifndef SYNTHESIS
    `ifndef VERILATOR
    // assert that cache only hits on one way
    assert property (
      @(posedge clk_i) $onehot0(hit)) else begin $error("[icache] Hit should be one-hot encoded"); $stop(); end
    `endif
    `endif

    // ------------------
    // Way Select
    // ------------------
    assign idx = index_q[BYTE_OFFSET-1:2];
    // cacheline selected by hit
    logic [CACHE_LINE_WIDTH/FETCH_WIDTH-1:0][FETCH_WIDTH-1:0] selected_cl;
    logic [CACHE_LINE_WIDTH-1:0] selected_cl_flat;

    for (genvar i = 0; i < CACHE_LINE_WIDTH; i++) begin
        logic [SET_ASSOCIATIVITY-1:0] hit_masked_cl;

        for (genvar j = 0; j < SET_ASSOCIATIVITY; j++)
            assign hit_masked_cl[j] = data_rdata[j][i] & hit[j];

        assign selected_cl_flat[i] = |hit_masked_cl;
    end

    assign selected_cl = selected_cl_flat;
    // maybe re-work if critical
    assign data_o = selected_cl[idx];

    for (genvar i = 0; i < SET_ASSOCIATIVITY; i++) begin
        assign way_valid[i] = tag_rdata[i].valid;
    end

    // ------------------
    // AXI Plumbing
    // ------------------
    assign axi.aw_valid  = '0;
    assign axi.aw_addr   = '0;
    assign axi.aw_prot   = '0;
    assign axi.aw_region = '0;
    assign axi.aw_len    = '0;
    assign axi.aw_size   = 3'b000;
    assign axi.aw_burst  = 2'b00;
    assign axi.aw_lock   = '0;
    assign axi.aw_cache  = '0;
    assign axi.aw_qos    = '0;
    assign axi.aw_id     = '0;
    assign axi.aw_user   = '0;

    assign axi.w_valid   = '0;
    assign axi.w_data    = '0;
    assign axi.w_strb    = '0;
    assign axi.w_user    = '0;
    assign axi.w_last    = 1'b0;
    assign axi.b_ready   = 1'b0;

    assign axi.ar_prot   = '0;
    assign axi.ar_region = '0;
    assign axi.ar_len    = 8'h00;
    assign axi.ar_size   = 3'b011;
    assign axi.ar_burst  = 2'b01;
    assign axi.ar_lock   = '0;
    assign axi.ar_cache  = '0;
    assign axi.ar_qos    = '0;
    assign axi.ar_id     = '0;
    assign axi.ar_user   = '0;

    assign axi.r_ready   = 1'b1;

    // ------------------
    // Cache Ctrl
    // ------------------
    always_comb begin : cache_ctrl
        // default assignments
        state_d     = state_q;
        cnt_d       = cnt_q;
        index_d     = index_q;
        tag_d       = tag_q;
        evict_way_d = evict_way_q;
        flushing_d  = flushing_q;

        req         = '0;
        addr        = index_i[INDEX_WIDTH-1:BYTE_OFFSET];
        we          = 1'b0;
        data_wdata  = '0;
        tag_wdata   = '0;
        ready_o     = 1'b0;
        tag         = tag_i;
        valid_o     = 1'b0;
        update_lfsr = 1'b0;
        miss_o      = 1'b0;

        axi.ar_valid  = 1'b0;
        axi.ar_addr   = '0;

        case (state_q)
            // ~> we are ready to receive a new request
            IDLE: begin
                ready_o = 1'b1;
                // we are getting a new request
                if (req_i) begin
                    // request the content of all arrays
                    req = '1;
                    // save the index
                    index_d = index_i;
                    state_d = TAG_CMP;
                end

                // go to flushing state
                if (flush_i || flushing_q)
                    state_d = FLUSH;

            end
            // ~> compare the tag
            TAG_CMP: begin
                // we have a hit
                if (|hit) begin
                    ready_o = 1'b1;
                    valid_o = 1'b1;
                    // we've got another request
                    if (req_i) begin
                        // request the content of all arrays
                        req = '1;
                        // save the index and stay in compare mode
                        index_d = index_i;
                    // no new request -> go back to idle
                    end else begin
                        state_d = IDLE;
                    end
                end else begin
                    state_d     = REFILL;
                    evict_way_d = '0;
                    // save tag
                    tag_d       = tag_i;
                    miss_o      = 1'b1;
                    // get way which to replace
                    if (repl_w_random) begin
                        evict_way_d = random_way;
                        // shift the lfsr
                        update_lfsr = 1'b1;
                    end else begin
                        evict_way_d[repl_invalid] = 1'b1;
                    end
                end
            end
            // ~> request a cache-line refill
            REFILL: begin
                axi.ar_valid  = 1'b1;
                axi.ar_addr[INDEX_WIDTH+TAG_WIDTH-1:0] = {tag_q, index_q};

                if (kill_req_i)
                    state_d = WAIT_KILLED_REFILL;

                if (axi.ar_ready)
                    state_d = (kill_req_i) ? WAIT_KILLED_AXI_R_RESP : WAIT_AXI_R_RESP;
            end
            // ~> wait for the read response
            // TODO: Handle responses for arbitrary cache line widths
            WAIT_AXI_R_RESP: begin

                state_d = REDO_REQ;
                req     = evict_way_q;
                addr    = index_q[INDEX_WIDTH-1:BYTE_OFFSET];

                if (axi.r_valid) begin
                    we = 1'b1;
                    tag_wdata.tag = tag_q;
                    tag_wdata.valid = 1'b1;
                    data_wdata = axi.r_data;
                end

                if (kill_req_i)
                    state_d = WAIT_KILLED_AXI_R_RESP;

                if (axi.r_last) begin
                    state_d = (kill_req_i) ? IDLE : REDO_REQ;
                end
            end
            // ~> redo the request,
            REDO_REQ: begin
                req = '1;
                addr = index_q[INDEX_WIDTH-1:BYTE_OFFSET];
                tag = tag_q;
                state_d = WAIT_TAG_SAVED;
            end
            // we already saved the tag -> apply it
            WAIT_TAG_SAVED: begin
                tag     = tag_q;
                state_d = IDLE;
                valid_o = 1'b1;
            end
            // we need to wait for some AXI responses to come back
            // here for the AW valid
            WAIT_KILLED_REFILL: begin
                if (axi.aw_valid)
                    state_d = IDLE;
            end
            // and here for the last R valid
            WAIT_KILLED_AXI_R_RESP: begin
                if (axi.r_last)
                    state_d = IDLE;
            end
            // ~> we are coming here after reset or when a flush was requested
            FLUSH: begin
                addr    = cnt_q;
                cnt_d   = cnt_q + 1;
                req     = '1;
                we      = 1;
                // we've finished flushing, go back to idle
                if (cnt_q == ICACHE_NUM_WORD - 1) begin
                    state_d = IDLE;
                    flushing_d = 1'b0;
                end
            end

            default : state_d = IDLE;
        endcase

        if (kill_req_i && !(state_q inside {REFILL, WAIT_AXI_R_RESP, WAIT_KILLED_REFILL, WAIT_KILLED_AXI_R_RESP})) begin
            state_d = IDLE;
        end

        if (flush_i) begin
            flushing_d = 1'b1;
        end
    end

    ff1 #(
        .LEN ( SET_ASSOCIATIVITY )
    ) i_ff1 (
        .in_i        ( ~way_valid    ),
        .first_one_o ( repl_invalid  ),
        .no_ones_o   ( repl_w_random )
    );

    // -----------------
    // Replacement LFSR
    // -----------------
    lfsr #(.WIDTH (SET_ASSOCIATIVITY)) i_lfsr (
        .clk_i          ( clk_i       ),
        .rst_ni         ( rst_ni      ),
        .en_i           ( update_lfsr ),
        .refill_way_oh  ( random_way  ),
        .refill_way_bin (             ) // left open
    );


    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (~rst_ni) begin
            state_q     <= FLUSH;
            cnt_q       <= '0;
            index_q     <= '0;
            tag_q       <= '0;
            evict_way_q <= '0;
            flushing_q  <= 1'b0;
        end else begin
            state_q     <= state_d;
            cnt_q       <= cnt_d;
            index_q     <= index_d;
            tag_q       <= tag_d;
            evict_way_q <= evict_way_d;
            flushing_q  <= flushing_d;
        end
    end

    `ifndef SYNTHESIS
        initial begin
            assert ($bits(axi.aw_addr) == 64) else $fatal(1, "Ariane needs a 64-bit bus");
            assert (CACHE_LINE_WIDTH == 64) else $fatal(1, "Instruction cacheline width needs to be 64 for the moment");
        end
    `endif
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
    localparam OFFSET = 2; // we are using compressed instructions so do not use the lower 2 bits for prediction
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
    parameter int unsigned NR_ENTRIES = 64
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

    bht_prediction_t                        bht_d[NR_ENTRIES-1:0], bht_q[NR_ENTRIES-1:0];
    logic [$clog2(NR_ENTRIES)-1:0]          index, update_pc;
    logic [1:0]     saturation_counter;

    assign index     = vpc_i[PREDICTION_BITS - 1:OFFSET];
    assign update_pc = bht_update_i.pc[PREDICTION_BITS - 1:OFFSET];
    // prediction assignment
    assign bht_prediction_o = bht_q[index];

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
                end
            end else begin
                bht_q <= bht_d;
            end
        end
    end
endmodule

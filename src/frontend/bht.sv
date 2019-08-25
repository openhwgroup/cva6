// Copyright 2018 - 2019 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 2.0 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-2.0. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// Author: Florian Zaruba, ETH Zurich
// Date: 08.02.2018
// Migrated: Luis Vitorio Cargnini, IEEE
// Date: 09.06.2018

// branch history table - 2 bit saturation counter
module bht #(
    parameter int unsigned NR_ENTRIES = 1024,
    parameter int unsigned NR_GLOBAL_HISTORIES = 4
)(
    input  logic                                    clk_i,
    input  logic                                    rst_ni,
    input  logic                                    flush_i,
    input  logic                                    flush_ftq_i,
    input  logic                                    debug_mode_i,
    input  logic [63:0]                             vpc_i,
    input  logic [$clog2(ariane_pkg::INSTR_PER_FETCH)-1:0] push_instr_cnt_i,
    input  logic                                    instr_queue_overflow_i,
    input  logic [63:0]                             instr_queue_replay_addr_i,
    input  logic                                    serving_unaligned_i, // we have an unalinged instruction at the beginning
    input  ariane_pkg::bht_update_t                 bht_update_i,
    input  logic [ariane_pkg::INSTR_PER_FETCH-1:0]  valid_i,
    input  logic [ariane_pkg::INSTR_PER_FETCH-1:0]  is_branch_i,
    input  cf_t  [ariane_pkg::INSTR_PER_FETCH-1:0]  cf_type_i,
    output logic                                    ftq_overflow_o,
    // we potentially need INSTR_PER_FETCH predictions/cycle
    output ariane_pkg::bht_prediction_t [ariane_pkg::INSTR_PER_FETCH-1:0] bht_prediction_o
);
    // the last bit is always zero, we don't need it for indexing
    localparam OFFSET = 1;
    // re-shape the branch history table
    localparam NR_ROWS = NR_ENTRIES / ariane_pkg::INSTR_PER_FETCH;
    // number of bits needed to index the row
    localparam ROW_ADDR_BITS = $clog2(ariane_pkg::INSTR_PER_FETCH);
    // number of bits we should use for prediction
    localparam PREDICTION_BITS = $clog2(NR_ROWS) + OFFSET + ROW_ADDR_BITS;
    // number of bits of the table index
    localparam INDEX_BITS = $clog2(NR_ROWS);

    localparam NR_GLOBAL_HISTORIES_REMAINDER = NR_GLOBAL_HISTORIES % INDEX_BITS;
    localparam EXTENDED_GHR_LEN = INDEX_BITS > NR_GLOBAL_HISTORIES ? INDEX_BITS :
				                            (NR_GLOBAL_HISTORIES_REMAINDER == 0 ? NR_GLOBAL_HISTORIES :
                                    (NR_GLOBAL_HISTORIES + INDEX_BITS - NR_GLOBAL_HISTORIES_REMAINDER));

    // we are not interested in a ll bits of the address
    unread i_unread (.d_i(|vpc_i));

    // global history register
    logic [NR_GLOBAL_HISTORIES-1:0] ghr_d, ghr_q;

    // this is the struct which provide the information from the branch predictor
    // and we will use it to update the branch history table.
    typedef struct packed {
        logic [INDEX_BITS-1:0] gshare_index;
        logic [$clog2(ariane_pkg::INSTR_PER_FETCH):0] bp_count;  // count how many valid branch predictions in this fetch
        logic serving_unaligned;
        logic [ariane_pkg::TAG_BITS-1:0] tag;
    } ftq_entry_t;

    // signals to make the predictions
    logic [63:0] realigned_vpc;
    logic [EXTENDED_GHR_LEN-1:0] extended_ghr;
    logic [$clog2(NR_ROWS)-1:0] gshare_index;
    logic [ariane_pkg::INSTR_PER_FETCH-1:0] valid_taken_cf;
    logic [ariane_pkg::INSTR_PER_FETCH-1:0] is_replay;  // replay logic per instruction
    logic [ariane_pkg::INSTR_PER_FETCH-1:0] is_valid_branch;

    // fetch target queue signals
    logic [$clog2(ariane_pkg::FETCH_FIFO_DEPTH)-1:0] ftq_usage;
    ftq_entry_t  ftq_entry_i, ftq_entry_o;
    logic pop_ftq, push_ftq;
    logic full_ftq;
    logic empty_ftq;

    // count the number of rest valid predictions in that entry
    logic [$clog2(ariane_pkg::INSTR_PER_FETCH):0] bp_count_d, bp_count_q;
    logic [$clog2(ariane_pkg::INSTR_PER_FETCH):0] pop_count;

    struct packed {
        logic [1:0] saturation_counter;
        logic [ariane_pkg::TAG_BITS-1:0] tag;
    } bht_d[NR_ROWS-1:0][ariane_pkg::INSTR_PER_FETCH-1:0], bht_q[NR_ROWS-1:0][ariane_pkg::INSTR_PER_FETCH-1:0];

    // update the prediction table
    logic                        is_unaligned_instr;
    logic [63:0]                 realigned_update_pc;
    logic [$clog2(NR_ROWS)-1:0]  update_pc;
    logic [ROW_ADDR_BITS-1:0]    update_row_index;
    logic [1:0]                  saturation_counter;

    // compute the index using gshare predictor
    // if the global history is shorter than the index bits, simply xor them
    // if the global history is longer than the index bits, than we do folded xor
    // for example, if the history is 1 0 1 0 1 1 1 1 and the index bits are 0 1 1
    // then we compute gshare index as (110) ^ (101) ^ (111) ^ (011)
    always_comb begin : gen_gshare_index
        gshare_index = realigned_vpc[PREDICTION_BITS - 1:ROW_ADDR_BITS + OFFSET];
        // extend global history register to the length of multiplication of index bits
        extended_ghr = {{{INDEX_BITS-NR_GLOBAL_HISTORIES_REMAINDER}{1'b0}}, ghr_q};
        for (int unsigned i = 0; i < NR_GLOBAL_HISTORIES; i = i + INDEX_BITS) begin
            gshare_index ^= extended_ghr[i +: INDEX_BITS];
        end
    end

    // realigned pc address to fetch block width
    assign realigned_vpc = {vpc_i[63:ROW_ADDR_BITS+1], (ROW_ADDR_BITS+1)'(0)};
    assign ftq_entry_i = { gshare_index,                                                  // gshare index
                           pop_count,                                                     // valid branch prediction count
                           serving_unaligned_i,                                           // serving an unaligned instruction
                           realigned_vpc[ROW_ADDR_BITS + OFFSET +: ariane_pkg::TAG_BITS]  // tag
                         };
    assign push_ftq = (|is_valid_branch);

    assign realigned_update_pc = bht_update_i.pc + 2;
    assign is_unaligned_instr = ftq_entry_o.serving_unaligned & (&bht_update_i.pc[ROW_ADDR_BITS + OFFSET - 1:OFFSET]);
    assign pop_ftq = bht_update_i.valid & ((bp_count_q == 1) || ftq_entry_o.bp_count == 1);
    assign update_row_index = is_unaligned_instr ? 0 : bht_update_i.pc[ROW_ADDR_BITS + OFFSET - 1:OFFSET];
    assign update_pc = ftq_entry_o.gshare_index;
    assign ftq_overflow_o = full_ftq & push_ftq;

    // if the incoming instruction is a replay at the replay address, then the rest of the fetched
    // instruction should also be replay. For example, in 64 bit fetch if the replay starts from 0x42,
    // the replay mask should be 1 1 1 0 from the highest to lowest.
    assign is_replay = {ariane_pkg::INSTR_PER_FETCH{instr_queue_overflow_i}} << push_instr_cnt_i;
    // an instruction is a valid branch instruction to push to fetch target queue if:
    // 1) it is a valid branch instruction
    // 2) it is not a replay
    // 3) no taken control flow before it in the same fetch block
    for (genvar i = 0; i < ariane_pkg::INSTR_PER_FETCH; i++) begin
        // check if the instructions are valid control flows
        assign valid_taken_cf[i] = valid_i[i] & (cf_type_i[i] != ariane_pkg::NoCF);

        if (i == 0) begin
            assign is_valid_branch[i] = is_branch_i[i] & ~is_replay[i];
        end else begin
            assign is_valid_branch[i] = is_branch_i[i] & ~(|valid_taken_cf[i-1:0]) & ~is_replay[i];
        end
    end

    // prediction assignment
    for (genvar i = 0; i < ariane_pkg::INSTR_PER_FETCH; i++) begin : gen_bht_output
        assign bht_prediction_o[i].valid = bht_q[ftq_entry_i.gshare_index][i].tag == ftq_entry_i.tag;
        assign bht_prediction_o[i].taken = bht_q[ftq_entry_i.gshare_index][i].saturation_counter[1] == 1'b1;
    end

    // count the numbers of valid branch predictions in this fetch
    popcount #(
      .INPUT_WIDTH   ( ariane_pkg::INSTR_PER_FETCH )
    ) i_popcount_bp (
      .data_i     ( is_valid_branch ),
      .popcount_o ( pop_count       )
    );

    fifo_v3 #(
      .DEPTH      ( ariane_pkg::FTQ_FIFO_DEPTH   ),
      .dtype      ( ftq_entry_t                  )
    ) i_fifo_ftq (
      .clk_i      ( clk_i                        ),
      .rst_ni     ( rst_ni                       ),
      .flush_i    ( flush_i | flush_ftq_i        ),
      .testmode_i ( 1'b0                         ),
      .full_o     ( full_ftq                     ),
      .empty_o    ( empty_ftq                    ),
      .usage_o    ( ftq_usage                    ),
      .data_i     ( ftq_entry_i                  ),
      .push_i     ( push_ftq & ~full_ftq         ),
      .data_o     ( ftq_entry_o                  ),
      .pop_i      ( pop_ftq                      )
    );

    always_comb begin : update_bht
        bht_d = bht_q;
        saturation_counter = bht_q[update_pc][update_row_index].saturation_counter;

        ghr_d = ghr_q;

        if (bp_count_q == '0) begin
            bp_count_d = empty_ftq ? '0 : ftq_entry_o.bp_count;
        end else begin
            bp_count_d = bp_count_q;
        end

        if (bht_update_i.valid && !debug_mode_i) begin

            // shift the new branch result into the global history buffer at least significant bit
            for (int unsigned i = 1; i < NR_GLOBAL_HISTORIES; i++) begin
                ghr_d[i] = ghr_q[i-1];
            end
            ghr_d[0] = bht_update_i.taken;

            // update the valid branch prediction counter
            // if the count is decreased to zero due to the previous bp, then the counter should be updated
            // to the number of the new ftq entry. Else the counter should be decreased by 1.
            if (bp_count_q == '0) begin
                bp_count_d = ftq_entry_o.bp_count - 1;
            end
            else begin
                bp_count_d = bp_count_q - 1;
            end

            if (bht_q[update_pc][update_row_index].tag != ftq_entry_o.tag) begin
                // reset the counter
                if (!bht_update_i.taken)
                    bht_d[update_pc][update_row_index].saturation_counter = 2'b01;
                else
                    bht_d[update_pc][update_row_index].saturation_counter = 2'b10;
            end else if (saturation_counter == 2'b11) begin
                // we can safely decrease it
                if (!bht_update_i.taken)
                    bht_d[update_pc][update_row_index].saturation_counter = saturation_counter - 1;
            // then check if it saturated in the negative regime e.g.: branch not taken
            end else if (saturation_counter == 2'b00) begin
                // we can safely increase it
                if (bht_update_i.taken)
                    bht_d[update_pc][update_row_index].saturation_counter = saturation_counter + 1;
            end else begin // otherwise we are not in any boundaries and can decrease or increase it
                if (bht_update_i.taken)
                    bht_d[update_pc][update_row_index].saturation_counter = saturation_counter + 1;
                else
                    bht_d[update_pc][update_row_index].saturation_counter = saturation_counter - 1;
            end

            // update the tag
            bht_d[update_pc][update_row_index].tag = ftq_entry_o.tag;

        end
    end

    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
            for (int unsigned i = 0; i < NR_ROWS; i++) begin
                for (int j = 0; j < ariane_pkg::INSTR_PER_FETCH; j++) begin
                    bht_q[i][j] <= '0;
                end
            end
            ghr_q <= '0;
            bp_count_q <= '0;
        end else begin
            // evict all entries
            if (flush_i) begin
                for (int i = 0; i < NR_ROWS; i++) begin
                    for (int j = 0; j < ariane_pkg::INSTR_PER_FETCH; j++) begin
                        bht_q[i][j].saturation_counter <= 2'b10;
                    end
                end
                ghr_q <= '0;
            end else begin
                bht_q <= bht_d;
                ghr_q <= ghr_d;
            end

            if (flush_i || flush_ftq_i) begin
                bp_count_q <= '0;
            end else begin
                bp_count_q <= bp_count_d;
            end
        end
    end
endmodule

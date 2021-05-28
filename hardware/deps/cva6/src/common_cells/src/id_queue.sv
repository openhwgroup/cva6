// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// ID Queue
//
// In an ID queue, every element has a numeric ID. Among all elements that have the same ID, the ID
// queue preserves FIFO order.
//
// This ID queue implementation allows to either push (through the `inp_*` signals) or pop (through
// the `oup_*` signals) one element per clock cycle. The `inp_` port has priority and grants a
// request iff the queue is not full. The `oup_` port dequeues an element iff `oup_pop_i` is
// asserted during an `oup_` handshake; otherwise, it performs a non-destructive read. `oup_data_o`
// is valid iff `oup_data_valid_o` is asserted during an `oup_` handshake. If `oup_data_valid_o` is
// not asserted, the queue did not contain an element with the provided ID.
//
// This ID queue additionally provides the `exists_` port, which searches for an element anywhere in
// the queue. The comparison performed during the search can be masked: for every bit that is
// asserted in `exists_mask_i`, the corresponding bit in the queue element and in `exists_data_i`
// must be equal for a match; the other bits are not compared. If masking is not required, tie
// `exists_mask_i_ to `'1` and the synthesizer should simplify the comparisons to unmasked ones. The
// `exists_` port operates independently of the `inp_` and `oup_` ports. If the `exists_` port is
// unused, tie `exists_req_i` to `1'b0` and the synthesizer should remove the internal comparators.
//
// This ID queue can store at most `CAPACITY` elements, independent of their ID. Let
// - C = `CAPACITY`
// - B = $bits(data_t)
// - I = 2**`ID_WIDTH`
// Then
// - the queue element storage requires O(C * (B + log2(C))) bit
// - the ID table requires O(H * log2(C)) bit, where H = min(C, I)
//
// Maintainers:
// - Andreas Kurth <akurth@iis.ee.ethz.ch>

module id_queue #(
    parameter int ID_WIDTH  = 0,
    parameter int CAPACITY  = 0,
    parameter type data_t   = logic,
    // Dependent parameters, DO NOT OVERRIDE!
    localparam type id_t    = logic[ID_WIDTH-1:0],
    localparam type mask_t  = logic[$bits(data_t)-1:0]
) (
    input  logic    clk_i,
    input  logic    rst_ni,

    input  id_t     inp_id_i,
    input  data_t   inp_data_i,
    input  logic    inp_req_i,
    output logic    inp_gnt_o,

    input  data_t   exists_data_i,
    input  mask_t   exists_mask_i,
    input  logic    exists_req_i,
    output logic    exists_o,
    output logic    exists_gnt_o,

    input  id_t     oup_id_i,
    input  logic    oup_pop_i,
    input  logic    oup_req_i,
    output data_t   oup_data_o,
    output logic    oup_data_valid_o,
    output logic    oup_gnt_o
);

    // Capacity of the head-tail table, which associates an ID with corresponding head and tail
    // indices.
    localparam int N_IDS = 2**ID_WIDTH;
    localparam int HT_CAPACITY = (N_IDS <= CAPACITY) ? N_IDS : CAPACITY;
    localparam int unsigned HT_IDX_WIDTH = HT_CAPACITY == 1 ? 1 : $clog2(HT_CAPACITY);
    localparam int unsigned LD_IDX_WIDTH = CAPACITY    == 1 ? 1 : $clog2(CAPACITY);

    // Type for indexing the head-tail table.
    typedef logic [HT_IDX_WIDTH-1:0] ht_idx_t;

    // Type for indexing the lined data table.
    typedef logic [LD_IDX_WIDTH-1:0] ld_idx_t;

    // Type of an entry in the head-tail table.
    typedef struct packed {
        id_t        id;
        ld_idx_t    head,
                    tail;
        logic       free;
    } head_tail_t;

    // Type of an entry in the linked data table.
    typedef struct packed {
        data_t      data;
        ld_idx_t    next;
        logic       free;
    } linked_data_t;

    head_tail_t [HT_CAPACITY-1:0]   head_tail_d,    head_tail_q;

    linked_data_t [CAPACITY-1:0]    linked_data_d,  linked_data_q;

    logic                           full,
                                    match_id_valid,
                                    no_id_match;

    logic [HT_CAPACITY-1:0]         head_tail_free,
                                    idx_matches_id;

    logic [CAPACITY-1:0]            exists_match,
                                    linked_data_free;

    id_t                            match_id;

    ht_idx_t                        head_tail_free_idx,
                                    match_idx;

    ld_idx_t                        linked_data_free_idx;

    // Find the index in the head-tail table that matches a given ID.
    for (genvar i = 0; i < HT_CAPACITY; i++) begin: gen_idx_match
        assign idx_matches_id[i] = match_id_valid && (head_tail_q[i].id == match_id) &&
                !head_tail_q[i].free;
    end
    assign no_id_match = !(|idx_matches_id);
    onehot_to_bin #(
        .ONEHOT_WIDTH (HT_CAPACITY)
    ) i_id_ohb (
        .onehot (idx_matches_id),
        .bin    (match_idx)
    );

    // Find the first free index in the head-tail table.
    for (genvar i = 0; i < HT_CAPACITY; i++) begin: gen_head_tail_free
        assign head_tail_free[i] = head_tail_q[i].free;
    end
    lzc #(
        .WIDTH  (HT_CAPACITY),
        .MODE   (0)         // Start at index 0.
    ) i_ht_free_lzc (
        .in_i       (head_tail_free),
        .cnt_o      (head_tail_free_idx),
        .empty_o    ()
    );

    // Find the first free index in the linked data table.
    for (genvar i = 0; i < CAPACITY; i++) begin: gen_linked_data_free
        assign linked_data_free[i] = linked_data_q[i].free;
    end
    lzc #(
        .WIDTH  (CAPACITY),
        .MODE   (0)         // Start at index 0.
    ) i_ld_free_lzc (
        .in_i       (linked_data_free),
        .cnt_o      (linked_data_free_idx),
        .empty_o    ()
    );

    // The queue is full if and only if there are no free items in the linked data structure.
    assign full = !(|linked_data_free);

    assign inp_gnt_o = ~full;
    always_comb begin
        match_id            = 'x;
        match_id_valid      = 1'b0;
        head_tail_d         = head_tail_q;
        linked_data_d       = linked_data_q;
        oup_gnt_o           = 1'b0;
        oup_data_o          = data_t'('x);
        oup_data_valid_o    = 1'b0;
        if (inp_req_i && !full) begin
            match_id = inp_id_i;
            match_id_valid = 1'b1;
            // If the ID does not yet exist in the queue, add a new ID entry.
            if (no_id_match) begin
                head_tail_d[head_tail_free_idx] = '{
                    id: inp_id_i,
                    head: linked_data_free_idx,
                    tail: linked_data_free_idx,
                    free: 1'b0
                };
            // Otherwise append it to the existing ID subqueue.
            end else begin
                linked_data_d[head_tail_q[match_idx].tail].next = linked_data_free_idx;
                head_tail_d[match_idx].tail = linked_data_free_idx;
            end
            linked_data_d[linked_data_free_idx] = '{
                data: inp_data_i,
                next: 'x,
                free: 1'b0
            };
        end else if (oup_req_i) begin
            match_id = oup_id_i;
            match_id_valid = 1'b1;
            if (!no_id_match) begin
                oup_data_o = data_t'(linked_data_q[head_tail_q[match_idx].head].data);
                oup_data_valid_o = 1'b1;
                if (oup_pop_i) begin
                    // Set free bit of linked data entry, all other bits are don't care.
                    linked_data_d[head_tail_q[match_idx].head]      = 'x;
                    linked_data_d[head_tail_q[match_idx].head][0]   = 1'b1;
                    if (head_tail_q[match_idx].head == head_tail_q[match_idx].tail) begin
                        head_tail_d[match_idx] = '{free: 1'b1, default: 'x};
                    end else begin
                        head_tail_d[match_idx].head = linked_data_q[head_tail_q[match_idx].head].next;
                    end
                end
            end
            // Always grant the output request.  If there was no match, the default, invalid entry
            // will be returned.
            oup_gnt_o = 1'b1;
        end
    end

    // Exists Lookup
    for (genvar i = 0; i < CAPACITY; i++) begin: gen_lookup
        mask_t exists_match_bits;
        for (genvar j = 0; j < $bits(data_t); j++) begin: gen_mask
            always_comb begin
                if (linked_data_q[i].free) begin
                    exists_match_bits[j] = 1'b0;
                end else begin
                    if (!exists_mask_i[j]) begin
                        exists_match_bits[j] = 1'b1;
                    end else begin
                        exists_match_bits[j] = (linked_data_q[i].data[j] == exists_data_i[j]);
                    end
                end
            end
        end
        assign exists_match[i] = (&exists_match_bits);
    end
    always_comb begin
        exists_gnt_o = 1'b0;
        exists_o = 'x;
        if (exists_req_i) begin
            exists_gnt_o = 1'b1;
            exists_o = (|exists_match);
        end
    end

    // Registers
    for (genvar i = 0; i < HT_CAPACITY; i++) begin: gen_ht_ffs
        always_ff @(posedge clk_i, negedge rst_ni) begin
            if (!rst_ni) begin
                head_tail_q[i] <= '{free: 1'b1, default: 'x};
            end else begin
                head_tail_q[i] <= head_tail_d[i];
            end
        end
    end
    for (genvar i = 0; i < CAPACITY; i++) begin: gen_data_ffs
        always_ff @(posedge clk_i, negedge rst_ni) begin
            if (!rst_ni) begin
                // Set free bit of linked data entries, all other bits are don't care.
                linked_data_q[i]    <= 'x;
                linked_data_q[i][0] <= 1'b1;
            end else begin
                linked_data_q[i]    <= linked_data_d[i];
            end
        end
    end

    // Validate parameters.
// pragma translate_off
`ifndef VERILATOR
    initial begin: validate_params
        assert (ID_WIDTH >= 1)
            else $fatal("The ID must at least be one bit wide!");
        assert (CAPACITY >= 1)
            else $fatal("The queue must have capacity of at least one entry!");
    end
`endif
// pragma translate_on

endmodule

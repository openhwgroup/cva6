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
// Author: David Schaffenrath, TU Graz
// Author: Florian Zaruba, ETH Zurich
//
// Description: Pseudo Least Recently Used Tree (PLRU)
// See: https://en.wikipedia.org/wiki/Pseudo-LRU

module plru_tree #(
  parameter int unsigned ENTRIES = 16
) (
  input  logic               clk_i,
  input  logic               rst_ni,
  input  logic [ENTRIES-1:0] used_i, // element i was used (one hot)
  output logic [ENTRIES-1:0] plru_o  // element i is the least recently used (one hot)
);

    localparam LOG_ENTRIES = $clog2(ENTRIES);

    logic [2*(ENTRIES-1)-1:0] plru_tree_q, plru_tree_d;

    always_comb begin : plru_replacement
        plru_tree_d = plru_tree_q;
        // The PLRU-tree indexing:
        // lvl0        0
        //            / \
        //           /   \
        // lvl1     1     2
        //         / \   / \
        // lvl2   3   4 5   6
        //       / \ /\/\  /\
        //      ... ... ... ...
        // Just predefine which nodes will be set/cleared
        // E.g. for a TLB with 8 entries, the for-loop is semantically
        // equivalent to the following pseudo-code:
        // unique case (1'b1)
        // used_i[7]: plru_tree_d[0, 2, 6] = {1, 1, 1};
        // used_i[6]: plru_tree_d[0, 2, 6] = {1, 1, 0};
        // used_i[5]: plru_tree_d[0, 2, 5] = {1, 0, 1};
        // used_i[4]: plru_tree_d[0, 2, 5] = {1, 0, 0};
        // used_i[3]: plru_tree_d[0, 1, 4] = {0, 1, 1};
        // used_i[2]: plru_tree_d[0, 1, 4] = {0, 1, 0};
        // used_i[1]: plru_tree_d[0, 1, 3] = {0, 0, 1};
        // used_i[0]: plru_tree_d[0, 1, 3] = {0, 0, 0};
        // default: begin /* No hit */ end
        // endcase
        for (int unsigned i = 0; i < ENTRIES; i++) begin
            automatic int unsigned idx_base, shift, new_index;
            // we got a hit so update the pointer as it was least recently used
            if (used_i[i]) begin
                // Set the nodes to the values we would expect
                for (int unsigned lvl = 0; lvl < LOG_ENTRIES; lvl++) begin
                  idx_base = $unsigned((2**lvl)-1);
                  // lvl0 <=> MSB, lvl1 <=> MSB-1, ...
                  shift = LOG_ENTRIES - lvl;
                  // to circumvent the 32 bit integer arithmetic assignment
                  new_index =  ~((i >> (shift-1)) & 32'b1);
                  plru_tree_d[idx_base + (i >> shift)] = new_index[0];
                end
            end
        end
        // Decode tree to write enable signals
        // Next for-loop basically creates the following logic for e.g. an 8 entry
        // TLB (note: pseudo-code obviously):
        // plru_o[7] = &plru_tree_q[ 6, 2, 0]; //plru_tree_q[0,2,6]=={1,1,1}
        // plru_o[6] = &plru_tree_q[~6, 2, 0]; //plru_tree_q[0,2,6]=={1,1,0}
        // plru_o[5] = &plru_tree_q[ 5,~2, 0]; //plru_tree_q[0,2,5]=={1,0,1}
        // plru_o[4] = &plru_tree_q[~5,~2, 0]; //plru_tree_q[0,2,5]=={1,0,0}
        // plru_o[3] = &plru_tree_q[ 4, 1,~0]; //plru_tree_q[0,1,4]=={0,1,1}
        // plru_o[2] = &plru_tree_q[~4, 1,~0]; //plru_tree_q[0,1,4]=={0,1,0}
        // plru_o[1] = &plru_tree_q[ 3,~1,~0]; //plru_tree_q[0,1,3]=={0,0,1}
        // plru_o[0] = &plru_tree_q[~3,~1,~0]; //plru_tree_q[0,1,3]=={0,0,0}
        // For each entry traverse the tree. If every tree-node matches,
        // the corresponding bit of the entry's index, this is
        // the next entry to replace.
        for (int unsigned i = 0; i < ENTRIES; i += 1) begin
            automatic logic en;
            automatic int unsigned idx_base, shift, new_index;
            en = 1'b1;
            for (int unsigned lvl = 0; lvl < LOG_ENTRIES; lvl++) begin
                idx_base = $unsigned((2**lvl)-1);
                // lvl0 <=> MSB, lvl1 <=> MSB-1, ...
                shift = LOG_ENTRIES - lvl;
                // en &= plru_tree_q[idx_base + (i>>shift)] == ((i >> (shift-1)) & 1'b1);
                new_index =  (i >> (shift-1)) & 32'b1;
                if (new_index[0]) begin
                  en &= plru_tree_q[idx_base + (i>>shift)];
                end else begin
                  en &= ~plru_tree_q[idx_base + (i>>shift)];
                end
            end
            plru_o[i] = en;
        end
    end

    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
            plru_tree_q <= '0;
        end else begin
            plru_tree_q <= plru_tree_d;
        end
    end

// pragma translate_off
`ifndef VERILATOR
    initial begin
        assert (ENTRIES == 2**LOG_ENTRIES) else $error("Entries must be a power of two");
    end
`endif
// pragma translate_on

endmodule

// Copyright 2019 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// Author: Moritz Schneider, ETH Zurich
// Date: 2.10.2019
// Description: NAPOT extract

module napot_extract #(
    parameter int unsigned PMP_LEN = 54
) (
    input logic [PMP_LEN-1:0] conf_addr_i,
    output int unsigned size_o
);
    always_comb begin
        int unsigned i;
        for (i = 0; i < PMP_LEN; i++) begin
            if (conf_addr_i[i] != 1'b1) begin
                break;
            end
        end
        size_o = i+3;

        `ifdef FORMAL
        assert(size_o > 2);
        if (size_o < PMP_LEN) begin
            assert(conf_addr_i[size_o - 3] == 0);  // check 0 bit that seperates the ones in the end
        end
        
        for (i = 0; i < PMP_LEN; i++) begin
            if (size_o > 3 && i <= size_o - 4) begin
                assert(conf_addr_i[i] == 1); // check that all the rest are ones
            end
        end
        `endif
    end
endmodule
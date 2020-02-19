//Copyright (C) 2018 to present,
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

// return address stack
module ras #(
    parameter int unsigned DEPTH = 2
)(
    input  logic             clk_i,
    input  logic             rst_ni,
    input  logic             flush_i,
    input  logic             push_i,
    input  logic             pop_i,
    input  logic [riscv::VLEN-1:0]      data_i,
    output ariane_pkg::ras_t data_o
);

    ariane_pkg::ras_t [DEPTH-1:0] stack_d, stack_q;

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
        // leave everything untouched and just push the latest value to the
        // top of the stack
        if (pop_i && push_i) begin
           stack_d = stack_q;
           stack_d[0].ra = data_i;
           stack_d[0].valid = 1'b1;
        end

        if (flush_i) begin
          stack_d = '0;
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

// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Author: Igor Loi - University of Bologna
// Author: Florian Zaruba, ETH Zurich
// Date: 12.11.2017
// Description: 8-bit LFSR

// --------------
// 8-bit LFSR
// --------------
//
// Description: Shift register
//
module lfsr_8bit #(
    parameter logic [7:0]  SEED  = 8'b0,
    parameter int unsigned WIDTH = 8
)(
    input  logic                      clk_i,
    input  logic                      rst_ni,
    input  logic                      en_i,
    output logic [WIDTH-1:0]          refill_way_oh,
    output logic [$clog2(WIDTH)-1:0]  refill_way_bin
);

    localparam int unsigned LOG_WIDTH = $clog2(WIDTH);

    logic [7:0] shift_d, shift_q;


    always_comb begin

        automatic logic shift_in;
        shift_in = !(shift_q[7] ^ shift_q[3] ^ shift_q[2] ^ shift_q[1]);

        shift_d = shift_q;

        if (en_i)
            shift_d = {shift_q[6:0], shift_in};

        // output assignment
        refill_way_oh = 'b0;
        refill_way_oh[shift_q[LOG_WIDTH-1:0]] = 1'b1;
        refill_way_bin = shift_q;
    end

    always_ff @(posedge clk_i or negedge rst_ni) begin : proc_
        if(~rst_ni) begin
            shift_q <= SEED;
        end else begin
            shift_q <= shift_d;
        end
    end

    //pragma translate_off
    initial begin
        assert (WIDTH <= 8) else $fatal(1, "WIDTH needs to be less than 8 because of the 8-bit LFSR");
    end
    //pragma translate_on

endmodule

// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Author: Florian Zaruba, zarubaf@iis.ee.ethz.ch
// Description: Delay (or randomize) AXI-like handshaking

module stream_delay #(
    parameter bit   StallRandom = 0,
    parameter int   FixedDelay  = 1,
    parameter type  payload_t  = logic
)(
    input  logic     clk_i,
    input  logic     rst_ni,

    input  payload_t payload_i,
    output logic     ready_o,
    input  logic     valid_i,

    output payload_t payload_o,
    input  logic     ready_i,
    output logic     valid_o
);

    if (FixedDelay == 0 && !StallRandom) begin : pass_through
        assign ready_o = ready_i;
        assign valid_o = valid_i;
        assign payload_o = payload_i;
    end else begin

        localparam COUNTER_BITS = 4;

        typedef enum logic [1:0] {
            Idle, Valid, Ready
        } state_e;

        state_e state_d, state_q;

        logic       load;
        logic [3:0] count_out;
        logic       en;

        logic [COUNTER_BITS-1:0] counter_load;

        assign payload_o = payload_i;

        always_comb begin
            state_d = state_q;
            valid_o = 1'b0;
            ready_o = 1'b0;
            load    = 1'b0;
            en      = 1'b0;

            unique case (state_q)
                Idle: begin
                    if (valid_i) begin
                        load = 1'b1;
                        state_d = Valid;
                        // Just one cycle delay
                        if (FixedDelay == 1 || (StallRandom && counter_load == 1)) begin
                            state_d = Ready;
                        end

                        if (StallRandom && counter_load == 0) begin
                            valid_o = 1'b1;
                            ready_o = ready_i;
                            if (ready_i) state_d = Idle;
                            else state_d = Ready;
                        end
                    end
                end
                Valid: begin
                    en = 1'b1;
                    if (count_out == 0) begin
                        state_d = Ready;
                    end
                end

                Ready: begin
                    valid_o = 1'b1;
                    ready_o = ready_i;
                    if (ready_i) state_d = Idle;
                end
                default : /* default */;
            endcase

        end

        if (StallRandom) begin : random_stall
            lfsr_16bit #(
              .WIDTH ( 16 )
            ) i_lfsr_16bit (
                .clk_i          ( clk_i        ),
                .rst_ni         ( rst_ni       ),
                .en_i           ( load         ),
                .refill_way_oh  (              ),
                .refill_way_bin ( counter_load )
            );
        end else begin
            assign counter_load = FixedDelay;
        end

        counter #(
            .WIDTH      ( COUNTER_BITS )
        ) i_counter (
            .clk_i      ( clk_i        ),
            .rst_ni     ( rst_ni       ),
            .clear_i    ( 1'b0         ),
            .en_i       ( en           ),
            .load_i     ( load         ),
            .down_i     ( 1'b1         ),
            .d_i        ( counter_load ),
            .q_o        ( count_out    ),
            .overflow_o (              )
        );

        always_ff @(posedge clk_i or negedge rst_ni) begin
            if (~rst_ni) begin
                state_q <= Idle;
            end else begin
                state_q <= state_d;
            end
        end
    end

endmodule

// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Testbench for generic FIFO
module fifo_inst_tb #(
    // FIFO parameters
    parameter bit           FALL_THROUGH,
    parameter int unsigned  DEPTH,
    parameter int unsigned  DATA_WIDTH = 8,
    // TB parameters
    parameter int unsigned  N_CHECKS,
    parameter time          TA,
    parameter time          TT
) (
    input  logic    clk_i,
    input  logic    rst_ni,
    output logic    done_o
);

    timeunit 1ns;
    timeprecision 10ps;

    import rand_verif_pkg::rand_wait;

    typedef logic [DATA_WIDTH-1:0] data_t;

    logic           clk,
                    flush,
                    full,
                    empty,
                    push,
                    pop,
                    try_push,
                    try_pop;

    data_t          wdata,
                    rdata;

    int unsigned    n_checks = 0;

    assign clk = clk_i;

    fifo_v3 #(
        .FALL_THROUGH   ( FALL_THROUGH  ),
        .DATA_WIDTH     ( DATA_WIDTH    ),
        .DEPTH          ( DEPTH         )
    ) dut (
        .clk_i,
        .rst_ni,
        .flush_i        ( flush         ),
        .testmode_i     ( 1'b0          ),
        .full_o         ( full          ),
        .empty_o        ( empty         ),
        .usage_o        (               ),
        .data_i         ( wdata         ),
        .push_i         ( push          ),
        .data_o         ( rdata         ),
        .pop_i          ( pop           )
    );

    // Simulation information and stopping.
    // TODO: Better stop after certain coverage is reached.
    initial begin
        done_o = 1'b0;
        $display("%m: Running test with FALL_THROUGH=%0d, DEPTH=%0d", FALL_THROUGH, DEPTH);
        wait (n_checks >= N_CHECKS);
        done_o = 1'b1;
        $display("%m: Checked %0d stimuli", n_checks);
    end

    class random_action_t;
        rand logic [1:0] action;
        constraint random_action {
            action dist {
                0 := 40,
                1 := 40,
                3 := 2,
                0 := 0
            };
        }
    endclass

    // Input driver: push, wdata, and flush
    assign push = try_push & ~full;
    initial begin
        automatic random_action_t rand_act = new();
        flush       <= 1'b0;
        wdata       <= 'x;
        try_push    <= 1'b0;
        wait (rst_ni);
        forever begin
            static logic rand_success;
            rand_wait(1, 8, clk);
            rand_success = rand_act.randomize(); assert(rand_success);
            case (rand_act.action)
                0: begin // new random data and try to push
                    wdata       <= #TA $random();
                    try_push    <= #TA 1'b1;
                end
                1: begin // new random data but do not try to push
                    wdata       <= #TA $random();
                    try_push    <= #TA 1'b0;
                end
                2: begin // flush
                    flush       <= #TA 1'b1;
                    rand_wait(1, 8, clk);
                    flush       <= #TA 1'b0;
                end
            endcase
        end
    end

    // Output driver: pop
    assign pop = try_pop & ~empty;
    initial begin
        try_pop <= 1'b0;
        wait (rst_ni);
        forever begin
            rand_wait(1, 8, clk);
            try_pop <= #TA $random();
        end
    end

    // Monitor & checker: model expected response and check against actual response
    initial begin
        data_t queue[$];
        wait (rst_ni);
        forever begin
            @(posedge clk_i);
            #(TT);
            if (flush) begin
                queue = {};
            end else begin
                if (push && !full) begin
                    queue.push_back(wdata);
                end
                if (pop && !empty) begin
                    automatic data_t data = queue.pop_front();
                    assert (rdata == data) else $error("Queue output %0x != %0x", rdata, data);
                    n_checks++;
                end
            end
        end
    end

    if (FALL_THROUGH) begin
        // In fall through mode, assert that the output data is equal to the input data when pushing
        // to an empty FIFO.
        assert property (@(posedge clk_i) ((empty & ~push) ##1 push) |-> rdata == wdata)
            else $error("Input did not fall through");
    end

endmodule

// Testbench for different FIFO configurations
module fifo_tb #(
    // TB parameters
    parameter int unsigned  N_CHECKS        = 100000,
    parameter time          TCLK            = 10ns,
    parameter time          TA              = TCLK * 1/4,
    parameter time          TT              = TCLK * 3/4
);

    timeunit 1ns;
    timeprecision 10ps;

    logic       clk,
                rst_n;

    logic [3:0] done;

    clk_rst_gen #(.CLK_PERIOD(TCLK), .RST_CLK_CYCLES(10)) i_clk_rst_gen (
        .clk_o    (clk),
        .rst_no   (rst_n)
    );

    fifo_inst_tb #(
        .FALL_THROUGH   (1'b0),
        .DEPTH          (8),
        .N_CHECKS       (N_CHECKS),
        .TA             (TA),
        .TT             (TT)
    ) i_tb_8 (
        .clk_i  (clk),
        .rst_ni (rst_n),
        .done_o (done[0])
    );

    fifo_inst_tb #(
        .FALL_THROUGH   (1'b1),
        .DEPTH          (8),
        .N_CHECKS       (N_CHECKS),
        .TA             (TA),
        .TT             (TT)
    ) i_tb_ft_8 (
        .clk_i  (clk),
        .rst_ni (rst_n),
        .done_o (done[1])
    );

    fifo_inst_tb #(
        .FALL_THROUGH   (1'b0),
        .DEPTH          (1),
        .N_CHECKS       (N_CHECKS),
        .TA             (TA),
        .TT             (TT)
    ) i_tb_1 (
        .clk_i  (clk),
        .rst_ni (rst_n),
        .done_o (done[2])
    );

    fifo_inst_tb #(
        .FALL_THROUGH   (1'b1),
        .DEPTH          (1),
        .N_CHECKS       (N_CHECKS),
        .TA             (TA),
        .TT             (TT)
    ) i_tb_ft_1 (
        .clk_i  (clk),
        .rst_ni (rst_n),
        .done_o (done[3])
    );

    initial begin
        wait ((&done));
        $finish();
    end

endmodule

// Author: Florian Zaruba, ETH Zurich
// Date: 24.4.2017
// Description: FIFO testbench
//
//
// Copyright (C) 2017 ETH Zurich, University of Bologna
// All rights reserved.
//
// This code is under development and not yet released to the public.
// Until it is released, the code is under the copyright of ETH Zurich and
// the University of Bologna, and may contain confidential and/or unpublished
// work. Any reuse/redistribution is strictly forbidden without written
// permission from ETH Zurich.
//
// Bug fixes and contributions will eventually be released under the
// SolderPad open hardware license in the context of the PULP platform
// (http://www.pulp-platform.org), under the copyright of ETH Zurich and the
// University of Bologna.
//

module fifo_tb;
    logic rst_ni, clk;

    fifo_if #(.dtype ( logic[7:0] )) fifo_if (clk);

    logic push, pop;

    assign fifo_if.push = ~fifo_if.full & push;
    assign fifo_if.pop = ~fifo_if.empty & pop;

    fifo
        #(.dtype ( logic[7:0] ))
    dut
     (
        .clk_i   ( clk               ),
        .rst_ni  ( rst_ni            ),
        .full_o  ( fifo_if.full      ),
        .empty_o ( fifo_if.empty     ),
        .data_i  ( fifo_if.wdata     ),
        .push_i  ( fifo_if.push      ),
        .data_o  ( fifo_if.rdata     ),
        .pop_i   ( fifo_if.pop       )
    );

    initial begin
        clk = 1'b0;
        rst_ni = 1'b0;
        repeat(8)
            #10ns clk = ~clk;

        rst_ni = 1'b1;
        forever
            #10ns clk = ~clk;
    end

    // simulator stopper, this is suboptimal better go for coverage
    initial begin
        #10000000ns
        $finish;
    end

    program testbench (fifo_if fifo_if, output logic push, output logic pop);
        logic[7:0] queue [$];

        // ----------
        // Driver
        // ----------
        initial begin
            fifo_if.mck.wdata <= $urandom_range(0,256);
            push  <= 1'b0;
            // wait for reset to be high
            wait(rst_ni == 1'b1);
            // push
            forever begin
                repeat($urandom_range(0, 8)) @(fifo_if.mck)
                    // if there is space lets push some random data
                    if (~fifo_if.mck.full) begin
                        fifo_if.mck.wdata <= $urandom_range(0,256);

                        push  <= 1'b1;
                    end else begin
                        fifo_if.mck.wdata <= $urandom_range(0,256);
                        push  <= 1'b0;
                    end
            end
        end

        initial begin
            // wait for reset to be high
            wait(rst_ni == 1'b1);
            // pop from queue
            forever begin
                @(fifo_if.mck)
                pop <= 1'b1;
                repeat($urandom_range(0, 8)) @(fifo_if.mck)
                pop <= 1'b0;
            end
        end

        // -------------------
        // Monitor && Checker
        // -------------------
        initial begin

            automatic logic [7:0] data;
            forever begin
                @(fifo_if.pck)

                if (fifo_if.pck.push) begin
                    queue.push_back(fifo_if.pck.wdata);
                end

                if (fifo_if.pck.pop) begin
                    data = queue.pop_front();
                    // $display("Time: %t, Expected: %0h Got %0h", $time, data, fifo_if.pck.rdata);
                    assert(data == fifo_if.mck.rdata) else $error("Mismatch, Expected: %0h Got %0h", data, fifo_if.pck.rdata);
                end

            end
        end

    endprogram

    testbench tb(fifo_if, push, pop);
endmodule
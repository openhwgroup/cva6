// Author: Florian Zaruba, ETH Zurich
// Date: 14.5.2017
// Description: Fetch FIFO testbench
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

import ariane_pkg::*;
import fetch_fifo_pkg::*;

module fetch_fifo_tb;

    logic rst_ni, clk_i;
    fetch_fifo_if fetch_fifo_if (clk_i);

    fetch_fifo
    dut (
        .clk_i            ( clk_i                            ),
        .rst_ni           ( rst_ni                           ),
        .flush_i          ( fetch_fifo_if.flush              ),
        .branch_predict_i ( fetch_fifo_if.in_branch_predict  ),
        .in_addr_i        ( fetch_fifo_if.in_addr            ),
        .in_rdata_i       ( fetch_fifo_if.in_rdata           ),
        .in_valid_i       ( fetch_fifo_if.in_valid           ),
        .in_ready_o       ( fetch_fifo_if.in_ready           ),
        .branch_predict_o ( fetch_fifo_if.out_branch_predict ),
        .out_addr_o       ( fetch_fifo_if.out_addr           ),
        .out_rdata_o      ( fetch_fifo_if.out_rdata          ),
        .out_valid_o      ( fetch_fifo_if.out_valid          ),
        .out_ready_i      ( fetch_fifo_if.out_ready          )
    );

    initial begin
        clk_i = 1'b0;
        rst_ni = 1'b0;
        repeat(8)
            #10ns clk_i = ~clk_i;

        rst_ni = 1'b1;
        forever
            #10ns clk_i = ~clk_i;
    end

    // simulator stopper, this is suboptimal better go for coverage
    initial begin
        #10000000ns
        $finish;
    end

    program testbench (fetch_fifo_if fetch_fifo_if);

        instruction_stream is    = new;
        fetch_fifo_model   model = new;
        instruction_queue_entry_t iqe;

        initial begin

            fetch_fifo_if.mck.flush              <= 1'b0;
            fetch_fifo_if.mck.in_branch_predict  <= 'b0;
            fetch_fifo_if.mck.in_addr            <= 'b0;
            fetch_fifo_if.mck.in_rdata           <= 'b0;
            fetch_fifo_if.mck.in_valid           <= 'b0;
            fetch_fifo_if.mck.out_ready          <= 'b0;
            wait(rst_ni == 1'b1);

            // Driver
            forever begin
                @(fetch_fifo_if.mck iff fetch_fifo_if.in_ready);

                do begin
                    iqe = is.get_instruction();
                    fetch_fifo_if.mck.in_addr           <= iqe.address;
                    fetch_fifo_if.mck.in_rdata          <= iqe.instr;
                    fetch_fifo_if.mck.in_branch_predict <= iqe.bp;
                    fetch_fifo_if.mck.in_valid          <= 1'b1;
                    @(fetch_fifo_if.mck);
                end while (fetch_fifo_if.mck.in_ready);
                fetch_fifo_if.mck.in_valid <= 1'b0;
            end
        end

    endprogram

    testbench tb(fetch_fifo_if);
endmodule
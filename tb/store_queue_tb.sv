// Author: Florian Zaruba, ETH Zurich
// Date: 28.4.2017
// Description: Store Queue Testbench
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

module store_queue_tb;
    logic rst_ni, clk;
    logic store_valid;
    logic slave_data_gnt;

    mem_if slave(clk);

    store_queue_if store_queue(clk);

    store_queue dut (
        .clk_i         ( clk                          ),
        .rst_ni        ( rst_ni                       ),
        .flush_i       ( store_queue.flush            ),
        .paddr_o       ( store_queue.check_paddr      ),
        .data_o        ( store_queue.check_data       ),
        .valid_o       ( store_queue.valid            ),
        .be_o          ( store_queue.check_be         ),
        .commit_i      ( store_queue.commit           ),
        .ready_o       ( store_queue.ready            ),
        .valid_i       ( store_queue.store_valid      ),
        .paddr_i       ( store_queue.store_paddr      ),
        .data_i        ( store_queue.store_data       ),
        .be_i          ( store_queue.store_be         ),

        .address_o     ( slave.address                 ),
        .data_wdata_o  ( slave.data_wdata              ),
        .data_req_o    ( slave.data_req                ),
        .data_we_o     ( slave.data_we                 ),
        .data_be_o     ( slave.data_be                 ),
        .data_gnt_i    ( slave.data_gnt                ),
        .data_rvalid_i ( slave.data_rvalid             )
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

    // combinatorial signals
    assign store_queue.flush = 1'b0;
    assign store_queue.store_valid = store_valid & store_queue.ready;
    assign slave.data_gnt = slave_data_gnt;

    // simulator stopper, this is suboptimal better go for coverage
    initial begin
        #10000000ns
        $stop;
    end

    program testbench (mem_if slave, store_queue_if store_queue);
        // data to store
        class store_data;
            rand logic [63:0] data;
            rand logic [7:0]  be;
        endclass : store_data

        store_data data = new();
        semaphore sem = new(1);
        // ----------
        // Driver
        // ----------

        // make a new store if it is possible
        initial begin
            // reset assignment
            store_valid                 <= 'b0;
            store_queue.mck.store_paddr <= 'b0;
            store_queue.mck.store_data  <= 'b0;
            store_queue.mck.store_be    <= 'b0;
            store_queue.mck.commit      <= 1'b0;
            wait(rst_ni);

            forever begin
                @(store_queue.mck);
                store_queue.mck.commit <= 1'b0;
                if (store_queue.mck.ready) begin
                    store_queue.mck.store_paddr <= 64'h1;
                    store_valid <= 1'b1;
                    // get some randomized data
                    void'(data.randomize());
                    store_queue.mck.store_data <= data.data;
                    store_queue.mck.store_be   <= data.be;

                    // commit a couple of cycles later
                    fork
                        commit_block: begin
                            sem.get(1);
                            @(store_queue.mck);
                            @(store_queue.mck);
                            store_queue.mck.commit <= 1'b1;
                            sem.put(1);
                        end
                    join_none

                end else begin
                    store_valid <= 1'b0;
                end
            end

        end
        // commit part
        initial begin

        end

        // grant process
        initial begin
            forever begin
                slave_data_gnt = 1'b0;
                wait (slave.data_req);
                // randomize grant delay
                // repeat ($urandom_range(0,4)) @(slave.mck);
                slave_data_gnt = 1'b1;
                wait (~slave.data_req);
            end
        end

        // write memory interface
        initial begin
            forever begin
                @(slave.mck);
                if (slave.mck.data_req)
                    slave.mck.data_rvalid <= 1'b1;
                else
                    slave.mck.data_rvalid <= 1'b0;
            end
        end


        // -------------------
        // Monitor && Checker
        // -------------------

        initial begin

        end

    endprogram

    testbench tb(slave, store_queue);
endmodule
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
    assign store_queue.store_valid = store_valid & store_queue.ready;
    assign slave.data_gnt = slave_data_gnt;

    // simulator stopper, this is suboptimal better go for coverage
    initial begin
        #1000000ns
        $stop;
    end

    program testbench (mem_if slave, store_queue_if store_queue);
        // data to store
        class store_data;
            rand logic [63:0] address;
            rand logic [63:0] data;
            rand logic [7:0]  be;

            function new (logic [63:0] address, logic [63:0] data, logic [7:0] be);
                this.address = address;
                this.data    = data;
                this.be      = be;
            endfunction : new

            function string convert2string();
                string s;
                $sformat(s, "Address: %0h, Data: %0h, BE: %0h", address, data, be);
                return s;
            endfunction : convert2string

            function bit do_compare(store_data rhs);

                if (rhs.address == address && rhs.data == data && rhs.be == be)
                    return 1;
                else return 0;

            endfunction : do_compare

        endclass : store_data

        store_data data = new(64'b0, 64'b0, 8'b0);
        semaphore sem = new(1);
        logic flush;
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
                if (store_queue.mck.ready) begin
                    // get some randomized data
                    void'(data.randomize());
                    store_queue.mck.store_paddr <= data.address;
                    store_queue.mck.store_data  <= data.data;
                    store_queue.mck.store_be    <= data.be;
                    store_valid <= 1'b1;

                    // commit a couple of cycles later
                    fork
                        commit_block: begin
                            sem.get(1);
                            @(store_queue.mck)
                            wait(~flush);
                            store_queue.mck.commit <= 1'b1;
                            @(store_queue.mck)
                            store_queue.mck.commit <= 1'b0;
                            sem.put(1);
                        end
                    join_none

                end else begin
                    store_valid <= 1'b0;
                end
            end

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

        // random flush signal
        initial begin
            flush = 1'b0;
            store_queue.mck.flush <= 0;
            forever begin
                repeat (20) @(store_queue.mck);
                // TODO: Implement Flush test, needs some more test logic
                store_queue.mck.flush <= 0;
                flush = 1'b1;
                repeat (4) @(store_queue.mck);
                store_queue.mck.flush <= 0;
                flush = 1'b0;

            end
        end

        // -------------------
        // Monitor && Checker
        // -------------------
        store_data request_data_queue [$];
        store_data tmp;
        store_data result;
        // check that all requested stores got through
        // therefore put them in a queue when requested from the LSU and check them on the
        // memory interface output
        initial begin
            forever begin
                @(store_queue.pck iff store_queue.pck.store_valid)
                tmp = new(store_queue.pck.store_paddr, store_queue.pck.store_data, store_queue.pck.store_be);
                request_data_queue.push_back(tmp);
                // $display("[LSU] Got: %s", tmp.convert2string());
            end
        end
        // check here what we actually got on the memory interface
        initial begin
            automatic store_data queue_data;

            forever begin
                @(slave.pck iff slave.pck.data_req & slave.pck.data_gnt)
                result = new(slave.pck.address, slave.pck.data_wdata, slave.pck.data_be);
                // $display("[MEM] Got: %s", result.convert2string());
                // pop from queue and check if this was indeed requested
                queue_data = request_data_queue.pop_front();
                assert(queue_data.do_compare(result)) else $error("Mismatch: Expected %s, Got: %s", queue_data.convert2string() , result.convert2string());
            end
        end

    endprogram

    testbench tb(slave, store_queue);
endmodule
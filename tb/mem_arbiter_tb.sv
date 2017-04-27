// Author: Florian Zaruba, ETH Zurich
// Date: 24.4.2017
// Description: Memory Arbiter Testbench
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

module mem_arbiter_tb;
    logic rst_ni, clk;
    logic end_test;

    logic flush_ready_o;
    logic slave_data_gnt, slave_data_req;

    mem_if master[3](clk);
    mem_if slave(clk);

    mem_arbiter dut (
        .clk_i          ( clk               ),
        .rst_ni         ( rst_ni            ),
        .flush_ready_o  ( flush_ready_o     ),

        .address_o      ( slave.address     ),
        .data_wdata_o   ( slave.data_wdata  ),
        .data_req_o     ( slave.data_req    ),
        .data_we_o      ( slave.data_we     ),
        .data_be_o      ( slave.data_be     ),
        .data_gnt_i     ( slave.data_gnt    ),
        .data_rvalid_i  ( slave.data_rvalid ),
        .data_rdata_i   ( slave.data_rdata  ),

        .address_i      ( {master[2].address,     master[1].address,     master[0].address}      ),
        .data_wdata_i   ( {master[2].data_wdata,  master[1].data_wdata,  master[0].data_wdata}   ),
        .data_req_i     ( {master[2].data_req,    master[1].data_req,    master[0].data_req}     ),
        .data_we_i      ( {master[2].data_we,     master[1].data_we,     master[0].data_we}      ),
        .data_be_i      ( {master[2].data_be,     master[1].data_be,     master[0].data_be}      ),
        .data_gnt_o     ( {master[2].data_gnt,    master[1].data_gnt,    master[0].data_gnt}     ),
        .data_rvalid_o  ( {master[2].data_rvalid, master[1].data_rvalid, master[0].data_rvalid}  ),
        .data_rdata_o   ( {master[2].data_rdata,  master[1].data_rdata,  master[0].data_rdata}   )
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

    initial begin
        end_test = 1'b0;

        #1000000ns;

        end_test = 1'b1;

    end


    assign slave.data_gnt = slave_data_gnt;

    program testbench (mem_if master[3], mem_if slave, input flush_ready);
        // --------------
        // Slave Port
        // --------------
        logic [7:0]  imem [400];
        logic [63:0] address [$];
        logic [63:0] addr;
        // grant process
        initial begin

            forever begin
                slave_data_gnt = 1'b0;
                wait (slave.data_req);
                // randomize grant delay
                repeat ($urandom_range(0,4)) @(slave.mck);
                slave_data_gnt = 1'b1;
                wait (~slave.data_req);
            end
        end
        // instruction memory
        initial begin
            slave.mck.data_rdata  <= 32'b0;
            // apply stimuli for instruction interface
            forever begin
                @(slave.mck)
                slave.mck.data_rvalid <= 1'b0;
                    fork
                        imem_read: begin
                            @(slave.mck);
                            if (slave_data_gnt) begin
                            // $display("Time: %t, Pushing", $time);
                            address.push_back(slave.mck.address);
                            if (address.size() != 0) begin
                                // we an wait a couple of cycles here
                                repeat (3) @(slave.mck);
                                slave.mck.data_rvalid <= 1'b1;
                                addr = address.pop_front();
                                slave.mck.data_rdata  <= addr;
                            end else
                                slave.mck.data_rvalid <= 1'b0;
                            end
                        end
                        imem_write: begin

                        end
                    join_none
            end
        end

        // --------------
        // Master Ports
        // --------------
        // request a read
        initial begin
            // initial statements, sane resets
            master[0].sck.data_req    <= 1'b0;
            master[0].sck.address     <= 64'b0;
            master[0].sck.data_be     <= 7'b0;
            master[0].sck.data_we     <= 1'b0;
            master[0].sck.data_wdata  <= 64'b0;

            master[1].sck.data_req    <= 1'b0;
            master[1].sck.address     <= 64'b0;
            master[1].sck.data_be     <= 7'b0;
            master[1].sck.data_we     <= 1'b0;
            master[1].sck.data_wdata  <= 64'b0;

            master[2].sck.data_req    <= 1'b0;
            master[2].sck.address     <= 64'b0;
            master[2].sck.data_be     <= 7'b0;
            master[2].sck.data_we     <= 1'b0;
            master[2].sck.data_wdata  <= 64'b0;

            wait (rst_ni);

            forever begin
                if (end_test)
                    break;
                fork
                    master0: begin
                        // read request master 0
                        do begin
                            master[0].sck.data_req    <= 1'b1;
                            master[0].sck.address     <= 64'b1;
                            master[0].sck.data_be     <= 7'b1011;
                            master[0].sck.data_we     <= 1'b0;
                            master[0].sck.data_wdata  <= 64'b0;

                            @(master[0].sck);
                        end while (~master[0].data_gnt);
                        master[0].sck.data_req    <= 1'b0;
                        // randomize response
                        repeat ($urandom_range(0,10)) @(master[0].sck);
                    end
                    master1: begin
                        // read request master 1
                        do begin
                            master[1].sck.data_req    <= 1'b1;
                            master[1].sck.address     <= 64'h8;
                            master[1].sck.data_be     <= 7'b1011;
                            master[1].sck.data_we     <= 1'b0;
                            master[1].sck.data_wdata  <= 64'b0;

                            @(master[1].sck);
                        end while (~master[1].data_gnt);
                        master[1].sck.data_req    <= 1'b0;
                        // randomize response
                        repeat ($urandom_range(0,10)) @(master[1].sck);
                    end
                    master2: begin
                        // read request master 2
                        do begin
                            master[2].sck.data_req    <= 1'b1;
                            master[2].sck.address     <= 64'hF;
                            master[2].sck.data_be     <= 7'b1011;
                            master[2].sck.data_we     <= 1'b0;
                            master[2].sck.data_wdata  <= 64'b0;

                            @(master[2].sck);
                        end while (~master[2].data_gnt);
                        master[2].sck.data_req    <= 1'b0;
                        // randomize response
                        repeat ($urandom_range(0,10)) @(master[2].sck);
                    end
                join_any
            end
        end

        // ----------------------
        // Monitor & Scoreboard
        // ----------------------

        initial begin

            automatic int slave_count = 0;
            automatic int master_count [3] = {0, 0, 0};

            fork
                slave_scoreboard: begin
                    forever begin
                        @(slave.pck iff slave.pck.data_rvalid);
                        slave_count++;
                    end
                end

                master0_scoreboard: begin
                    forever begin
                        @(master[0].pck iff master[0].pck.data_rvalid);
                        master_count[0]++;
                        assert (master[0].pck.data_rdata == 64'h1) else $error("Mismatch @%t, expected: %0h got: %0h", $time, 64'h1, master[0].pck.data_rdata);
                    end
                end

                master1_scoreboard: begin
                    forever begin
                        @(master[1].pck iff master[1].pck.data_rvalid);
                        master_count[1]++;
                        assert (master[1].pck.data_rdata == 64'h8) else $error("Mismatch @%t, expected: %0h got: %0h", $time, 64'h8, master[1].pck.data_rdata);
                    end
                end

                master2_scoreboard: begin
                    forever begin
                        @(master[2].pck iff master[2].pck.data_rvalid);
                        master_count[2]++;
                        assert (master[2].pck.data_rdata == 64'hF) else $error("Mismatch @%t, expected: %0h got: %0h", $time, 64'hF, master[2].pck.data_rdata);
                    end
                end

                control_block: begin
                    // Wait here for the end of test signal
                    wait(end_test);
                    // wait an additional time to be sure that all results got propagated
                    wait(flush_ready);
                    // check the result count
                    assert(slave_count === master_count[0] + master_count[1] + master_count[2]) else $error("Mismatch in expected result count!");
                    $stop;
                end
            join
        end
    endprogram

    testbench tb (master, slave, flush_ready_o);
endmodule
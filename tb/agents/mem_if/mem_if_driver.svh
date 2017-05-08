// Author: Florian Zaruba, ETH Zurich
// Date: 30.04.2017
// Description: Driver for interface mem_if
// Copyright (C) 2017 ETH Zurich, University of Bologna
// All rights reserved.
// This code is under development and not yet released to the public.
// Until it is released, the code is under the copyright of ETH Zurich and
// the University of Bologna, and may contain confidential and/or unpublished
// work. Any reuse/redistribution is strictly forbidden without written
// permission from ETH Zurich.
// Bug fixes and contributions will eventually be released under the
// SolderPad open hardware license in the context of the PULP platform
// (http://www.pulp-platform.org), under the copyright of ETH Zurich and the
// University of Bologna.

class mem_if_driver extends uvm_driver #(mem_if_seq_item);

    // UVM Factory Registration Macro
    `uvm_component_utils(mem_if_driver)

    // Virtual Interface
    virtual mem_if fu;
    // create a 4 kB memory
    logic [7:0]  rmem [4096];
    //---------------------
    // Data Members
    //---------------------
    mem_if_agent_config m_cfg;

    // Standard UVM Methods:
    function new(string name = "mem_if_driver", uvm_component parent = null);
      super.new(name, parent);
    endfunction

    task read_mem(logic [64:0] address, string path);
        $readmemh(path, rmem, address);
        $display("Read instruction memory file @%0h from %s", address, path);
    endtask : read_mem

    task run_phase(uvm_phase phase);
        mem_if_seq_item cmd;

        // --------------
        // Slave Port
        // --------------
        // this driver is configured as a SLAVE
        if (m_cfg.mem_if_config inside {SLAVE, SLAVE_REPLAY, SLAVE_NO_RANDOM}) begin

            logic [63:0] address [$];
            logic [63:0] addr;
            logic slave_data_gnt;
            semaphore lock = new(1);
            slave_data_gnt = 1'b1;

            // we serve all requests from the memory file we store in our configuration object
            // read memory file
            // TODO: get the filename and address from plusarg
            if (m_cfg.mem_if_config inside {SLAVE, SLAVE_NO_RANDOM}) begin
                read_mem(64'b0, "test/add_test.v");
            end

            // grant process is combinatorial
            fork
                slave_gnt: begin
                    fu.mck.data_gnt <= 1'b1;
                    // we don't to give random grants
                    // instead we always grant immediately
                    if (m_cfg.mem_if_config != SLAVE_NO_RANDOM) begin
                        forever begin
                            // randomize grant delay - the grant may come in the same clock cycle
                            repeat ($urandom_range(0,3)) @(fu.mck);
                            fu.mck.data_gnt <= 1'b1;
                            repeat ($urandom_range(0,3)) @(fu.mck);
                            fu.mck.data_gnt <= 1'b0;
                        end
                    end
                end
                slave_serve: begin
                    fu.mck.data_rdata  <= 32'b0;
                    // apply stimuli for instruction interface
                    forever begin
                        @(fu.mck)
                        fu.mck.data_rvalid <= 1'b0;
                        fork
                            // replay interface
                            imem_read: begin
                                if (fu.pck.data_gnt & fu.mck.data_req) begin
                                    // $display("Time: %t, Pushing", $time);
                                    address.push_back(fu.mck.address);
                                    if (address.size() != 0) begin
                                        // we an wait a couple of cycles here
                                        // but at least one
                                        lock.get(1);
                                        // we give the rvalid in the next cycle if didn't request randomization
                                        if (m_cfg.mem_if_config != SLAVE_NO_RANDOM)
                                            repeat ($urandom_range(1,3)) @(fu.mck);

                                        fu.mck.data_rvalid <= 1'b1;
                                        addr = address.pop_front();
                                        // simply replay the address on the data port
                                        if (m_cfg.mem_if_config == SLAVE_REPLAY)
                                            fu.mck.data_rdata  <= addr;
                                        else begin
                                            // read from memory
                                            fu.mck.data_rdata  <= {
                                                rmem[$unsigned(addr + 3)],
                                                rmem[$unsigned(addr + 2)],
                                                rmem[$unsigned(addr + 1)],
                                                rmem[$unsigned(addr + 0)]
                                                };
                                        end
                                        lock.put(1);
                                    end else
                                        fu.mck.data_rvalid <= 1'b0;
                                    end
                            end
                            imem_write: begin

                            end
                        join_none
                    end
                end
            join_none

        // although no other option exist lets be specific about its purpose
        // -> this is a master interface
        // --------------
        // Master Port
        // --------------
        end else if (m_cfg.mem_if_config == MASTER) begin
            // request a read
            // initial statements, sane resets
            fu.sck.data_req        <= 1'b0;
            fu.sck.address         <= 64'b0;
            fu.sck.data_be         <= 7'b0;
            fu.sck.data_we         <= 1'b0;
            fu.sck.data_wdata      <= 64'b0;
            // request read or write
            // we don't care about results at this point
            forever begin
                seq_item_port.get_next_item(cmd);
                    // do begin
                fu.sck.data_req         <= 1'b1;
                fu.sck.address          <= cmd.address;
                fu.sck.data_be          <= cmd.be;
                fu.sck.data_we          <= (cmd.mode == READ) ? 1'b0 : 1'b1;
                fu.sck.data_wdata       <= cmd.data;

                @(fu.sck iff fu.sck.data_gnt);
                fu.sck.data_req         <= 1'b0;

                // delay the next request
                repeat(cmd.requestDelay) @(fu.sck);
                seq_item_port.item_done();
            end
        end
    endtask : run_phase

    function void build_phase(uvm_phase phase);
      if (!uvm_config_db #(mem_if_agent_config)::get(this, "", "mem_if_agent_config", m_cfg) )
         `uvm_fatal("CONFIG_LOAD", "Cannot get() configuration mem_if_agent_config from uvm_config_db. Have you set() it?")

      fu = m_cfg.fu;
    endfunction: build_phase
endclass : mem_if_driver

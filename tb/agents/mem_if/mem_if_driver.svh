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

    //---------------------
    // Data Members
    //---------------------
    mem_if_agent_config m_cfg;

    // Standard UVM Methods:
    function new(string name = "mem_if_driver", uvm_component parent = null);
      super.new(name, parent);
    endfunction

    task run_phase(uvm_phase phase);
        mem_if_seq_item cmd;

        // this driver is configured as a SLAVE
        if (m_cfg.mem_if_config == SLAVE) begin
            // we serve all requests from the memory file we store in our configuration object
            // --------------
            // Slave Port
            // --------------
            logic [7:0]  imem [400];
            logic [63:0] address [$];
            logic [63:0] addr;
            logic slave_data_gnt;
            // grant process is combinatorial
            fork
                slave_gnt: begin
                    forever begin
                        slave_data_gnt = 1'b0;
                        fu.data_gnt = slave_data_gnt;
                        wait (fu.data_req);
                        // randomize grant delay
                        repeat ($urandom_range(0,4)) @(fu.mck);
                        slave_data_gnt = 1'b1;
                        fu.data_gnt = slave_data_gnt;
                        wait (~fu.data_req);
                    end
                end
                slave_serve: begin
                    fu.mck.data_rdata  <= 32'b0;
                    // apply stimuli for instruction interface
                    forever begin
                        @(fu.mck)
                        fu.mck.data_rvalid <= 1'b0;
                        fork
                            imem_read: begin
                                @(fu.mck);
                                if (slave_data_gnt) begin
                                // $display("Time: %t, Pushing", $time);
                                address.push_back(fu.mck.address);
                                if (address.size() != 0) begin
                                    // we an wait a couple of cycles here
                                    repeat (3) @(fu.mck);
                                    fu.mck.data_rvalid <= 1'b1;
                                    addr = address.pop_front();
                                    fu.mck.data_rdata  <= addr;
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
        // this is a master interface
        end else if (m_cfg.mem_if_config == MASTER) begin
            // --------------
            // Master Port
            // --------------
            // request a read
            // initial statements, sane resets
            fu.sck.data_req    <= 1'b0;
            fu.sck.address     <= 64'b0;
            fu.sck.data_be     <= 7'b0;
            fu.sck.data_we     <= 1'b0;
            fu.sck.data_wdata  <= 64'b0;
            // request read or write
            // we don't care about results at this point
            forever begin
                seq_item_port.get_next_item(cmd);
                   do begin
                        fu.sck.data_req    <= 1'b1;
                        fu.sck.address     <= cmd.address;
                        fu.sck.data_be     <= cmd.be;
                        fu.sck.data_we     <= (cmd.mode == READ) ? 1'b0 : 1'b1;
                        fu.sck.data_wdata  <= cmd.data;
                        @(fu.sck);
                    end while (~fu.data_gnt);
                end
                fu.sck.data_req <= 1'b0;
                seq_item_port.item_done();
        end
    endtask : run_phase

    function void build_phase(uvm_phase phase);
      if (!uvm_config_db #(mem_if_agent_config)::get(this, "", "mem_if_agent_config", m_cfg) )
         `uvm_fatal("CONFIG_LOAD", "Cannot get() configuration mem_if_agent_config from uvm_config_db. Have you set() it?")

      fu = m_cfg.fu;
    endfunction: build_phase
endclass : mem_if_driver

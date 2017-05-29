// Author: Florian Zaruba, ETH Zurich
// Date: 29.05.2017
// Description: Driver for interface dcache_if
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

class dcache_if_driver extends uvm_driver #(dcache_if_seq_item);

    // UVM Factory Registration Macro
    `uvm_component_utils(dcache_if_driver)

    // Virtual Interface
    virtual dcache_if m_vif;

    //---------------------
    // Data Members
    //---------------------
    dcache_if_agent_config m_cfg;

    // Standard UVM Methods:
    function new(string name = "dcache_if_driver", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    task run_phase(uvm_phase phase);
        dcache_if_seq_item cmd;
        logic [11:0] address_index [$];
        logic [43:0] address_tag   [$];
        logic [55:0] address_out;

        semaphore lock = new(1);

        // --------------
        // Slave Port
        // --------------
        // this driver is configured as a SLAVE
        if (m_cfg.dcache_if_config inside {SLAVE, SLAVE_REPLAY, SLAVE_NO_RANDOM}) begin
            // grant process is combinatorial
            fork
                slave_gnt: begin
                    m_vif.mck.data_gnt <= 1'b1;
                    // we don't to give random grants
                    // instead we always grant immediately
                    if (m_cfg.dcache_if_config != SLAVE_NO_RANDOM) begin
                        forever begin
                            // randomize grant delay - the grant may come in the same clock cycle
                            repeat ($urandom_range(0,3)) @(m_vif.mck);
                            m_vif.mck.data_gnt <= 1'b1;
                            repeat ($urandom_range(0,3)) @(m_vif.mck);
                            m_vif.mck.data_gnt <= 1'b0;
                        end
                    end
                end
                slave_serve: begin
                    m_vif.mck.data_rdata  <= 32'b0;
                    // apply stimuli for instruction interface
                    forever begin
                        @(m_vif.mck)
                        m_vif.mck.data_rvalid <= 1'b0;
                        fork
                            // replay interface
                            mem_read: begin
                                // we've got a new request
                                if (m_vif.pck.data_gnt && m_vif.mck.data_req) begin
                                    // push the low portion of the address a.k.a. the index
                                    address_index.push_back(m_vif.mck.address_index);
                                    // wait a couple of cycles, but at least one
                                    @(m_vif.mck);
                                    // in this cycle the tag is ready
                                    address_tag.push_back(m_vif.mck.address_tag);
                                    lock.get(1);
                                    // randomize rvalid here
                                    repeat ($urandom_range(1,2)) @(m_vif.mck);
                                    m_vif.mck.data_rvalid <= 1'b1;
                                    // compose the address
                                    address_out = {address_tag.pop_front(), address_index.pop_front()};
                                    m_vif.mck.data_rdata <= address_out;
                                    // put back the lock
                                    lock.put(1);
                                end else
                                    m_vif.mck.data_rvalid <= 1'b0;
                            end
                            mem_write: begin

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
        end else if (m_cfg.dcache_if_config == MASTER) begin
            // request a read
            // initial statements, sane resets
            m_vif.sck.data_req        <= 1'b0;
            m_vif.sck.address_index   <= 12'b0;
            m_vif.sck.address_tag     <= 44'b0;
            m_vif.sck.data_be         <= 7'b0;
            m_vif.sck.data_we         <= 1'b0;
            m_vif.sck.tag_valid       <= 1'b0;
            m_vif.sck.kill_req        <= 1'b0;
            m_vif.sck.data_wdata      <= 64'b0;
            // request read or write
            // we don't care about results at this point
            fork
                forever begin
                    seq_item_port.get_next_item(cmd);
                        // do begin
                    m_vif.sck.data_req      <= 1'b1;
                    m_vif.sck.address_index <= cmd.address[11:0];
                    m_vif.sck.data_be       <= cmd.be;
                    m_vif.sck.data_we       <= (cmd.mode == READ) ? 1'b0 : 1'b1;
                    m_vif.sck.data_wdata    <= cmd.data;

                    @(m_vif.sck iff m_vif.sck.data_gnt);
                    m_vif.sck.address_tag   <= cmd.address[43:12];
                    m_vif.sck.data_req      <= 1'b0;
                    // delay the next request
                    repeat (cmd.requestDelay) @(m_vif.sck);

                    seq_item_port.item_done();
                end

                forever begin
                    @(m_vif.sck);
                    m_vif.sck.tag_valid <= m_vif.sck.data_gnt;
                end
            join_none
        end

        seq_item_port.get_next_item(cmd);

        seq_item_port.item_done();
    endtask : run_phase

    function void build_phase(uvm_phase phase);
        if (!uvm_config_db #(dcache_if_agent_config)::get(this, "", "dcache_if_agent_config", m_cfg) )
           `uvm_fatal("CONFIG_LOAD", "Cannot get() configuration dcache_if_agent_config from uvm_config_db. Have you set() it?")

        m_vif = m_cfg.m_vif;
    endfunction: build_phase
endclass : dcache_if_driver

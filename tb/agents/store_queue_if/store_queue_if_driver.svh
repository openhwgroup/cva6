// Author: Florian Zaruba, ETH Zurich
// Date: 29.05.2017
// Description: Driver for interface store_queue_if
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

class store_queue_if_driver extends uvm_driver #(store_queue_if_seq_item);

    // UVM Factory Registration Macro
    `uvm_component_utils(store_queue_if_driver)

    // Virtual Interface
    virtual store_queue_if m_vif;

    //---------------------
    // Data Members
    //---------------------
    store_queue_if_agent_config m_cfg;

    // Standard UVM Methods:
    function new(string name = "store_queue_if_driver", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    task run_phase(uvm_phase phase);
        semaphore sem = new(1);
        store_queue_if_seq_item cmd;
        // reset assignment
        m_vif.mck.store_paddr <= 'b0;
        m_vif.mck.store_data  <= 'b0;
        m_vif.mck.store_be    <= 'b0;
        m_vif.mck.commit      <= 1'b0;
        m_vif.mck.store_valid <= 1'b0;
        m_vif.mck.flush       <= 1'b0;
        fork
            put_data: begin
                forever begin

                    @(m_vif.mck);
                    // make a new store request
                    if (m_vif.mck.ready) begin
                        seq_item_port.get_next_item(cmd);

                        m_vif.mck.store_paddr <= cmd.address;
                        m_vif.mck.store_data  <= cmd.data;
                        m_vif.mck.store_be    <= cmd.be;
                        m_vif.mck.store_valid <= 1'b1;

                        seq_item_port.item_done();
                        // fork off a commit task
                        // commit a couple of cycles later
                        @(m_vif.mck iff m_vif.pck.valid)
                        fork
                            commit_block: begin
                                sem.get(1);
                                m_vif.mck.commit <= 1'b1;
                                @(m_vif.mck)
                                m_vif.mck.commit <= 1'b0;
                                sem.put(1);
                            end
                        join_none
                    end else begin
                        m_vif.mck.store_valid <= 1'b0;
                    end
                end
            end
        join_none

    endtask : run_phase

    function void build_phase(uvm_phase phase);
        if (!uvm_config_db #(store_queue_if_agent_config)::get(this, "", "store_queue_if_agent_config", m_cfg) )
           `uvm_fatal("CONFIG_LOAD", "Cannot get() configuration store_queue_if_agent_config from uvm_config_db. Have you set() it?")

        m_vif = m_cfg.m_vif;
    endfunction: build_phase
endclass : store_queue_if_driver

// Author: Florian Zaruba, ETH Zurich
// Date: 29.05.2017
// Description: dcache_if Monitor, monitors the DUT's pins and writes out
//              appropriate sequence items as defined for this particular dut
//
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

class dcache_if_monitor extends uvm_component;

    // UVM Factory Registration Macro
    `uvm_component_utils(dcache_if_monitor)

    // analysis port
    uvm_analysis_port #(dcache_if_seq_item) m_ap;

    // Virtual Interface
    virtual dcache_if m_vif;

    mailbox address_mbx;
    mailbox data_mbx;

    //---------------------
    // Data Members
    //---------------------
    dcache_if_agent_config m_cfg;

    // Standard UVM Methods:
    function new(string name = "dcache_if_driver", uvm_component parent = null);
      super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
      if (!uvm_config_db #(dcache_if_agent_config)::get(this, "", "dcache_if_agent_config", m_cfg) )
        `uvm_fatal("CONFIG_LOAD", "Cannot get() configuration dcache_if_agent_config from uvm_config_db. Have you set() it?")

        m_ap = new("m_ap", this);
        address_mbx  = new();
        data_mbx  = new();

    endfunction: build_phase

    function void connect_phase(uvm_phase phase);
        // connect virtual interface
        m_vif = m_cfg.m_vif;
    endfunction

    task run_phase(uvm_phase phase);

        string if_type = this.get_full_name();//(m_cfg.dcache_if_config inside {SLAVE, SLAVE_REPLAY, SLAVE_NO_RANDOM}) ? "[SLAVE]" : "[MASTER]";
        logic [11:0] address_index [$];
        logic [7:0]  be [$];
        logic [63:0] wdata [$];

        dcache_if_seq_item cmd =  dcache_if_seq_item::type_id::create("cmd");
        // Monitor process
        fork
            // 1. Thread
            // detect a request
            req: begin
                forever begin
                    @(m_vif.pck iff (m_vif.pck.data_gnt && m_vif.pck.data_req));
                    // save tag and byte enable
                    // $display("%s: %t, Putting index: %0h", if_type, $time(), m_vif.pck.address_index);
                    address_index.push_back(m_vif.pck.address_index);
                    be.push_back(m_vif.pck.data_be);
                    wdata.push_back(m_vif.pck.data_wdata);
                end
            end

            // 2. Thread
            // detect a valid tag and save it
            tag_valid: begin
                forever begin
                    @(m_vif.pck iff m_vif.pck.tag_valid);
                    // save tag for later use
                    address_mbx.put({m_vif.pck.address_tag, address_index.pop_front()});

                    // $display("%s: %t, Putting Tag %0h, Queue Size: %d", if_type, $time(), m_vif.pck.address_tag, address_mbx.num());
                end
            end

            // 3. thread wait for valid data
            read_valid: begin
                forever begin
                    @(m_vif.pck iff m_vif.pck.data_rvalid);
                    data_mbx.put(m_vif.pck.data_rdata);
                end
            end

            respsonese_gen: begin
                forever begin
                    dcache_if_seq_item cloned_item;

                    // blocking get, wait for both to be ready
                    data_mbx.get(cmd.data);
                    address_mbx.get(cmd.address);
                    cmd.be    = be.pop_front();
                    cmd.wdata = wdata.pop_front();
                    // $display("%s: %t, Popping %0h from MBX", if_type, $time(), cmd.address);
                    // was this from a master or slave agent monitor?
                    cmd.isSlaveAnswer = (m_cfg.dcache_if_config inside {SLAVE, SLAVE_REPLAY, SLAVE_NO_RANDOM}) ? 1'b1 : 1'b0;
                    $cast(cloned_item, cmd.clone());
                    m_ap.write(cloned_item);
                end
            end
        join_any


    endtask : run_phase
endclass : dcache_if_monitor

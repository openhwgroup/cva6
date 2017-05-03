// Author: Florian Zaruba, ETH Zurich
// Date: 02.05.2017
// Description: Driver for interface lsu_if
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

class lsu_if_driver extends uvm_driver #(lsu_if_seq_item);

    // UVM Factory Registration Macro
    `uvm_component_utils(lsu_if_driver)

    // Virtual Interface
    virtual lsu_if m_vif;

    //---------------------
    // Data Members
    //---------------------
    lsu_if_agent_config m_cfg;

    // Standard UVM Methods:
    function new(string name = "lsu_if_driver", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    task run_phase(uvm_phase phase);
        semaphore lock = new(1);

        lsu_if_seq_item cmd;
        // reset values
        m_vif.mck.lsu_trans_id_id <= 'b0;
        m_vif.mck.source_valid    <= 1'b0;
        m_vif.mck.imm             <= 'b0;
        m_vif.mck.operator        <=  ADD;
        m_vif.mck.operand_a       <= 'b0;
        m_vif.mck.operand_b       <= 'b0;
        m_vif.mck.commit          <= 1'b0;
        forever begin
            // if the LSU is ready apply a new stimuli
            @(m_vif.mck);
            if (m_vif.mck.ready) begin
                seq_item_port.get_next_item(cmd);
                // we potentially want to wait a couple of cycles before applying
                // a new request
                repeat(cmd.requestDelay) @(m_vif.mck);
                // the data we apply is valid
                m_vif.mck.lsu_trans_id_id <= cmd.trans_id;
                m_vif.mck.source_valid    <= 1'b1;
                m_vif.mck.imm             <= cmd.imm;
                m_vif.mck.operator        <= cmd.operator;
                m_vif.mck.operand_a       <= cmd.operandA;
                m_vif.mck.operand_b       <= cmd.operandB;
                @(m_vif.mck);
                // spawn a commit thread that will eventually commit this instruction
                case (cmd.operator)
                    SD, SW, SH, SB, SBU:
                        fork
                            commit_thread: begin
                                lock.get(1);
                                    @(m_vif.mck);
                                    m_vif.mck.commit <= 1'b1;
                                    @(m_vif.mck);
                                    m_vif.mck.commit <= 1'b0;
                                lock.put(1);
                            end
                        join_none
                endcase
                m_vif.mck.source_valid    <= 1'b0;
                seq_item_port.item_done();
            end else
                m_vif.mck.source_valid <= 1'b0;

        end
    endtask : run_phase

    function void build_phase(uvm_phase phase);
        if (!uvm_config_db #(lsu_if_agent_config)::get(this, "", "lsu_if_agent_config", m_cfg) )
           `uvm_fatal("CONFIG_LOAD", "Cannot get() configuration lsu_if_agent_config from uvm_config_db. Have you set() it?")

        m_vif = m_cfg.m_vif;
    endfunction: build_phase
endclass : lsu_if_driver

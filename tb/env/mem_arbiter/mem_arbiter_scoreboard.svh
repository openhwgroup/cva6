// Author: Florian Zaruba, ETH Zurich
// Date: 01.05.2017
// Description: Memory Arbiter scoreboard
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
class mem_arbiter_scoreboard extends uvm_scoreboard;

    `uvm_component_utils(mem_arbiter_scoreboard);
    int slave_answer_cnt, master_answer_cnt;

    uvm_analysis_imp #(dcache_if_seq_item, mem_arbiter_scoreboard) item_export;

    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction : new

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        item_export  = new("item_slave_export", this);
        slave_answer_cnt = 0;
        master_answer_cnt = 0;
    endfunction : build_phase

    virtual function void write (dcache_if_seq_item seq_item);
        // $display("%s", seq_item.convert2string());
        // the answer is from a master
        // the address and data should be the same when we use the replay system
        if (~seq_item.isSlaveAnswer) begin
            if (seq_item.address !== seq_item.data) begin
                `uvm_error( "DCache Arbiter Scoreboard",  $sformatf("Got: %0h Expected: %0h", seq_item.address, seq_item.data) )
            end else begin
                // `uvm_info( "DCache Arbiter Scoreboard",  $sformatf("Got: %0h Expected: %0h", seq_item.address, seq_item.data), UVM_LOW)
            end
            master_answer_cnt++;
        end else begin
            slave_answer_cnt++;
        end

    endfunction

    // check here for the total amount of transactions
    virtual function void extract_phase( uvm_phase phase );
        super.extract_phase(phase);
        if (master_answer_cnt !== slave_answer_cnt) begin
            `uvm_error("DCache Arbiter Scoreboard", $sformatf("Mismatch in overall result count. Expected: %d Got: %d", slave_answer_cnt, master_answer_cnt))
        end else
            `uvm_info("DCache Arbiter Scoreboard", $sformatf("Overall result count: Expected: %d Got: %d", slave_answer_cnt, master_answer_cnt), UVM_LOW)
    endfunction : extract_phase

endclass : mem_arbiter_scoreboard

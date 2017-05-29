// Author: Florian Zaruba, ETH Zurich
// Date: 29.05.2017
// Description: Store Queue scoreboard
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
class store_queue_scoreboard extends uvm_scoreboard;

    `uvm_component_utils(store_queue_scoreboard);

    uvm_analysis_imp #(store_queue_if_seq_item, store_queue_scoreboard) store_queue_item_export;
    uvm_analysis_imp #(dcache_if_seq_item, store_queue_scoreboard) dcache_item_export;

    store_queue_if_seq_item store_queue_items [$];

    function new(string name, uvm_component parent);
        super.new(name, parent);
        store_queue_item_export = new("store_queue_item_export", this);
        dcache_item_export      = new("dcache_item_export", this);
    endfunction : new

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
    endfunction : build_phase

    virtual function void write (uvm_sequence_item seq_item);
        // variables to hold the casts
        store_queue_if_seq_item casted_store_queue = new;
        dcache_if_seq_item casted_dcache = new;


        // got a store queue item
        if (seq_item.get_type_name() == "store_queue_if_seq_item") begin
            // $display("%s", seq_item.convert2string());
            $cast(casted_store_queue, seq_item.clone());
            // this is the first item which is coming, so put it in a queue
            store_queue_items.push_back(casted_store_queue);
        end

        // got an dcache item
        if (seq_item.get_type_name() == "dcache_if_seq_item") begin
            // cast dcache variable
            $cast(casted_dcache, seq_item.clone());

            $display("%s", store_queue_items.pop_front().convert2string());
            $display("%s", casted_dcache.convert2string());

        end
    endfunction


endclass : store_queue_scoreboard
// Author: Florian Zaruba, ETH Zurich
// Date: 29.05.2017
// Description: dcache_if Sequence item
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

class dcache_if_seq_item extends uvm_sequence_item;

    // UVM Factory Registration Macro
    `uvm_object_utils(dcache_if_seq_item)

    //------------------------------------------
    // Data Members (Outputs rand, inputs non-rand)
    //------------------------------------------
    rand logic [63:0] address;
    rand logic [63:0] data;
    rand logic [7:0]  be;
    rand int requestDelay;
    mode_t mode;
    logic isSlaveAnswer;

    constraint delay_bounds {
        requestDelay inside {[0:10]};
    }
    //------------------------------------------
    // Methods
    //------------------------------------------

    // Standard UVM Methods:
    function new(string name = "dcache_if_seq_item");
        super.new(name);
    endfunction

    function void do_copy(uvm_object rhs);
        dcache_if_seq_item rhs_;

        if(!$cast(rhs_, rhs)) begin
          `uvm_fatal("do_copy", "cast of rhs object failed")
        end
        super.do_copy(rhs);
        // Copy over data members:
        // e.g.:
        address = rhs_.address;
        data = rhs_.data;
        be = rhs_.be;
        mode = rhs_.mode;
        isSlaveAnswer = rhs_.isSlaveAnswer;
    endfunction : do_copy

    function bit do_compare(uvm_object rhs, uvm_comparer comparer);
        dcache_if_seq_item rhs_;

        if(!$cast(rhs_, rhs)) begin
          `uvm_error("do_copy", "cast of rhs object failed")
          return 0;
        end

        return super.do_compare(rhs, comparer)
        && address == rhs_.address
        && data == rhs_.data
        && be == rhs_.be
        && mode == rhs_.mode;
    endfunction : do_compare

    function string convert2string();
        string s;

        $sformat(s, "%s\n", super.convert2string());
        $sformat(s, "%s\nMode: %s\nAddress: %0h\nData: %0h\nBE: %0h \nisSlaveAnswer: %h", s, mode.name, address, data, be, isSlaveAnswer);
        return s;

    endfunction:convert2string

    function void do_print(uvm_printer printer);
        if(printer.knobs.sprint == 0) begin
          $display(convert2string());
        end
        else begin
          printer.m_string = convert2string();
        end
    endfunction : do_print

    function void do_record(uvm_recorder recorder);
        super.do_record(recorder);

        // Use the record macros to record the item fields:
        `uvm_record_field("Mode", mode)
        `uvm_record_field("Address", address)
        `uvm_record_field("Data", data)
        `uvm_record_field("BE", be)
    endfunction:do_record

endclass : dcache_if_seq_item

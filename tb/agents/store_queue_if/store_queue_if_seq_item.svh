// Author: Florian Zaruba, ETH Zurich
// Date: 29.05.2017
// Description: store_queue_if Sequence item
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

class store_queue_if_seq_item extends uvm_sequence_item;

    // UVM Factory Registration Macro
    `uvm_object_utils(store_queue_if_seq_item)

    //------------------------------------------
    // Data Members (Outputs rand, inputs non-rand)
    //------------------------------------------
    // TODO: set data members

    //------------------------------------------
    // Methods
    //------------------------------------------

    // Standard UVM Methods:
    function new(string name = "store_queue_if_seq_item");
        super.new(name);
    endfunction

    function void do_copy(uvm_object rhs);
        store_queue_if_seq_item rhs_;

        if(!$cast(rhs_, rhs)) begin
          `uvm_fatal("do_copy", "cast of rhs object failed")
        end
        super.do_copy(rhs);
        // Copy over data members:
        // e.g.:
        // operator = rhs_.operator;

    endfunction:do_copy

    function bit do_compare(uvm_object rhs, uvm_comparer comparer);
        store_queue_if_seq_item rhs_;

        if(!$cast(rhs_, rhs)) begin
          `uvm_error("do_copy", "cast of rhs object failed")
          return 0;
        end
        // TODO
        return super.do_compare(rhs, comparer); // && operator == rhs_.operator

    endfunction:do_compare

    function string convert2string();
        string s;

        $sformat(s, "%s\n", super.convert2string());
        // Convert to string function reusing s:
        // TODO
        // $sformat(s, "%s\n operator\n", s, operator);
        return s;

    endfunction:convert2string

    function void do_print(uvm_printer printer);
        if(printer.knobs.sprint == 0) begin
          $display(convert2string());
        end
        else begin
          printer.m_string = convert2string();
        end
    endfunction:do_print

    function void do_record(uvm_recorder recorder);
        super.do_record(recorder);

        // Use the record macros to record the item fields:
        // TODO
        // `uvm_record_field("operator", operator)
    endfunction:do_record

endclass : store_queue_if_seq_item

// Author: Florian Zaruba, ETH Zurich
// Date: 12/21/2016
// Description: Sequence contains the necessary fields along with randomization constraints
//              Requests can be arbitrarily delayed.
//
// Copyright (C) 2017 ETH Zurich, University of Bologna
// All rights reserved.

typedef enum {
    ISSUE, COMMIT, PUSH
} scoreboard_op;

class scoreboard_if_seq_item extends uvm_sequence_item;

    // UVM Factory Registration Macro
    `uvm_object_utils(scoreboard_if_seq_item)

    //------------------------------------------
    // Data Members (Outputs rand, inputs non-rand)
    //------------------------------------------
    rand scoreboard_op instruction_type;
    rand scoreboard_entry scoreboard_entry;
    rand int delay;

    //------------------------------------------
    // Methods
    //------------------------------------------

    // Standard UVM Methods:
    function new(string name = "scoreboard_if_seq_item");
      super.new(name);
    endfunction

    function void do_copy(uvm_object rhs);
      scoreboard_if_seq_item rhs_;

      if(!$cast(rhs_, rhs)) begin
        `uvm_fatal("do_copy", "cast of rhs object failed")
      end
      super.do_copy(rhs);
      // Copy over data members:
      instruction_type = rhs_.instruction_type;
      scoreboard_entry = rhs_.scoreboard_entry;
      delay = rhs_.delay;

    endfunction:do_copy

    function bit do_compare(uvm_object rhs, uvm_comparer comparer);
      scoreboard_if_seq_item rhs_;

      if(!$cast(rhs_, rhs)) begin
        `uvm_error("do_copy", "cast of rhs object failed")
        return 0;
      end
      return super.do_compare(rhs, comparer) &&
                instruction_type == rhs_.instruction_type     &&
                scoreboard_entry == rhs_.scoreboard_entry   &&
                delay == rhs_.delay;
    endfunction:do_compare

    function string convert2string();
      string s;

      $sformat(s, "%s\n", super.convert2string());
      // Convert to string function reusing s:
      $sformat(s, "%s Scoreboard: %0h Operation: %s", s, instruction_type.name);
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
      `uvm_record_field("instruction_type", instruction_type)
      `uvm_record_field("scoreboard_entry", scoreboard_entry)
      `uvm_record_field("delay", delay)
    endfunction:do_record

endclass : scoreboard_if_seq_item

// Author: Florian Zaruba, ETH Zurich
// Date: 12/21/2016
// Description: Sequence contains the necessary fields along with randomization constraints
//              Requests can be arbitrarily delayed.

// Copy of APB Sequence Item

class fu_if_seq_item extends uvm_sequence_item;

    // UVM Factory Registration Macro
    `uvm_object_utils(fu_if_seq_item)

    //------------------------------------------
    // Data Members (Outputs rand, inputs non-rand)
    //------------------------------------------
    logic[7:0] operator;
    rand logic[64:0] operand_a;
    rand logic[64:0] operand_b;
    rand logic[64:0] operand_c;

    logic[64:0] result;
    logic       compare_result;

    //------------------------------------------
    // Methods
    //------------------------------------------

    // Standard UVM Methods:
    extern function new(string name = "fu_if_seq_item");
    extern function void do_copy(uvm_object rhs);
    extern function bit do_compare(uvm_object rhs, uvm_comparer comparer);
    extern function string convert2string();
    extern function void do_print(uvm_printer printer);
    extern function void do_record(uvm_recorder recorder);

endclass : fu_if_seq_item


function fu_if_seq_item::new(string name = "fu_if_seq_item");
  super.new(name);
endfunction

function void fu_if_seq_item::do_copy(uvm_object rhs);
  fu_if_seq_item rhs_;

  if(!$cast(rhs_, rhs)) begin
    `uvm_fatal("do_copy", "cast of rhs object failed")
  end
  super.do_copy(rhs);
  // Copy over data members:
  operator = rhs_.operator;
  operand_a = rhs_.operand_a;
  operand_b = rhs_.operand_b;
  operand_c = rhs_.operand_c;

  result = rhs_.result;
  compare_result = rhs.compare_result;

endfunction:do_copy

function bit fu_if_seq_item::do_compare(uvm_object rhs, uvm_comparer comparer);
  fu_if_seq_item rhs_;

  if(!$cast(rhs_, rhs)) begin
    `uvm_error("do_copy", "cast of rhs object failed")
    return 0;
  end
  return super.do_compare(rhs, comparer) &&
            operator == rhs_.operator     &&
            operand_a == rhs_.operand_a   &&
            operand_b == rhs_.operand_b   &&
            operand_c == rhs_.operand_c;


endfunction:do_compare

function string fu_if_seq_item::convert2string();
  string s;

  $sformat(s, "%s\n", super.convert2string());
  // Convert to string function reusing s:
  $sformat(s, "%s\n addr\t%0h\n data\t%0h\n we\t%0b\n delay\t%0d\n", s, addr, data, we, delay);
  return s;

endfunction:convert2string

function void fu_if_seq_item::do_print(uvm_printer printer);
  if(printer.knobs.sprint == 0) begin
    $display(convert2string());
  end
  else begin
    printer.m_string = convert2string();
  end
endfunction:do_print

function void fu_if_seq_item:: do_record(uvm_recorder recorder);
  super.do_record(recorder);

  // Use the record macros to record the item fields:
  `uvm_record_field("operator", operator)
  `uvm_record_field("operand_a", operand_a)
  `uvm_record_field("operand_b", operand_b)
  `uvm_record_field("operand_c", operand_c)
endfunction:do_record
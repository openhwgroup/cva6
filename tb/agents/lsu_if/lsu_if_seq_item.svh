// Author: Florian Zaruba, ETH Zurich
// Date: 02.05.2017
// Description: lsu_if Sequence item
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

class lsu_if_seq_item extends uvm_sequence_item;

    // UVM Factory Registration Macro
    `uvm_object_utils(lsu_if_seq_item)

    //------------------------------------------
    // Data Members (Outputs rand, inputs non-rand)
    //------------------------------------------
    rand fu_op  operator;
    rand logic [63:0] operandA;
    rand logic [63:0] operandB;
    rand logic [63:0] imm;
    rand logic [TRANS_ID_BITS-1:0]  trans_id;
    rand int requestDelay;
    logic [63:0] result;

    const fu_op allowed_ops[] = {LD, SD, LW, LWU, SW, LH, LHU, SH, LB, SB, LBU, SBU};
    // constraint the delay we allow
    constraint delay_bounds {
        requestDelay inside {[0:10]};
    }
    // constraint the allowed operators
    constraint allowed_operations {
        operator inside {allowed_ops};
    }
    constraint base {
        operandA[2:0] == 3'b000;
    }
    // aligned memory constraint
    constraint aligned_address {
        // constraint to signed or unsigned immediate
        imm[62:11] == {52 {imm[63]}};
        // constraint aligness
        (operator == LD || operator == SD) -> {
            imm[3:0] == 3'b000;
        }
        (operator == LW || operator == LWU || operator == SW) -> {
            imm[3:0] == 3'b00;
        }
        (operator == LH || operator == LHU || operator == SH) -> {
            imm[3:0] == 3'b0;
        }
    }
    //------------------------------------------
    // Methods
    //------------------------------------------

    // Standard UVM Methods:
    function new(string name = "lsu_if_seq_item");
      super.new(name);
    endfunction

    function void do_copy(uvm_object rhs);
      lsu_if_seq_item rhs_;

      if(!$cast(rhs_, rhs)) begin
        `uvm_fatal("do_copy", "cast of rhs object failed")
      end
      super.do_copy(rhs);
      // Copy over data members:
      operator = rhs_.operator;
      operandA = rhs_.operandA;
      operandB = rhs_.operandA;
      imm      = rhs_.imm;
      result   = rhs_.result;

    endfunction:do_copy

    function bit do_compare(uvm_object rhs, uvm_comparer comparer);
      lsu_if_seq_item rhs_;

      if(!$cast(rhs_, rhs)) begin
        `uvm_error("do_copy", "cast of rhs object failed")
        return 0;
      end
      // TODO
      return super.do_compare(rhs, comparer)
                && operandA == rhs_.operandA
                && operandB == rhs_.operandB
                && imm == rhs_.imm
                && result == rhs_.result;

    endfunction:do_compare

    function string convert2string();
      string s;

      $sformat(s, "%s\n", super.convert2string());
      // Convert to string function reusing s:
      $sformat(s, "%s\n operandA: %0h\noperandB: %0h\imm: %0h\result: %0h\n", s, operandA, operandB, imm, result);
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
      `uvm_record_field("operandA", operandA)
      `uvm_record_field("operandB", operandB)
      `uvm_record_field("imm", imm)
      `uvm_record_field("result", result)

    endfunction:do_record

endclass : lsu_if_seq_item

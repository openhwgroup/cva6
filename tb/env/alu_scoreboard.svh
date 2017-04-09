class alu_scoreboard extends uvm_scoreboard;

    `uvm_component_utils(alu_scoreboard);

     uvm_analysis_imp#(fu_if_seq_item, alu_scoreboard) item_export;

    bit [63:0] result;
    bit [31:0] result32;

    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction : new

    function void build_phase(uvm_phase phase);
       super.build_phase(phase);
       item_export = new("item_export", this);
    endfunction : build_phase

    virtual function void write (fu_if_seq_item seq_item);
        result = 64'b0;
	      result32 = 32'b0;

      	case (alu_op'(seq_item.operator))
      	    ADD:
      		    result = seq_item.operand_a + seq_item.operand_b;
            ADDW: begin
      		    result32 = seq_item.operand_a[31:0] + seq_item.operand_b[31:0];
      		    result = {{32{result32[31]}}, result32};
      	    end
      	    SUB:
        		  result = seq_item.operand_a - seq_item.operand_b;
      	    SUBW: begin
        		  result32 = seq_item.operand_a[31:0] - seq_item.operand_b[31:0];
      		    result = {{32{result32[31]}}, result32};
      	    end
            XORL:
              result =  seq_item.operand_a ^ seq_item.operand_b;
            ORL:
              result =  seq_item.operand_a | seq_item.operand_b;
            ANDL:
              result =  seq_item.operand_a & seq_item.operand_b;
            SRA:
              result = $signed(seq_item.operand_a) >>> seq_item.operand_b[5:0];
            SRL:
              result = $unsigned(seq_item.operand_a) >>> seq_item.operand_b[5:0];
            SLL:
              result = $unsigned(seq_item.operand_a) <<< seq_item.operand_b[5:0];
            SRLW:
              result32 = $unsigned(seq_item.operand_a[31:0]) >>> seq_item.operand_b[4:0];
            SLLW:
              result32 = $unsigned(seq_item.operand_a[31:0]) <<< seq_item.operand_b[4:0];
            SRAW:
              result32 = $signed(seq_item.operand_a[31:0]) >>> seq_item.operand_b[4:0];
        endcase

        if (result != seq_item.result)
		      `uvm_error("ALU Scoreboard", $sformatf("Result: %0h, Expected %0h", seq_item.result, result))

    endfunction : write;

endclass : alu_scoreboard

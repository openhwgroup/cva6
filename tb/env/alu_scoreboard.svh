class alu_scoreboard extends uvm_scoreboard;
    
    `uvm_component_utils(alu_scoreboard);

     uvm_analysis_imp#(fu_if_seq_item, alu_scoreboard) item_export;
    
    bit [63:0] result;
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction : new

    function void build_phase(uvm_phase phase);
       super.build_phase(phase);
       item_export = new("item_export", this);
    endfunction : build_phase

    virtual function void write (fu_if_seq_item seq_item);
        seq_item.print();
        result = 64'b0;

	case (alu_op'(seq_item.operator))
	    add: 
		result = seq_item.operand_a + seq_item.operand_b;
        endcase

        if (result != seq_item.result)
		`uvm_error("ALU Scoreboard", $sformatf("Result: %0h, Expected %0h", seq_item.result, result))

    endfunction : write;

endclass : alu_scoreboard

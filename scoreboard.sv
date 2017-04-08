import ariane_pkg::*;

module scoreboard #(
    parameter int  NR_ENTRIES = 8,
    parameter type dtype      = scoreboard_entry
    )
    (
    input  logic                                   clk_i,    // Clock
    input  logic                                   rst_ni,   // Asynchronous reset active low
    output logic                                   full_o,   // We can't take anymore data

    // list of clobbered registers to issue stage
    output logic [31:0][$bits(fu_t)-1:0]           rd_clobber_o,

    // regfile like interface to operand read stage
    input  logic [4:0]                             rs1_i,
    output logic [63:0]                            rs1_o,
    output logic                                   rs1_valid_o,

    input  logic [4:0]                             rs2_i,
    output logic [63:0]                            rs2_o,
    output logic                                   rs2_valid_o,

    // advertise instruction to commit stage, if ready_i is asserted advance the commit pointer
    output dtype                                   commit_instr_o,
    input  logic                                   commit_ready_i,

    // instruction to put on top of scoreboard e.g.: top pointer
    // we can always put this instruction to the top unless we signal with asserted full_o
    input  dtype                                   decoded_instr_i,
    input  logic                                   decoded_intr_valid_i,

    // instruction to issue logic, if issue_instr_valid and issue_ready is asserted, advance the issue pointer
    output dtype                                   issue_instr_o,
    output logic                                   issue_instr_valid_o,
    input  logic                                   issue_ready_i
);

dtype            [NR_ENTRIES-1:0]         mem_n, mem_q;
logic            [$clog2(NR_ENTRIES)-1:0] issue_pointer_n, issue_pointer_q, // points to the instruction currently in issue
                                          commit_pointer_n, commit_pointer_q, // points to the instruction currently in commit
                                          top_pointer_n, top_pointer_q; // points to the top of the scoreboard

logic                                     pointer_overflow;
logic                                     empty;

// full and empty signaling: signal that we are not able to take new instructions
// track pointer overflow
assign pointer_overflow = (commit_pointer_q < top_pointer_q) ? 1'b0 : 1'b1;
assign full_o           = (pointer_overflow) ? commit_pointer_q == top_pointer_q : 1'b0;
assign empty            = (pointer_overflow) ? 1'b0 : commit_pointer_q == top_pointer_q;

// rd_clobber output: output currently clobbered destination registers
// but only between commit and issue pointer
always_comb begin : clobber_output
    rd_clobber_o = '{default: 0};
    for (logic[$clog2(NR_ENTRIES):0] i = {1'b0, commit_pointer_q}; i < commit_pointer_q + issue_pointer_q; i++) begin
        // cast to integer e.g. 32 bit
        logic[31:0] index = {{(31 - $clog2(NR_ENTRIES)){1'b0}}, i};
        // output the functional unit which is going to give the result in register
        rd_clobber_o[mem_q[index % NR_ENTRIES].rd] = mem_q[index % NR_ENTRIES].fu;
    end
end
// read operand interface: same logic as register file, including a valid file

// push new decoded instruction: if still empty space push the instruction to the scoreboard

// issue instruction: advance the issue pointer
always_comb begin : issue_instruction

    // provide a combinatorial path in case the scoreboard is empty
    if (empty) begin
        issue_instr_o       = decoded_instr_i;
        issue_instr_valid_o = decoded_intr_valid_i;
    // if not empty go to scoreboard and get the instruction at the issue pointer
    end else begin
        issue_instr_o = mem_q[$unsigned(issue_pointer_q)];
        issue_instr_valid_o = 1'b1;
    end
    // default assignment: issue didn't read
    issue_pointer_n = issue_pointer_q;
    // advance pointer if the issue logic was ready
    if (issue_ready_i) begin
        issue_pointer_n = issue_pointer_q + 1;
    end

end
// write-back instruction: update value of RD register in scoreboard

// commit instruction: remove from scoreboard

assign mem_n = mem_q;

// sequential process
always_ff @(posedge clk_i or negedge rst_ni) begin : sequential
    if(~rst_ni) begin
        mem_q            <= '{default: 0};
        issue_pointer_q  <= '{default: 0};
        commit_pointer_q <= '{default: 0};
        top_pointer_q    <= '{default: 0};
    end else begin
        mem_q            <= mem_n;
        issue_pointer_q  <= issue_pointer_n;
        commit_pointer_q <= commit_pointer_n;
        top_pointer_q    <= top_pointer_n;
    end
end

`ifndef verilator
    assert (NR_ENTRIES == 2**$clog2(NR_ENTRIES)) else $error("Scoreboard size needs to be a power of two.");
`endif
endmodule
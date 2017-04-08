import ariane_pkg::*;

module scoreboard #(
    parameter int  NR_ENTRIES = 8,
    parameter type dtype      = scoreboard_entry
    )
    (
    input  logic                                   clk_i,    // Clock
    input  logic                                   rst_ni,   // Asynchronous reset active low
    output logic                                   full_o,   // We can't take anymore data
    input  logic                                   flush_i,
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
    input  logic                                   decoded_instr_valid_i,

    // instruction to issue logic, if issue_instr_valid and issue_ready is asserted, advance the issue pointer
    output dtype                                   issue_instr_o,
    output logic                                   issue_instr_valid_o,
    input  logic                                   issue_ready_i,

    // write-back port
    input logic[63:0]                              pc_i,        // PC at which to write the result back
    input logic[63:0]                              wdata_i,     // write data in
    input logic                                    wb_valid_i   // data in is valid
);
localparam BITS_ENTRIES      = $clog2(NR_ENTRIES);

dtype [NR_ENTRIES-1:0]         mem;
logic [BITS_ENTRIES-1:0]       issue_pointer_n, issue_pointer_q, // points to the instruction currently in issue
                               commit_pointer_n, commit_pointer_q, // points to the instruction currently in commit
                               top_pointer_n, top_pointer_q; // points to the top of the scoreboard, an empty slot

logic                          pointer_overflow;
logic                          empty;

// full and empty signaling: signal that we are not able to take new instructions
// track pointer overflow
assign pointer_overflow = (commit_pointer_q <= top_pointer_q) ? 1'b0 : 1'b1;
assign full_o           = (pointer_overflow) ? (commit_pointer_q == top_pointer_q) : 1'b0;
assign empty            = (pointer_overflow) ? 1'b0 : (commit_pointer_q == top_pointer_q);

// rd_clobber output: output currently clobbered destination registers
// but only between commit and issue pointer
// normal case:                                      overflow case:
// ._________________________.                      ._________________________.
// |_________________________|                      |_________________________|
// |_________________________|<- commit pointer     |_________________________|<- issue pointer
// |_________________________|                      |_________________________|<- top pointer
// |_________________________|<- issue pointer      |_________________________|<- commit pointer
// |_________________________|<- top pointer        |_________________________|
//
always_comb begin : clobber_output
    rd_clobber_o = '{default: 0};

    // excluding issue, the issue pointer points to the instruction which is currently not issued
    // but might be issued as soon as the issue unit acknowledges
    if (commit_pointer_q < issue_pointer_q) begin
        for (int unsigned i = 0; i < NR_ENTRIES; i++) begin
            // non overflowed case, depicted on the left
            if (i[BITS_ENTRIES-1:0] >= commit_pointer_q && i[BITS_ENTRIES-1:0] < issue_pointer_q)
                rd_clobber_o[mem[$unsigned(i)].rd] = mem[$unsigned(i)].fu;
        end
    end else begin // the issue pointer has overflowed, invert logic, depicted on the right
        for (int unsigned i = 0; i < NR_ENTRIES; i++) begin
            if (i[BITS_ENTRIES-1:0] >= commit_pointer_q || i[BITS_ENTRIES-1:0] < issue_pointer_q)
                rd_clobber_o[mem[$unsigned(i)].rd] = mem[$unsigned(i)].fu;
        end
    end
end
// read operand interface: same logic as register file, including a valid file
always_comb begin : read_operands

    rs1_o       = 64'b0;
    rs2_o       = 64'b0;
    rs1_valid_o = 1'b0;
    rs2_valid_o = 1'b0;

    if (commit_pointer_q < issue_pointer_q) begin
        for (int unsigned i = 0; i < NR_ENTRIES; i++) begin
            if (i[BITS_ENTRIES-1:0] >= commit_pointer_q && i[BITS_ENTRIES-1:0] < issue_pointer_q) begin
                // look at the appropriate fields and look whether there was an
                // instruction that wrote the rd field before, first for RS1 and then for RS2
                if (mem[i[BITS_ENTRIES-1:0]].rd == rs1_i) begin
                    rs1_o = mem[i[BITS_ENTRIES-1:0]].result;
                    rs1_valid_o = mem[i[BITS_ENTRIES-1:0]].valid;
                // do the same for rs2
                end else if (mem[i[BITS_ENTRIES-1:0]].rd == rs2_i) begin
                    rs2_o = mem[i[BITS_ENTRIES-1:0]].result;
                    rs2_valid_o = mem[i[BITS_ENTRIES-1:0]].valid;
                end
            end
        end
    end else begin // the issue pointer has overflowed, invert logic
        for (int unsigned i = 0; i < NR_ENTRIES; i++) begin
            if (i[BITS_ENTRIES-1:0] >= commit_pointer_q || i[BITS_ENTRIES-1:0] < issue_pointer_q) begin
                // same as above but for the overflowed pointer case
                if (mem[i[BITS_ENTRIES-1:0]].rd == rs1_i) begin
                    rs1_o = mem[i[BITS_ENTRIES-1:0]].result;
                    rs1_valid_o = mem[i[BITS_ENTRIES-1:0]].valid;
                // do the same for rs2
                end else if (mem[i[BITS_ENTRIES-1:0]].rd == rs2_i) begin
                    rs2_o = mem[i[BITS_ENTRIES-1:0]].result;
                    rs2_valid_o = mem[i[BITS_ENTRIES-1:0]].valid;
                end
            end
        end
    end
end
// push new decoded instruction: if still empty space push the instruction to the scoreboard
// write-back instruction: update value of RD register in scoreboard
always_latch begin : push_instruction_and_wb
    // default assignment
    top_pointer_n = top_pointer_q;
    // if we are not full we can push a new instruction
    if (~full_o && decoded_instr_valid_i) begin
        mem[$unsigned(top_pointer_q)] = decoded_instr_i;
        top_pointer_n = top_pointer_q + 1;
    end

    // write back:
    // look for the intruction with the given PC and write the result data back
    // also set the valid bit
    if (wb_valid_i) begin
        for (int unsigned i = 0; i < NR_ENTRIES; i++) begin
            if (mem[i[BITS_ENTRIES-1:0]].pc == pc_i) begin
                mem[i[BITS_ENTRIES-1:0]].valid  = 1'b1;
                mem[i[BITS_ENTRIES-1:0]].result = wdata_i;
            end
        end
    end

    // flush signal
    if (flush_i)
        mem = '{default: 0};

end

// issue instruction: advance the issue pointer
always_comb begin : issue_instruction

    // provide a combinatorial path in case the scoreboard is empty
    if (empty) begin
        issue_instr_o       = decoded_instr_i;
        issue_instr_valid_o = decoded_instr_valid_i;
    // if not empty go to scoreboard and get the instruction at the issue pointer
    end else begin
        issue_instr_o = mem[$unsigned(issue_pointer_q)];
        issue_instr_valid_o = 1'b1;
    end
    // default assignment: issue didn't read
    issue_pointer_n = issue_pointer_q;
    // advance pointer if the issue logic was ready
    if (issue_ready_i) begin
        issue_pointer_n = issue_pointer_q + 1;
    end

end

// commit instruction: remove from scoreboard, advance pointer
always_comb begin: commit_instruction
    commit_pointer_n = commit_pointer_q;
    // we can always safely output the instruction at which the commit pointer points
    // since the scoreboard entry has a valid bit which the commit stage needs to check anyway
    commit_instr_o   = mem[commit_pointer_q];
    if (commit_ready_i) begin
        commit_pointer_n = commit_pointer_q + 1;
    end
end

// sequential process
always_ff @(posedge clk_i or negedge rst_ni) begin : sequential
    if(~rst_ni) begin
        issue_pointer_q  <= '{default: 0};
        commit_pointer_q <= '{default: 0};
        top_pointer_q    <= '{default: 0};
    end else begin
        issue_pointer_q  <= issue_pointer_n;
        commit_pointer_q <= commit_pointer_n;
        top_pointer_q    <= top_pointer_n;
    end
end

`ifndef SYNTHESIS
`ifndef verilator
    assert (NR_ENTRIES == 2**$clog2(NR_ENTRIES)) else $error("Scoreboard size needs to be a power of two.");
    // asserts
`endif
`endif
endmodule
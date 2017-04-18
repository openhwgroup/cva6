class Scoreboard;

    scoreboard_entry decoded_instructions[$];
    scoreboard_entry issued_instructions[$];
    static logic[4:0] i = 0;

    // utility function to get randomized input data
    static function scoreboard_entry randomize_scoreboard();
            exception exception = { 63'h0, 63'h0, 1'b0};
            scoreboard_entry entry = {
                i, ALU, ADD, 5'h5, 5'h5, 5'h5, 64'h0, 1'b0, 1'b0, exception
            };
            return entry;
    endfunction : randomize_scoreboard

    // just allow one operation
    function void submit_instruction(scoreboard_entry entry);
        entry.trans_id = i;
        i = (++i % 8);
        decoded_instructions.push_back(entry);
    endfunction : submit_instruction

    // get the current issue instruction
    function scoreboard_entry get_issue();
        scoreboard_entry issue = decoded_instructions.pop_front();
        // put in issue queue
        issued_instructions.push_back(issue);
        return issue;
    endfunction : get_issue

    // write back to scoreboard
    function void write_back(logic [4:0] trans_id, logic [63:0] value);
        for (int i = 0; i < $size(issued_instructions); i++) begin
            if (issued_instructions[i].trans_id == trans_id) begin
                issued_instructions[i].valid = 1'b1;
                issued_instructions[i].result  = value;
            end
        end
    endfunction : write_back

    // // commit the instruction, e.g.: delete it from the entries
    function scoreboard_entry commit();
        return issued_instructions.pop_front();
    endfunction : commit

    // return the clobbered registers
    function logic [31:0][$bits(fu_t)-1:0] get_clobber();
        logic [31:0][$bits(fu_t)-1:0] result;
        for (int i = 0; i < $size(issued_instructions); i++) begin
            if (issued_instructions[i].rd != 5'h0) begin
                result[issued_instructions[i].rd] = issued_instructions[i].fu;
            end
        end
        return result;
    endfunction : get_clobber


endclass : Scoreboard
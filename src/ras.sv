// return address stack
module ras #(
    parameter int unsigned DEPTH = 2
)(
    input  logic        clk_i,
    input  logic        rst_ni,
    input  logic        push_i,
    input  logic        pop_i,
    input  logic [63:0] data_i,
    output ras_t        data_o
);

    ras_t [DEPTH-1:0] stack_d, stack_q;

    assign data_o = stack_q[0];

    always_comb begin
        stack_d = stack_q;

        // push on the stack
        if (push_i) begin
            stack_d[0].ra = data_i;
            // mark the new return address as valid
            stack_d[0].valid = 1'b1;
            stack_d[DEPTH-1:1] = stack_q[DEPTH-2:0];
        end

        if (pop_i) begin
            stack_d[DEPTH-2:0] = stack_q[DEPTH-1:1];
            // we popped the value so invalidate the end of the stack
            stack_d[DEPTH-1].valid = 1'b0;
            stack_d[DEPTH-1].ra = 'b0;
        end
    end

    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (~rst_ni) begin
            stack_q <= '0;
        end else begin
            stack_q <= stack_d;
        end
    end
endmodule

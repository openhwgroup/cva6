module sim_timeout #(
  parameter longint unsigned  Cycles = 0,
  parameter bit               ResetRestartsTimeout = 1'b0
) (
  input logic clk_i,
  input logic rst_ni
);

  longint unsigned cycles = 0;
  always_ff @(posedge clk_i, negedge rst_ni) begin
    if (ResetRestartsTimeout && !rst_ni) begin
      cycles <= 0;
    end else begin
      cycles <= cycles + 1;
    end
    if (cycles > Cycles) begin
      $fatal(1, "Timeout exceeded!");
    end
  end

  `ifndef VERILATOR
    initial begin: validate_params
      assert (Cycles > 0)
        else $fatal("The number of timeout cycles must be greater than 0!");
      end
  `endif

endmodule

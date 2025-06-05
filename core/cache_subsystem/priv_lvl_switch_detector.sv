module priv_lvl_switch_detector
  import riscv::*;
(
  input  logic clk_i,
  input  logic rst_ni,
  input  priv_lvl_t priv_lvl_i,
  output logic switch_o,
  output logic [63:0] switch_count_o
);
  priv_lvl_t priv_lvl_q;
  logic [63:0] switch_counter;

  assign switch_o = (priv_lvl_q != priv_lvl_i);
  assign switch_count_o = switch_counter;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      priv_lvl_q <= PRIV_LVL_M;
      switch_counter <= '0;
    end else begin
      priv_lvl_q <= priv_lvl_i;
      if (switch_o) switch_counter <= switch_counter + 1'b1;
    end
  end
endmodule


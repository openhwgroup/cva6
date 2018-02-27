module cluster_clock_inverter
(
    input  logic clk_i,
    output logic clk_o
  );

  assign clk_o = ~clk_i;

endmodule

module cva6tb_clk_rst_gen #(
  parameter int unsigned ClkPeriodPs  = 1000,
  parameter int unsigned RstClkCycles = 0
) (
  output logic clk_o,
  output logic rst_no
);

  localparam int unsigned HighTimePs = ClkPeriodPs / 2;
  localparam int unsigned LowTimePs  = ClkPeriodPs - (ClkPeriodPs / 2);

  localparam realtime HighTime = HighTimePs * 1ps;
  localparam realtime LowTime  =  LowTimePs * 1ps;

  logic clk;

  // Clock generation
  initial begin
    clk = 0;
  end
  always begin
    clk = 1;
    #(HighTime);
    clk = 0;
    #(LowTime);
  end
  assign clk_o = clk;

  // Reset Generation
  initial begin
    static int unsigned rst_cnt = 0;
    rst_no = 1'b0;
    #(HighTime); // Start counting clock cycles on first complete cycle.
    while (rst_cnt < RstClkCycles) begin
      @(posedge clk);
      rst_cnt++;
    end
    // Release between edges: on an edge, whether flops still see reset depends
    // on the simulator's event order.
    @(negedge clk);
    rst_no = 1'b1;
  end

  // Validate parameters.
`ifndef VERILATOR
  initial begin: validate_params
    assert (ClkPeriodPs >= 2)
      else $fatal(1, "The clock period must be at least 2ps!");
      // Reason: Gets divided by two, and some simulators do not support non-integer time steps, so
      // if the time unit is 1ps, this would fail.
    assert (RstClkCycles > 0)
      else $fatal(1, "The number of clock cycles in reset must be greater than 0!");
  end
`endif

endmodule

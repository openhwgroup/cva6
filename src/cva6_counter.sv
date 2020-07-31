module cva6_counter #(
  parameter int CounterWidth = 64
) (
  input  logic        clk_i,
  input  logic        rst_ni,

  input  logic        counter_inc_i,
  input  logic        counter_we_i,
  input  logic [63:0] counter_val_i,
  output logic [63:0] counter_val_o
);

  logic [63:0]             counter;
  logic [CounterWidth-1:0] counter_upd;
  logic [63:0]             counter_load;
  logic [CounterWidth-1:0] counter_d;


  // Update
  always_comb begin
    // Increment
    counter_upd = counter[CounterWidth-1:0] + {{CounterWidth-1{1'b0}}, 1'b1};

    // Next value logic
    if (counter_we_i) begin
      counter_d = counter_val_i[CounterWidth-1:0];
    end else if (counter_inc_i) begin
      counter_d = counter_upd[CounterWidth-1:0];
    end else begin
      counter_d = counter[CounterWidth-1:0];
    end
  end

`ifdef TARGET_XILINX
  // Set DSP pragma for supported Xilinx FPGAs
  localparam int DspPragma = CounterWidth < 49  ? "yes" : "no";
  (* use_dsp = DspPragma *) logic [CounterWidth-1:0] counter_q;

  // DSP output register requires synchronous reset.
  `define COUNTER_FLOP_RST posedge clk_i
`else
  logic [CounterWidth-1:0] counter_q;

  `define COUNTER_FLOP_RST posedge clk_i or negedge rst_ni
`endif

  // Counter flop
  always_ff @(`COUNTER_FLOP_RST) begin
    if (!rst_ni) begin
      counter_q <= '0;
    end else begin
      counter_q <= counter_d;
    end
  end

  if (CounterWidth < 64) begin : g_counter_narrow
    logic [63:CounterWidth] unused_counter_load;
    assign counter[CounterWidth-1:0] = counter_q;
    assign counter[63:CounterWidth]  = '0;
    assign unused_counter_load       = counter_val_i[63:CounterWidth];
  end else begin : g_counter_full
    assign counter = counter_q;
  end

  assign counter_val_o = counter;

endmodule

// Keep helper defines file-local.
`undef COUNTER_FLOP_RST

// Vivado BD needs a .v verilog wrapper...
module bootrom_wrapper (
    input  wire        clk_i,
    input  wire        req_i,
    input  wire [63:0] addr_i,
    output wire [63:0] rdata_o
);

  bootrom_64 i_bootrom (
      .clk_i  (clk_i),
      .req_i  (req_i),
      .addr_i (addr_i),
      .rdata_o(rdata_o)
  );

endmodule

// Verilator-compatible version of tc_sram behavioral model
// This is a workaround for the BLKLOOPINIT error in Verilator

module tc_sram #(
  parameter int unsigned NumWords     = 32'd1024,
  parameter int unsigned DataWidth    = 32'd128,
  parameter int unsigned ByteWidth    = 32'd8,
  parameter int unsigned NumPorts     = 32'd2,
  parameter int unsigned Latency      = 32'd1,
  parameter              SimInit      = "none",
  parameter bit          PrintSimCfg  = 1'b0,
  parameter int unsigned AddrWidth = (NumWords > 32'd1) ? $clog2(NumWords) : 32'd1,
  parameter int unsigned BeWidth   = (DataWidth + ByteWidth - 32'd1) / ByteWidth,
  parameter type         addr_t    = logic [AddrWidth-1:0],
  parameter type         data_t    = logic [DataWidth-1:0],
  parameter type         be_t      = logic [BeWidth-1:0],
  parameter string       ImplKey   = "none"
) (
  input  logic                 clk_i,
  input  logic                 rst_ni,
  input  logic  [NumPorts-1:0] req_i,
  input  logic  [NumPorts-1:0] we_i,
  input  addr_t [NumPorts-1:0] addr_i,
  input  data_t [NumPorts-1:0] wdata_i,
  input  be_t   [NumPorts-1:0] be_i,
  output data_t [NumPorts-1:0] rdata_o
);

  // Simplified behavioral model for Verilator
  data_t sram [NumWords-1:0];
  
  // Read/write logic
  always_ff @(posedge clk_i) begin
    for (int unsigned i = 0; i < NumPorts; i++) begin
      if (req_i[i]) begin
        if (we_i[i]) begin
          // Write with byte enables
          for (int unsigned j = 0; j < BeWidth; j++) begin
            if (be_i[i][j]) begin
              sram[addr_i[i]][j*ByteWidth +: ByteWidth] <= wdata_i[i][j*ByteWidth +: ByteWidth];
            end
          end
        end
        // Read
        rdata_o[i] <= sram[addr_i[i]];
      end
    end
  end

endmodule
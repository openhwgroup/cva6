
module data_arrays_0_ext(
  input RW0_clk,
  input [8:0] RW0_addr,
  input RW0_en,
  input RW0_wmode,
  input [31:0] RW0_wmask,
  input [255:0] RW0_wdata,
  output [255:0] RW0_rdata
);

/* name=data_arrays_0_ext, width=256, depth=512, mask_gran=8, mask_seg=32, ports=['mrw'] FPGA special case */

  infer_bram  #(
    .BRAM_SIZE(9),
    .BYTE_WIDTH(32))
    my_block_ram (
  .ram_clk(RW0_clk),    // input wire clka
  .ram_en(RW0_en),      // input wire ena
  .ram_we(RW0_wmode ? {RW0_wmask} : 32'b0),   // input wire [31 : 0] wea
  .ram_addr(RW0_addr),  // input wire [8: 0] addra
  .ram_wrdata(RW0_wdata),  // input wire [255 : 0] dina
  .ram_rddata(RW0_rdata)  // output wire [255 : 0] douta
  );

endmodule

module tag_array_ext(
  input RW0_clk,
  input [5:0] RW0_addr,
  input RW0_en,
  input RW0_wmode,
  input [3:0] RW0_wmask,
  input [87:0] RW0_wdata,
  output reg [87:0] RW0_rdata
);

  reg [87:0] ram [63:0];

    integer initvar;
    initial begin
      #0.002 begin end
      for (initvar = 0; initvar < 64; initvar = initvar+1)
        ram[initvar] = 88'b0;
    end

  integer i;
  always @(posedge RW0_clk)
    if (RW0_en && !RW0_wmode) RW0_rdata <= ram[RW0_addr];
  always @(posedge RW0_clk)
    if (RW0_en && RW0_wmode) begin
      if (RW0_wmask[0]) ram[RW0_addr][21:0] <= RW0_wdata[21:0];
      if (RW0_wmask[1]) ram[RW0_addr][43:22] <= RW0_wdata[43:22];
      if (RW0_wmask[2]) ram[RW0_addr][65:44] <= RW0_wdata[65:44];
      if (RW0_wmask[3]) ram[RW0_addr][87:66] <= RW0_wdata[87:66];
    end

endmodule

module tag_array_0_ext(
  input RW0_clk,
  input [5:0] RW0_addr,
  input RW0_en,
  input RW0_wmode,
  input [3:0] RW0_wmask,
  input [83:0] RW0_wdata,
  output reg [83:0] RW0_rdata
);

  reg [83:0] ram [63:0];

    integer initvar;
    initial begin
      #0.002 begin end
      for (initvar = 0; initvar < 64; initvar = initvar+1)
        ram[initvar] = 84'b0;
    end

  integer i;
  always @(posedge RW0_clk)
    if (RW0_en && !RW0_wmode) RW0_rdata <= ram[RW0_addr];
  always @(posedge RW0_clk)
    if (RW0_en && RW0_wmode) begin
      if (RW0_wmask[0]) ram[RW0_addr][20:0] <= RW0_wdata[20:0];
      if (RW0_wmask[1]) ram[RW0_addr][41:21] <= RW0_wdata[41:21];
      if (RW0_wmask[2]) ram[RW0_addr][62:42] <= RW0_wdata[62:42];
      if (RW0_wmask[3]) ram[RW0_addr][83:63] <= RW0_wdata[83:63];
    end

endmodule

module data_arrays_0_0_ext(
  input RW0_clk,
  input [8:0] RW0_addr,
  input RW0_en,
  input RW0_wmode,
  input [3:0] RW0_wmask,
  input [127:0] RW0_wdata,
  output [127:0] RW0_rdata
);

/* name=data_arrays_0_0_ext, width=128, depth=512, mask_gran=32, mask_seg=4, ports=['mrw'] FPGA special case */

  infer_bram  #(
    .BRAM_SIZE(9),
    .BYTE_WIDTH(16))
    my_block_ram (
  .ram_clk(RW0_clk),    // input wire clka
  .ram_en(RW0_en),      // input wire ena
  .ram_we(RW0_wmode ? {RW0_wmask[3],RW0_wmask[3],RW0_wmask[3],RW0_wmask[3],RW0_wmask[2],RW0_wmask[2],RW0_wmask[2],RW0_wmask[2],RW0_wmask[1],RW0_wmask[1],RW0_wmask[1],RW0_wmask[1],RW0_wmask[0],RW0_wmask[0],RW0_wmask[0],RW0_wmask[0]} : 16'b0),   // input wire [15 : 0] wea
  .ram_addr(RW0_addr),  // input wire [8: 0] addra
  .ram_wrdata(RW0_wdata),  // input wire [127 : 0] dina
  .ram_rddata(RW0_rdata)  // output wire [127 : 0] douta
  );

endmodule

module mem_ext(
  input W0_clk,
  input [24:0] W0_addr,
  input W0_en,
  input [63:0] W0_data,
  input [7:0] W0_mask,
  input R0_clk,
  input [24:0] R0_addr,
  input R0_en,
  output [63:0] R0_data
);

  reg [24:0] reg_R0_addr;
  reg [63:0] ram [(1<<19)-1:0];

    integer initvar;
    initial begin
      #0.002 begin end
      for (initvar = 0; initvar < 33554432; initvar = initvar+1)
        ram[initvar] = 64'b0;
    end

  integer i;
  always @(posedge R0_clk)
    if (R0_en) reg_R0_addr <= R0_addr;
  always @(posedge W0_clk)
    if (W0_en) begin
      if (W0_mask[0]) ram[W0_addr][7:0] <= W0_data[7:0];
      if (W0_mask[1]) ram[W0_addr][15:8] <= W0_data[15:8];
      if (W0_mask[2]) ram[W0_addr][23:16] <= W0_data[23:16];
      if (W0_mask[3]) ram[W0_addr][31:24] <= W0_data[31:24];
      if (W0_mask[4]) ram[W0_addr][39:32] <= W0_data[39:32];
      if (W0_mask[5]) ram[W0_addr][47:40] <= W0_data[47:40];
      if (W0_mask[6]) ram[W0_addr][55:48] <= W0_data[55:48];
      if (W0_mask[7]) ram[W0_addr][63:56] <= W0_data[63:56];
    end
  assign R0_data = ram[reg_R0_addr];

endmodule

module mem_0_ext(
  input W0_clk,
  input [8:0] W0_addr,
  input W0_en,
  input [63:0] W0_data,
  input [7:0] W0_mask,
  input R0_clk,
  input [8:0] R0_addr,
  input R0_en,
  output reg [63:0] R0_data
);

  reg [8:0] reg_R0_addr;
  reg [63:0] ram [511:0];

    integer initvar;
    initial begin
      #0.002 begin end
      for (initvar = 0; initvar < 512; initvar = initvar+1)
        ram[initvar] = 64'b0;
    end

  integer i;
  always @(posedge R0_clk)
    if (R0_en) R0_data <= ram[R0_addr];
  always @(posedge W0_clk)
    if (W0_en) begin
      if (W0_mask[0]) ram[W0_addr][7:0] <= W0_data[7:0];
      if (W0_mask[1]) ram[W0_addr][15:8] <= W0_data[15:8];
      if (W0_mask[2]) ram[W0_addr][23:16] <= W0_data[23:16];
      if (W0_mask[3]) ram[W0_addr][31:24] <= W0_data[31:24];
      if (W0_mask[4]) ram[W0_addr][39:32] <= W0_data[39:32];
      if (W0_mask[5]) ram[W0_addr][47:40] <= W0_data[47:40];
      if (W0_mask[6]) ram[W0_addr][55:48] <= W0_data[55:48];
      if (W0_mask[7]) ram[W0_addr][63:56] <= W0_data[63:56];
    end

endmodule

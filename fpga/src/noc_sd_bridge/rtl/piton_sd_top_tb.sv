`include "piton_sd_define.vh"
// import axi_pkg::*;

module  tb();

   logic sys_clk, sd_clk, sys_rst, init_done;
   // 4-bit full SD interface
   wire         sd_sclk;
   wire         sd_detect = 1'b0; // Simulate SD-card always there
   wire [3:0]   sd_dat_to_host, sd_dat_from_host;
   wire         sd_cmd_to_host, sd_cmd_from_host;
   wire         sd_reset, oeCmd, oeDat, sd_cmd_oe_o, sd_dat_oe_o;

    parameter
      AxiAddrWidth = 64,
      AxiDataWidth = 64,
      AxiIdWidth   = 5,
      AxiUserWidth = 1;
   
    // Request Slave
    logic [`SD_ADDR_WIDTH-1:0]    req_addr_sd;    // addr in SD 
    logic [`SD_ADDR_WIDTH-1:0]    req_addr_dma;   // addr in fake memory
    logic [`SD_ADDR_WIDTH-10:0]   req_blkcnt;
   
    logic                         req_wr;     // HIGH write; LOW read.
    logic                         req_val;
    wire                         req_rdy;

    // Response Master
    wire                         resp_ok;    // HIGH ok; LOW err.
    wire                         resp_val;
   logic                         resp_rdy;
   

piton_sd_top dut
(
    // Clock and reset
    .sys_clk,
    .sd_clk,
    .sys_rst,

    // SD interface
    .sd_cd(sd_detect),
    .sd_reset,
    .sd_clk_out(sd_sclk),
    .sd_cmd_dat_i(sd_cmd_to_host),
    .sd_cmd_out_o(sd_cmd_from_host),
    .sd_cmd_oe_o,
    .sd_dat_dat_i(sd_dat_to_host),
    .sd_dat_out_o(sd_dat_from_host),
    .sd_dat_oe_o,

    .init_done,
    .req_addr_sd            (req_addr_sd),
    .req_addr_dma           (req_addr_dma),
    .req_blkcnt             (req_blkcnt),
    .req_wr                 (req_wr),
    .req_val                (req_val),
    .req_rdy                (req_rdy),

    .resp_ok                (resp_ok),
    .resp_val               (resp_val),
    .resp_rdy               (resp_rdy)
    );

   initial begin
      sys_rst = 1;
      #130;
      sys_rst = 0;
      req_addr_sd = 0;
      req_addr_dma = 0;
      req_wr = 0;
      req_val = 0;
      resp_rdy = 1;
      req_blkcnt = 8;
      
      @(posedge init_done)
        req_val = 1;
      @(posedge resp_val)
        req_val = 0;
   end

   initial begin
      sys_clk = 0;
      forever sys_clk = #5 !sys_clk;
   end // initial begin

   initial begin
      sd_clk = 0;
      forever sd_clk = #5 !sd_clk;
   end // initial begin


sd_verilator_model sdflash1 (
             .sdClk(sd_sclk),
             .cmd(sd_cmd_from_host),
             .cmdOut(sd_cmd_to_host),
             .dat(sd_dat_from_host),
             .datOut(sd_dat_to_host),
             .oeCmd(oeCmd),
             .oeDat(oeDat)
);

endmodule // tb

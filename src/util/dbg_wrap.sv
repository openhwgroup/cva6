// Copyright 2015 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the “License”); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an “AS IS” BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

`default_nettype none
`timescale 1ns/1ps

module dbg_wrap
#(
    parameter NB_CORES             = 1,
    parameter AXI_ADDR_WIDTH       = 32,
    parameter AXI_DATA_WIDTH       = 64,
    parameter AXI_ID_MASTER_WIDTH  = 4,
    parameter AXI_ID_SLAVE_WIDTH   = 4,
    parameter AXI_USER_WIDTH       = 0,
    parameter JTAG_CHAIN_START     = 1
 )
    (
    // Clock and Reset
    input logic         clk,
    input logic         rst_n,
    input  logic        testmode_i,
    output logic        aresetn,

    AXI_BUS.Master      input_if, output_if,
    // CPU signals
    output logic [15:0] cpu_addr_o, 
    input  logic [AXI_DATA_WIDTH-1:0] cpu_rdata_i, 
    output logic [AXI_DATA_WIDTH-1:0] cpu_wdata_o,
    input  logic        cpu_halted_i,
    output logic        cpu_halt_o,
    output logic        cpu_req_o,
    output logic        cpu_we_o,
    input  logic        cpu_gnt_i,
    output logic        cpu_resume_o,
    input  logic        cpu_rvalid_i,
    output logic        cpu_fetch_o,
  // JTAG signals
    input  logic        tck_i,
    input  logic        trstn_i,
    input  logic        tms_i,
    input  logic        tdi_i,
    output logic        tdo_o,
    output logic [63:0] boot_rdata,
    input  logic [15:0] boot_addr,
    input logic  [63:0] boot_wdata,
    input logic         boot_en,
    input logic  [7:0]  boot_we,
    output logic [63:0] wrap_rdata,
    input  logic [13:0] wrap_addr,
    input logic  [63:0] wrap_wdata,
    input logic         wrap_en,
    input logic  [7:0]  wrap_we,
    output logic [31:0] address,  
    input wire [15:0]   i_dip 
  );

localparam AXI4_ADDR_WIDTH = 32; // 763
localparam AXI4_ALEN_WIDTH = 8; // 763
localparam AXI4_ALOCK_WIDTH = 8; // 763
localparam AXI4_USER_WIDTH = 2; // 763
localparam AXI4_ID_WIDTH = 8; // 763
localparam SYNC_WIDTH = 4; // 763
localparam GPI_WIDTH = 4; // 763
localparam GPO_WIDTH = 4; // 763
localparam _WIDTH = 4; // 763

logic  [AXI_ADDR_WIDTH-1:0] move_src_addr;
logic  [AXI_ADDR_WIDTH-1:0] move_dest_addr;
logic  [AXI_ADDR_WIDTH-1:0] move_length;
logic  [7:0]                move_mask;
logic move_en, move_en_in, move_en_dly, move_en_edge;
logic move_done;

wire combined_rstn = rst_n && trstn_i;
logic cpu_nofetch;   
logic [15:0] cpu_addr; 
logic [AXI_DATA_WIDTH-1:0] cpu_rdata; 
logic [AXI_DATA_WIDTH-1:0] cpu_wdata;
logic        cpu_halted;
logic        cpu_halt;
logic        cpu_req;
logic        cpu_we;
logic        cpu_gnt;
logic        cpu_resume;
logic        cpu_rvalid;
logic        cpu_fetch;
  
logic [8:0] capture_address;
logic [63:0] capture_rdata;
logic pc_asserted, cpu_capture, areset;
logic [289:0] capture_input, capture_output, capture_select;

wire [96 : 0] pc_status;

    logic [5:0] DBG;
    logic WREN;
    logic [63:0] TO_MEM;
    logic [31:0] ADDR;
    logic [63:0] FROM_MEM;
    logic TCK;
    logic TCK2;
    logic RESET;
    logic RUNTEST;
    logic CAPTURE;
    logic CAPTURE2;
    logic UPDATE;
    logic UPDATE2;
   logic [63:0]  sharedmem_dout, bootmem_dout;
   logic [7:0]   sharedmem_en;
   logic [511:0] capmem_dout, capmem_shift, capture_wdata;
   logic [7:0]   bootmem_en;
   logic         cpu_en, capture_rst;
   logic [10:0]  unused1;
   logic         capmem_en;
   logic         dma_capture, dma_capture_select;
   
   wire   capture_busy = (dma_capture || cpu_capture) & !(&capture_address);
   wire [63:0] move_status = {move_done, areset, dma_capture_select, dma_capture, move_en_in, move_mask};
   assign capture_select = dma_capture_select ? capture_output : capture_input;
   assign aresetn = combined_rstn && (!areset);
   
   logic  dma_en;

   always @(posedge TCK)
     if (!combined_rstn)
       begin
          {cpu_capture, cpu_nofetch, cpu_resume, cpu_we, cpu_req, cpu_halt, cpu_addr, cpu_wdata} <= 'b0;
          {cpu_rdata, cpu_halted, cpu_gnt, cpu_rvalid} <= 'b0;
          {areset, dma_capture_select, dma_capture, move_src_addr, move_dest_addr, move_length, move_en_in, move_mask} <= 'b0; 
       end
     else if (WREN)
       begin
        {cpu_rdata, cpu_halted, cpu_gnt, cpu_rvalid} <= {cpu_rdata_i, cpu_halted_i, cpu_gnt_i, cpu_rvalid_i};
        if (cpu_en)
          begin
             if (ADDR[19])
               {cpu_capture, cpu_nofetch, cpu_resume, cpu_we, cpu_req, cpu_halt, cpu_addr} <= TO_MEM;
             else
               cpu_wdata <= TO_MEM;
          end
        if (dma_en)
          begin
             casez (ADDR[19:18])
               2'b00: move_src_addr <= TO_MEM;
               2'b01: move_dest_addr <= TO_MEM;
               2'b10: move_length <= TO_MEM;
               2'b11: {areset, dma_capture_select, dma_capture, move_en_in, move_mask} <= TO_MEM;
             endcase
          end
       end
   
    always @*
      begin
         cpu_en = 1'b0; dma_en = 1'b0;
         sharedmem_en = 8'h0; capmem_en = 1'b0; bootmem_en = 8'b0;
         capmem_shift = capmem_dout >> {ADDR[5:3],6'b0};
         casez(ADDR[23:20])
           4'hf: begin cpu_en = &ADDR[31:24];
              FROM_MEM = ADDR[19] ? {cpu_rvalid, cpu_halted, cpu_gnt, cpu_capture, cpu_nofetch, cpu_resume, cpu_we, cpu_req, cpu_halt, cpu_addr} : cpu_rdata; end
           4'h9: begin capmem_en = 1'b1; FROM_MEM = capmem_shift[63:0]; end
           4'h8: begin sharedmem_en = 8'hff; FROM_MEM = sharedmem_dout; end
           4'h6: begin dma_en = 1'b1;
              casez (ADDR[19:18])
                2'b00: FROM_MEM <= move_src_addr;
                2'b01: FROM_MEM <= move_dest_addr;
                2'b10: FROM_MEM <= move_length;
                2'b11: FROM_MEM <= move_status;
              endcase
              end               
           4'h5: begin FROM_MEM = {31'b0, pc_status[96:64]}; end
           4'h4: begin FROM_MEM = pc_status[63:0]; end
           4'h3: begin FROM_MEM = {55'b0, capture_address}; end
           4'h2: begin bootmem_en = ADDR[31:24]; FROM_MEM = bootmem_dout; end
           default: FROM_MEM = 64'hDEADBEEF;
         endcase
      end

`ifdef NOJTAG

   assign DBG = 'b0;
   assign RESET = 'b0;
   assign RUNTEST = 'b0;

   initial
     begin:init
        logic [63:0] tmpmem[0:8191];
        integer      ix = 0;
        
        $readmemh("cnvmem64.hex", tmpmem);
        TCK = 1'b0;
        WREN = 1'b0;
        TO_MEM = 64'b0;
        ADDR = 32'h000000;
        @(posedge clk)
          TCK = 1'b1;        
        @(negedge clk)
          TCK = 1'b0;
        
        @(posedge rst_n)
          for (ix = 0; ix < 'h10000; ix=ix+8)
            begin
               WREN = 1'b1;
               TO_MEM = tmpmem[ix/8];
               ADDR = 32'hFF200000 + ix;
               @(posedge clk)
                 TCK = 1'b1;        
               @(negedge clk)
                 TCK = 1'b0;
               WREN = 1'b0;
               @(posedge clk)
                 TCK = 1'b1;        
               @(negedge clk)
                 TCK = 1'b0;
            end
        
        ADDR = 32'h000000;
        
     end
`else
   
jtag_dummy #(.JTAG_CHAIN_START(JTAG_CHAIN_START)) jtag1(.*);

`endif
   
   genvar r;

   generate for (r = 0; r < 32; r=r+1)
     RAMB16_S2_S2
     RAMB16_S2_S2_inst
       (
        .CLKA   ( TCK                      ),     // Port A Clock
        .DOA    ( bootmem_dout[r*2 +: 2]   ),     // Port A 1-bit Data Output
        .ADDRA  ( ADDR[15:3]               ),     // Port A 14-bit Address Input
        .DIA    ( TO_MEM[r*2 +:2]          ),     // Port A 1-bit Data Input
        .ENA    ( bootmem_en[r/4]          ),     // Port A RAM Enable Input
        .SSRA   ( 1'b0                     ),     // Port A Synchronous Set/Reset Input
        .WEA    ( WREN                     ),     // Port A Write Enable Input
        .CLKB   ( clk                      ),     // Port B Clock
        .DOB    ( boot_rdata[r*2 +: 2]     ),     // Port B 1-bit Data Output
        .ADDRB  ( boot_addr[15:3]          ),     // Port B 14-bit Address Input
        .DIB    ( boot_wdata[r*2 +: 2]     ),     // Port B 1-bit Data Input
        .ENB    ( boot_en                  ),     // Port B RAM Enable Input
        .SSRB   ( 1'b0                     ),     // Port B Synchronous Set/Reset Input
        .WEB    ( boot_we[r/4]             )      // Port B Write Enable Input
        );
   endgenerate

   generate for (r = 0; r < 8; r=r+1)
     RAMB16_S9_S9
     RAMB16_S9_S9_inst
       (
        .CLKA   ( TCK                      ),     // Port A Clock
        .DOA    ( sharedmem_dout[r*8 +: 8] ),     // Port A 1-bit Data Output
        .DOPA   (                          ),
        .ADDRA  ( ADDR[13:3]               ),     // Port A 14-bit Address Input
        .DIA    ( TO_MEM[r*8 +:8]          ),     // Port A 1-bit Data Input
        .DIPA   ( 1'b0                     ),
        .ENA    ( sharedmem_en[r]          ),     // Port A RAM Enable Input
        .SSRA   ( 1'b0                     ),     // Port A Synchronous Set/Reset Input
        .WEA    ( WREN                     ),     // Port A Write Enable Input
        .CLKB   ( clk                      ),     // Port B Clock
        .DOB    ( wrap_rdata[r*8 +: 8]     ),     // Port B 1-bit Data Output
        .DOPB   (                          ),
        .ADDRB  ( wrap_addr[13:3]          ),     // Port B 14-bit Address Input
        .DIB    ( wrap_wdata[r*8 +: 8]     ),     // Port B 1-bit Data Input
        .DIPB   ( 1'b0                     ),
        .ENB    ( wrap_en                  ),     // Port B RAM Enable Input
        .SSRB   ( 1'b0                     ),     // Port B Synchronous Set/Reset Input
        .WEB    ( wrap_we[r]               )      // Port B Write Enable Input
        );
   endgenerate

   generate for (r = 0; r < 16; r=r+1)
     RAMB16_S36_S36
     RAMB16_S36_S36_inst
       (
        .CLKA   ( TCK                      ),     // Port A Clock
        .DOA    ( capmem_dout[r*32 +: 32]  ),     // Port A 1-bit Data Output
        .DOPA   (                          ),
        .ADDRA  ( ADDR[14:6]               ),     // Port A 14-bit Address Input
        .DIA    ( 32'b0                    ),     // Port A 1-bit Data Input
        .DIPA   ( 4'b0                     ),
        .ENA    ( capmem_en                ),     // Port A RAM Enable Input
        .SSRA   ( 1'b0                     ),     // Port A Synchronous Set/Reset Input
        .WEA    ( 1'b0                     ),     // Port A Write Enable Input
        .CLKB   ( clk                      ),     // Port B Clock
        .DOB    (                          ),     // Port B 1-bit Data Output
        .DOPB   (                          ),
        .ADDRB  ( capture_address          ),     // Port B 14-bit Address Input
        .DIB    ( capture_wdata[r*32 +: 32]),     // Port B 1-bit Data Input
        .DIPB   ( 4'b0                     ),
        .ENB    ( capture_busy             ),     // Port B RAM Enable Input
        .SSRB   ( 1'b0                     ),     // Port B Synchronous Set/Reset Input
        .WEB    ( capture_busy             )      // Port B Write Enable Input
        );
   endgenerate

always @(posedge clk)
    begin
       move_en <= move_en_in;
       move_en_dly <= move_en;
       move_en_edge <= move_en & !move_en_dly;
       {cpu_capture, cpu_fetch_o, cpu_resume_o, cpu_we_o, cpu_req_o, cpu_halt_o, cpu_addr_o, cpu_wdata_o} <=
            {cpu_capture, ~cpu_nofetch, cpu_resume, cpu_we, cpu_req, cpu_halt, cpu_addr, cpu_wdata};
       if (capture_rst)
         capture_address <= 'b0;
       else if (capture_busy)
         capture_address <= capture_address + 9'b1;
       capture_wdata <= {
 wrap_rdata,
 wrap_en,
 wrap_addr[13:0],
 boot_rdata,
 boot_addr,
 boot_wdata,
 boot_en,
 boot_we,
 capture_address[8:0],
 capture_select
 };
       
    end

capture_wrap capture1(
         .clk_i(clk),
         .rst_ni(aresetn),
         .capture(capture_input),              // output wire [96 : 0] pc_status
         .capture_if(input_if));

capture_wrap capture2(
         .clk_i(clk),
         .rst_ni(aresetn),
         .capture(capture_output),              // output wire [96 : 0] pc_status
         .capture_if(output_if));

   nasti_channel
  #(
    .ID_WIDTH    ( AXI_ID_MASTER_WIDTH      ),
    .USER_WIDTH  ( AXI_USER_WIDTH    ),
    .ADDR_WIDTH  ( AXI_ADDR_WIDTH    ),
    .DATA_WIDTH  ( AXI_DATA_WIDTH    ))
 move_src(), move_dest();

   if_converter #(
 .ID_WIDTH(AXI_ID_MASTER_WIDTH),               // id width
 .ADDR_WIDTH(AXI_ADDR_WIDTH),             // address width
 .DATA_WIDTH(AXI_DATA_WIDTH),             // width of data
 .USER_WIDTH(AXI_USER_WIDTH)              // width of user field, must > 0, let synthesizer trim it if not in use
 ) cnv0(.incoming_nasti(move_src), .outgoing_if(input_if)),
   cnv1(.incoming_nasti(move_dest), .outgoing_if(output_if));

nasti_data_mover # (
   .ADDR_WIDTH(64),
   .DATA_WIDTH(64)) move1 (
   .aclk(clk),
   .aresetn(aresetn),
   .src(move_src),
   .dest(move_dest),
   .src_addr(move_src_addr),
   .dest_addr(move_dest_addr),
   .length(move_length),
   .mask(move_mask),
   .en(move_en_edge),
   .done(move_done)
);
  
`ifdef PROTO_WRAPPER
   axi_proto_wrap #(
    .ID_WIDTH(AXI_ID_SLAVE_WIDTH),           // id width
    .ADDR_WIDTH(AXI_ADDR_WIDTH),             // address width
    .DATA_WIDTH(AXI_DATA_WIDTH),             // width of data
    .USER_WIDTH(AXI_USER_WIDTH)              // width of user field, must > 0, let synthesizer trim it if not in use
    ) axi_proto1(
        .clk(clk),
        .aresetn(aresetn),
        .pc_status(pc_status),              // output wire [96 : 0] pc_status
        .pc_asserted(pc_asserted),          // output wire pc_asserted
        .proto_if(dbg_master));
`endif

`ifdef PROTO_CHECKER
axi_protocol_checker_0 pc1 (
  .pc_status(pc_status),              // output wire [96 : 0] pc_status
  .pc_asserted(pc_asserted),          // output wire pc_asserted
  .system_resetn(aresetn),            // input wire system_resetn
  .aclk(clk),                         // input wire aclk
  .aresetn(aresetn),                  // input wire aresetn
  .pc_axi_awid(dbg_master.aw_id),
  .pc_axi_awaddr(dbg_master.aw_addr),
  .pc_axi_awlen(dbg_master.aw_len),
  .pc_axi_awsize(dbg_master.aw_size),
  .pc_axi_awburst(dbg_master.aw_burst),
  .pc_axi_awlock(dbg_master.aw_lock),
  .pc_axi_awcache(dbg_master.aw_cache),
  .pc_axi_awprot(dbg_master.aw_prot),
  .pc_axi_awregion(dbg_master.aw_region),
  .pc_axi_awqos(dbg_master.aw_qos),
  .pc_axi_awuser(dbg_master.aw_user),
  .pc_axi_awvalid(dbg_master.aw_valid),
  .pc_axi_awready(dbg_master.aw_ready),
  .pc_axi_wdata(dbg_master.w_data),
  .pc_axi_wstrb(dbg_master.w_strb),
  .pc_axi_wlast(dbg_master.w_last),
  .pc_axi_wuser(dbg_master.w_user),
  .pc_axi_wvalid(dbg_master.w_valid),
  .pc_axi_wready(dbg_master.w_ready),
  .pc_axi_bid(dbg_master.b_id),
  .pc_axi_bresp(dbg_master.b_resp),
  .pc_axi_buser(dbg_master.b_user),
  .pc_axi_bvalid(dbg_master.b_valid),
  .pc_axi_bready(dbg_master.b_ready),
  .pc_axi_arid(dbg_master.ar_id),
  .pc_axi_araddr(dbg_master.ar_addr),
  .pc_axi_arlen(dbg_master.ar_len),
  .pc_axi_arsize(dbg_master.ar_size),
  .pc_axi_arburst(dbg_master.ar_burst),
  .pc_axi_arlock(dbg_master.ar_lock),
  .pc_axi_arcache(dbg_master.ar_cache),
  .pc_axi_arprot(dbg_master.ar_prot),
  .pc_axi_arregion(dbg_master.ar_region),
  .pc_axi_arqos(dbg_master.ar_qos),
  .pc_axi_aruser(dbg_master.ar_user),
  .pc_axi_arvalid(dbg_master.ar_valid),
  .pc_axi_arready(dbg_master.ar_ready),
  .pc_axi_rid(dbg_master.r_id),
  .pc_axi_rdata(dbg_master.r_data),
  .pc_axi_rresp(dbg_master.r_resp),
  .pc_axi_rlast(dbg_master.r_last),
  .pc_axi_ruser(dbg_master.r_user),
  .pc_axi_rvalid(dbg_master.r_valid),
  .pc_axi_rready(dbg_master.r_ready)
);
`endif

always @*
    casez (i_dip[15:14])
                2'b00: address <= move_src_addr;
                2'b01: address <= move_dest_addr;
                2'b10: address <= move_length;
                2'b11: address <= move_status;
    endcase
    
endmodule

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

    AXI_BUS.Master      dbg_master, input_if, output_if,
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
    output logic [31:0] address    
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
logic move_en;
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
  
logic go;   
wire error;
logic RNW;  
wire busy; 
wire done; 
logic [7:0] burst_length;        //: in integer range 1 to 256; -- number of beats in a burst
logic [6:0] burst_size;          //: in integer range 1 to 128;  -- number of byte lanes in each beat
logic increment_burst;   
logic [8:0] capture_address;
logic [63:0] capture_rdata;
logic [2:0] current_state;
logic [2:0] current_state_rac;
logic [2:0] current_state_resp;
logic [2:0] current_state_wrdata;
logic [9:0] start_out;
logic read_data_valid, write_data_valid, pc_asserted, cpu_capture;

wire [96 : 0] pc_status;

    wire [5:0] DBG;
    wire WREN;
    wire [63:0] TO_MEM;
    wire [31:0] ADDR;
    logic [63:0] FROM_MEM;
    wire TCK;
    wire TCK2;
    wire RESET;
    wire RUNTEST;
    wire CAPTURE;
    wire CAPTURE2;
    wire UPDATE;
    wire UPDATE2;
   logic [63:0]  sharedmem_dout, bootmem_dout;
   logic [7:0]   sharedmem_en;
   logic [511:0] capmem_dout, capmem_shift, capture_wdata;
   logic [7:0]   bootmem_en;
   logic         burst_en, cpu_en, capture_rst;
   logic [10:0]  unused1;
   logic         capmem_en;
   logic                          dma_capture;
   
   wire   capture_busy = (dma_capture || cpu_capture) & !(&capture_address);
   logic  dma_en, wrap_rst_notused;

   always @(posedge TCK)
     if (!combined_rstn)
       begin
          {capture_rst, wrap_rst_notused, aresetn, go, increment_burst, RNW, burst_size, burst_length, address} <= 'b0;
          {cpu_capture, cpu_nofetch, cpu_resume, cpu_we, cpu_req, cpu_halt, cpu_addr, cpu_wdata} <= 'b0;
          {cpu_rdata, cpu_halted, cpu_gnt, cpu_rvalid} <= 'b0;
          {move_src_addr, move_dest_addr, move_length, move_en} <= 'b0; 
       end
     else if (WREN)
       begin
        {cpu_rdata, cpu_halted, cpu_gnt, cpu_rvalid} <= {cpu_rdata_i, cpu_halted_i, cpu_gnt_i, cpu_rvalid_i};
        if (burst_en)
          begin
             {unused1[10:0],capture_rst, wrap_rst_notused, aresetn, go, increment_burst, RNW, burst_size, burst_length, address} <= TO_MEM;
          end
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
               2'b11: {dma_capture, move_en} <= TO_MEM;
             endcase
          end
       end
   
    always @*
      begin
         cpu_en = 1'b0; burst_en = 1'b0; dma_en = 1'b0;
         sharedmem_en = 8'h0; capmem_en = 1'b0; bootmem_en = 8'b0;
         capmem_shift = capmem_dout >> {ADDR[5:3],6'b0};
         casez(ADDR[23:20])
           4'hf: begin cpu_en = &ADDR[31:24];
              FROM_MEM = ADDR[19] ? {cpu_rvalid, cpu_halted, cpu_gnt, cpu_capture, cpu_nofetch, cpu_resume, cpu_we, cpu_req, cpu_halt, cpu_addr} : cpu_rdata; end
           4'h9: begin capmem_en = 1'b1; FROM_MEM = capmem_shift[63:0]; end
           4'h8: begin sharedmem_en = 8'hff; FROM_MEM = sharedmem_dout; end
           4'h7: begin burst_en = 1'b1; FROM_MEM = {11'b0, capture_rst, wrap_rst_notused, aresetn, go,
                                                    increment_burst, RNW, burst_size, burst_length, address}; end
           4'h6: begin dma_en = 1'b1;
              casez (ADDR[19:18])
                2'b00: FROM_MEM <= move_src_addr;
                2'b01: FROM_MEM <= move_dest_addr;
                2'b10: FROM_MEM <= move_length;
                2'b11: FROM_MEM <= {move_done, dma_capture, move_en};
              endcase
              end               
           4'h5: begin FROM_MEM = {31'b0, pc_status[96:64]}; end
           4'h4: begin FROM_MEM = pc_status[63:0]; end
           4'h3: begin FROM_MEM = {55'b0, capture_address}; end
           4'h2: begin bootmem_en = ADDR[31:24]; FROM_MEM = bootmem_dout; end
           default: FROM_MEM = 64'hDEADBEEF;
         endcase
      end

jtag_dummy #(.JTAG_CHAIN_START(JTAG_CHAIN_START)) jtag1(.*);

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
 read_data_valid,
 write_data_valid,
 boot_rdata,
 boot_addr,
 boot_wdata,
 boot_en,
 boot_we,
 capture_address[8:0],
 current_state_resp,                         
 current_state,                         
 current_state_wrdata,                         
 current_state_rac,
 start_out,                      
 done,
 busy,
 error,
 dbg_master.aw_valid  ,
 dbg_master.aw_prot   ,
 dbg_master.aw_region ,
 dbg_master.aw_len    ,
 dbg_master.aw_size   ,
 dbg_master.aw_burst  ,
 dbg_master.aw_lock   ,
 dbg_master.aw_cache  ,
 dbg_master.aw_qos    ,
 dbg_master.aw_id     ,
 dbg_master.aw_ready  ,
 dbg_master.ar_valid  ,
 dbg_master.ar_prot   ,
 dbg_master.ar_region ,
 dbg_master.ar_len    ,
 dbg_master.ar_size   ,
 dbg_master.ar_burst  ,
 dbg_master.ar_lock   ,
 dbg_master.ar_cache  ,
 dbg_master.ar_qos    ,
 dbg_master.ar_id     ,
 dbg_master.ar_ready  ,
 dbg_master.w_valid   ,
 dbg_master.w_strb    ,
 dbg_master.w_last    ,
 dbg_master.w_ready   ,
 dbg_master.r_valid   ,
 dbg_master.r_resp    ,
 dbg_master.r_last    ,
 dbg_master.r_id      ,
 dbg_master.r_ready   ,
 dbg_master.b_valid   ,
 dbg_master.b_resp    ,
 dbg_master.b_id      ,
 dbg_master.b_ready   ,
 dbg_master.w_data    ,
 dbg_master.r_data    ,
 dbg_master.aw_addr   ,
 dbg_master.ar_addr   
  };
       
    end

`ifdef SCATTER_GATHER_DMA

   logic                          dma_req;
   logic                          dma_gnt;
   logic                          dma_rvalid;
   logic                          dma_introut;
   logic [31:0]                   dma_addr;
   logic                          dma_we;
   logic [3:0]                    dma_be;
   logic [31:0]                   dma_rdata;
   logic [31:0]                   dma_wdata;
   logic [31:0]                   dma_tvect;

    AXI_BUS #(
              .AXI_ADDR_WIDTH ( 32 ),
              .AXI_DATA_WIDTH ( 32 ),
              .AXI_ID_WIDTH   ( 4  ),
              .AXI_USER_WIDTH ( 2  )
    ) ctrl_if();
  
core2axi dma_if(
.clk_i(clk),
.rst_ni(aresetn),

.data_req_i(dma_req),
.data_gnt_o(dma_gnt),
.data_rvalid_o(dma_rvalid),
.data_addr_i(dma_addr),
.data_we_i(dma_we),
.data_be_i(dma_be),
.data_rdata_o(dma_rdata),
.data_wdata_i(dma_wdata),

    // ---------------------------------------------------------
    // AXI TARG Port Declarations ------------------------------
    // ---------------------------------------------------------
    //AXI write address bus -------------- // USED// -----------
.aw_id_o(ctrl_if.aw_id),
.aw_addr_o(ctrl_if.aw_addr),
.aw_len_o(ctrl_if.aw_len),
.aw_size_o(ctrl_if.aw_size),
.aw_burst_o(ctrl_if.aw_burst),
.aw_lock_o(ctrl_if.aw_lock),
.aw_cache_o(ctrl_if.aw_cache),
.aw_prot_o(ctrl_if.aw_prot),
.aw_region_o(ctrl_if.aw_region),
.aw_user_o(ctrl_if.aw_user),
.aw_qos_o(ctrl_if.aw_qos),
.aw_valid_o(ctrl_if.aw_valid),
.aw_ready_i(ctrl_if.aw_ready),
    // ---------------------------------------------------------

    //AXI write data bus -------------- // USED// --------------
.w_data_o(ctrl_if.w_data),
.w_strb_o(ctrl_if.w_strb),
.w_last_o(ctrl_if.w_last),
.w_user_o(ctrl_if.w_user),
.w_valid_o(ctrl_if.w_valid),
.w_ready_i(ctrl_if.w_ready),
    // ---------------------------------------------------------

    //AXI write response bus -------------- // USED// ----------
.b_id_i(ctrl_if.b_id),
.b_resp_i(ctrl_if.b_resp),
.b_valid_i(ctrl_if.b_valid),
.b_user_i(ctrl_if.b_user),
.b_ready_o(ctrl_if.b_ready),
    // ---------------------------------------------------------

    //AXI read address bus -------------------------------------
.ar_id_o(ctrl_if.ar_id),
.ar_addr_o(ctrl_if.ar_addr),
.ar_len_o(ctrl_if.ar_len),
.ar_size_o(ctrl_if.ar_size),
.ar_burst_o(ctrl_if.ar_burst),
.ar_lock_o(ctrl_if.ar_lock),
.ar_cache_o(ctrl_if.ar_cache),
.ar_prot_o(ctrl_if.ar_prot),
.ar_region_o(ctrl_if.ar_region),
.ar_user_o(ctrl_if.ar_user),
.ar_qos_o(ctrl_if.ar_qos),
.ar_valid_o(ctrl_if.ar_valid),
.ar_ready_i(ctrl_if.ar_ready),
    // ---------------------------------------------------------

    //AXI read data bus ----------------------------------------
.r_id_i(ctrl_if.r_id),
.r_data_i(ctrl_if.r_data),
.r_resp_i(ctrl_if.r_resp),
.r_last_i(ctrl_if.r_last),
.r_user_i(ctrl_if.r_user),
.r_valid_i(ctrl_if.r_valid),
.r_ready_o(ctrl_if.r_ready)
);

PUMP_AXI4_TO_AXI4 DUT (
	.ARESETn(aresetn),
	.C_CLK(clk),
	.C_ARID(ctrl_if.ar_id),
	.C_ARADDR(ctrl_if.ar_addr),
	.C_ARLEN(ctrl_if.ar_len),
	.C_ARSIZE(ctrl_if.ar_size),
	.C_ARBURST(ctrl_if.ar_burst),
	.C_ARVALID(ctrl_if.ar_valid),
	.C_ARREADY(ctrl_if.ar_ready),
	.C_RID(ctrl_if.r_id),
	.C_RDATA(ctrl_if.r_data),
	.C_RRESP(ctrl_if.r_resp),
	.C_RLAST(ctrl_if.r_last),
	.C_RVALID(ctrl_if.r_valid),
	.C_RREADY(ctrl_if.r_ready),
	.C_AWID(ctrl_if.aw_id),
	.C_AWADDR(ctrl_if.aw_addr),
	.C_AWLEN(ctrl_if.aw_len),
	.C_AWSIZE(ctrl_if.aw_size),
	.C_AWBURST(ctrl_if.aw_burst),
	.C_AWVALID(ctrl_if.aw_valid),
	.C_AWREADY(ctrl_if.aw_ready),
	.C_WDATA(ctrl_if.w_data),
	.C_WSTRB(ctrl_if.w_strb),
	.C_WLAST(ctrl_if.w_last),
	.C_WVALID(ctrl_if.w_valid),
	.C_WREADY(ctrl_if.w_ready),
	.C_BID(ctrl_if.b_id),
	.C_BRESP(ctrl_if.b_resp),
	.C_BVALID(ctrl_if.b_valid),
	.C_BREADY(ctrl_if.b_ready),
	.M_CLK(clk),
	.M_ARID(dbg_master.ar_id),
	.M_ARADDR(dbg_master.ar_addr),
	.M_ARLEN(dbg_master.ar_len),
	.M_ARSIZE(dbg_master.ar_size),
	.M_ARBURST(dbg_master.ar_burst),
	.M_ARLOCK(dbg_master.ar_lock),
	.M_ARCACHE(dbg_master.ar_cache),
	.M_ARPROT(dbg_master.ar_prot),
	.M_ARQOS(dbg_master.ar_qos),
	.M_ARREGION(dbg_master.ar_region),
	.M_ARUSER(dbg_master.ar_user),
	.M_ARVALID(dbg_master.ar_valid),
	.M_ARREADY(dbg_master.ar_ready),
	.M_RID(dbg_master.r_id),
	.M_RDATA(dbg_master.r_data),
	.M_RRESP(dbg_master.r_resp),
	.M_RLAST(dbg_master.r_last),
	.M_RVALID(dbg_master.r_valid),
	.M_RREADY(dbg_master.r_ready),
	.M_AWID(dbg_master.aw_id),
	.M_AWADDR(dbg_master.aw_addr),
	.M_AWLEN(dbg_master.aw_len),
	.M_AWSIZE(dbg_master.aw_size),
	.M_AWBURST(dbg_master.aw_burst),
	.M_AWLOCK(dbg_master.aw_lock),
	.M_AWCACHE(dbg_master.aw_cache),
	.M_AWPROT(dbg_master.aw_prot),
	.M_AWQOS(dbg_master.aw_qos),
	.M_AWREGION(dbg_master.aw_region),
	.M_AWUSER(dbg_master.aw_user),
	.M_AWVALID(dbg_master.aw_valid),
	.M_AWREADY(dbg_master.aw_ready),
	.M_WDATA(dbg_master.w_data),
	.M_WSTRB(dbg_master.w_strb),
	.M_WLAST(dbg_master.w_last),
	.M_WVALID(dbg_master.w_valid),
	.M_WREADY(dbg_master.w_ready),
	.M_BID(dbg_master.b_id),
	.M_BRESP(dbg_master.b_resp),
	.M_BVALID(dbg_master.b_valid),
	.M_BREADY(dbg_master.b_ready),
	.I_CLK(clk),
	.I_ARID(input_if.ar_id),
	.I_ARADDR(input_if.ar_addr),
	.I_ARLEN(input_if.ar_len),
	.I_ARSIZE(input_if.ar_size),
	.I_ARBURST(input_if.ar_burst),
	.I_ARLOCK(input_if.ar_lock),
	.I_ARCACHE(input_if.ar_cache),
	.I_ARPROT(input_if.ar_prot),
	.I_ARQOS(input_if.ar_qos),
	.I_ARREGION(input_if.ar_region),
	.I_ARUSER(input_if.ar_user),
	.I_ARVALID(input_if.ar_valid),
	.I_ARREADY(input_if.ar_ready),
	.I_RID(input_if.r_id),
	.I_RDATA(input_if.r_data),
	.I_RRESP(input_if.r_resp),
	.I_RLAST(input_if.r_last),
	.I_RVALID(input_if.r_valid),
	.I_RREADY(input_if.r_ready),
	.I_AWID(input_if.aw_id),
	.I_AWADDR(input_if.aw_addr),
	.I_AWLEN(input_if.aw_len),
	.I_AWSIZE(input_if.aw_size),
	.I_AWBURST(input_if.aw_burst),
	.I_AWLOCK(input_if.aw_lock),
	.I_AWCACHE(input_if.aw_cache),
	.I_AWPROT(input_if.aw_prot),
	.I_AWQOS(input_if.aw_qos),
	.I_AWREGION(input_if.aw_region),
	.I_AWUSER(input_if.aw_user),
	.I_AWVALID(input_if.aw_valid),
	.I_AWREADY(input_if.aw_ready),
	.I_WDATA(input_if.w_data),
	.I_WSTRB(input_if.w_strb),
	.I_WLAST(input_if.w_last),
	.I_WVALID(input_if.w_valid),
	.I_WREADY(input_if.w_ready),
	.I_BID(input_if.b_id),
	.I_BRESP(input_if.b_resp),
	.I_BVALID(input_if.b_valid),
	.I_BREADY(input_if.b_ready),
	.O_CLK(clk),
	.O_ARID(output_if.ar_id),
	.O_ARADDR(output_if.ar_addr),
	.O_ARLEN(output_if.ar_len),
	.O_ARSIZE(output_if.ar_size),
	.O_ARBURST(output_if.ar_burst),
	.O_ARLOCK(output_if.ar_lock),
	.O_ARCACHE(output_if.ar_cache),
	.O_ARPROT(output_if.ar_prot),
	.O_ARQOS(output_if.ar_qos),
	.O_ARREGION(output_if.ar_region),
	.O_ARUSER(output_if.ar_user),
	.O_ARVALID(output_if.ar_valid),
	.O_ARREADY(output_if.ar_ready),
	.O_RID(output_if.r_id),
	.O_RDATA(output_if.r_data),
	.O_RRESP(output_if.r_resp),
	.O_RLAST(output_if.r_last),
	.O_RVALID(output_if.r_valid),
	.O_RREADY(output_if.r_ready),
	.O_AWID(output_if.aw_id),
	.O_AWADDR(output_if.aw_addr),
	.O_AWLEN(output_if.aw_len),
	.O_AWSIZE(output_if.aw_size),
	.O_AWBURST(output_if.aw_burst),
	.O_AWLOCK(output_if.aw_lock),
	.O_AWCACHE(output_if.aw_cache),
	.O_AWPROT(output_if.aw_prot),
	.O_AWQOS(output_if.aw_qos),
	.O_AWREGION(output_if.aw_region),
	.O_AWUSER(output_if.aw_user),
	.O_AWVALID(output_if.aw_valid),
	.O_AWREADY(output_if.aw_ready),
	.O_WDATA(output_if.w_data),
	.O_WSTRB(output_if.w_strb),
	.O_WLAST(output_if.w_last),
	.O_WVALID(output_if.w_valid),
	.O_WREADY(output_if.w_ready),
	.O_BID(output_if.b_id),
	.O_BRESP(output_if.b_resp),
	.O_BVALID(output_if.b_valid),
	.O_BREADY(output_if.b_ready),
	.I_IRQ(i_irq),
	.O_IRQ(o_irq)
);
`else
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
   .en(move_en),
   .done(move_done)
);
`endif
  
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

endmodule

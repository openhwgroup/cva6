// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// Author: Florian Zaruba, ETH Zurich
// Date: 19.03.2017
// Description: Ariane Top-level module

import ariane_pkg::*;

module ariane_wrapped #(
        parameter logic [63:0] CACHE_START_ADDR  = 64'h8000_0000, // address on which to decide whether the request is cache-able or not
        parameter int unsigned AXI_ID_WIDTH      = 10,
        parameter int unsigned AXI_USER_WIDTH    = 1,
        parameter int unsigned AXI_ADDRESS_WIDTH = 64,
        parameter int unsigned AXI_DATA_WIDTH    = 64
    )(
        input  logic                           clk_i,
        input  logic                           rst_ni,
        input  logic                           test_en_i,     // enable all clock gates for testing
        // CPU Control Signals
        input  logic                           fetch_enable_i,
        // Core ID, Cluster ID and boot address are considered more or less static
        input  logic [63:0]                    boot_addr_i,
        input  logic [ 3:0]                    core_id_i,
        input  logic [ 5:0]                    cluster_id_i,
        input  logic                           flush_req_i,
        output logic                           flushing_o,
        // Interrupt inputs
        input  logic [1:0]                     irq_i,        // level sensitive IR lines, mip & sip
        input  logic                           ipi_i,        // inter-processor interrupts
        output logic                           sec_lvl_o,    // current privilege level oot
        // Timer facilities
        input  logic [63:0]                    time_i,        // global time (most probably coming from an RTC)
        input  logic                           time_irq_i,    // timer interrupt in
        
        input logic [15:0] i_dip,
        output logic [15:0] o_led
    );

    localparam int unsigned AXI_NUMBYTES = AXI_DATA_WIDTH/8;

    logic        flush_dcache_ack, flush_dcache;
    logic        flush_dcache_d, flush_dcache_q;

    AXI_BUS #(
        .AXI_ADDR_WIDTH ( 64             ),
        .AXI_DATA_WIDTH ( 64             ),
        .AXI_ID_WIDTH   ( AXI_ID_WIDTH   ),
        .AXI_USER_WIDTH ( AXI_USER_WIDTH )
    ) data_if();

    AXI_BUS #(
        .AXI_ADDR_WIDTH ( 64             ),
        .AXI_DATA_WIDTH ( 64             ),
        .AXI_ID_WIDTH   ( AXI_ID_WIDTH   ),
        .AXI_USER_WIDTH ( AXI_USER_WIDTH )
    ) bypass_if();

    AXI_BUS #(
        .AXI_ADDR_WIDTH ( 64             ),
        .AXI_DATA_WIDTH ( 64             ),
        .AXI_ID_WIDTH   ( AXI_ID_WIDTH   ),
        .AXI_USER_WIDTH ( AXI_USER_WIDTH )
    ) instr_if();

    ariane #(
        .CACHE_START_ADDR ( CACHE_START_ADDR ),
        .AXI_ID_WIDTH     ( 10               ),
        .AXI_USER_WIDTH   ( 1                )
    ) i_ariane (
        .*,
        .flush_dcache_i         ( flush_dcache         ),
        .flush_dcache_ack_o     ( flush_dcache_ack     ),
        .data_if                ( data_if              ),
        .bypass_if              ( bypass_if            ),
        .instr_if               ( instr_if             )
    );

    assign flush_dcache = flush_dcache_q;
    assign flushing_o = flush_dcache_q;

    // direct store interface
    always_ff @(posedge clk_i or negedge rst_ni) begin

        automatic logic [63:0] store_address;

        if (~rst_ni) begin
            flush_dcache_q  <= 1'b0;
        end else begin
            // got acknowledge from dcache - release the flush signal
            if (flush_dcache_ack)
                flush_dcache_q <= 1'b0;

            if (flush_req_i) begin
                flush_dcache_q <= 1'b1;
            end
        end
    end

    logic        instr_req,     bypass_req,     data_req;
    logic [63:0] instr_address, bypass_address, data_address;
    logic        instr_we,      bypass_we,      data_we;
    logic [7:0]  instr_be,      bypass_be,      data_be;
    logic [63:0] instr_wdata,   bypass_wdata,   data_wdata;
    logic [63:0] instr_rdata,   bypass_rdata,   data_rdata;

   logic [31:0] debug_addr;

   // sharedmem shared port
   logic [7:0]  sharedmem_en;
   logic [63:0] sharedmem_dout;
   logic [31:0] shared_rdata;
   logic        shared_sel;

   // datamem shared port
   logic [0:0]  datamem_web;
   logic [7:0]  datamem_enb;
   logic [63:0] datamem_doutb;
  
   // progmem shared port
   logic [0:0]  progmem_web;
   logic [7:0]  progmem_enb;
   logic [63:0] progmem_doutb;
   
        // Debug Interface
         logic                           debug_req_i;
         logic                           debug_gnt_o;
         logic                           debug_rvalid_o;
         logic [15:0]                    debug_addr_i = debug_addr[15:0];
         logic                           debug_we_i;
         logic [63:0]                    debug_wdata_i;
         logic [63:0]                    debug_rdata_o;
         logic                           debug_halted_o;
         logic                           debug_halt_i;
         logic                           debug_resume_i;

   logic        debug_reset;
   logic        debug_runtest;
   logic        debug_clk, debug_clk2, debug_blocksel;
   logic [2:0]  debug_unused;
   
   logic [63:0] debug_dout;

    axi2mem #(
        .AXI_ID_WIDTH   ( AXI_ID_WIDTH      ),
        .AXI_ADDR_WIDTH ( AXI_ADDRESS_WIDTH ),
        .AXI_DATA_WIDTH ( AXI_DATA_WIDTH    ),
        .AXI_USER_WIDTH ( AXI_USER_WIDTH    )
    ) i_bypass (
        .clk_i  ( clk_i          ),
        .rst_ni ( rst_ni         ),
        .slave  ( bypass_if      ),
        .req_o  ( bypass_req     ),
        .we_o   ( bypass_we      ),
        .addr_o ( bypass_address ),
        .be_o   ( bypass_be      ),
        .data_o ( bypass_wdata   ),
        .data_i ( bypass_rdata   )
    );
    
    axi2mem #(
        .AXI_ID_WIDTH   ( AXI_ID_WIDTH      ),
        .AXI_ADDR_WIDTH ( AXI_ADDRESS_WIDTH ),
        .AXI_DATA_WIDTH ( AXI_DATA_WIDTH    ),
        .AXI_USER_WIDTH ( AXI_USER_WIDTH    )
    ) i_data (
        .clk_i  ( clk_i        ),
        .rst_ni ( rst_ni       ),
        .slave  ( data_if      ),
        .req_o  ( data_req     ),
        .we_o   ( data_we      ),
        .addr_o ( data_address ),
        .be_o   ( data_be      ),
        .data_o ( data_wdata   ),
        .data_i ( data_rdata   )
    );

data_ram my_data_ram (
  .clka(clk_i),    // input wire clka
  .ena(data_req),      // input wire ena
  .wea(data_we ? data_be : 8'b0),      // input wire [7 : 0] wea
  .addra(data_address[16:3]),  // input wire [3 : 0] addra
  .dina(data_wdata),    // input wire [63 : 0] dina
  .douta(data_rdata),  // output wire [63 : 0] douta
  .clkb(debug_clk),    // input wire clkb
  .enb(|datamem_enb),      // input wire enb
  .web(datamem_web ? datamem_enb : 8'b0),      // input wire [7 : 0] web
  .addrb(debug_addr[16:3]),  // input wire [3 : 0] addrb
  .dinb(debug_wdata_i),    // input wire [63 : 0] dinb
  .doutb(datamem_doutb)  // output wire [63 : 0] doutb
);

/*
infer_bram  #(
        .BRAM_SIZE(10),
        .BYTE_WIDTH(8))
        my_data_ram (
      .ram_clk(clk_i),    // input wire clka
      .ram_en(data_req),      // input wire ena
      .ram_we(data_we ? data_be : 8'b0),   // input wire [31 : 0] wea
      .ram_addr(data_address[11:3]),  // input wire [8: 0] addra
      .ram_wrdata(data_wdata),  // input wire [255 : 0] dina
      .ram_rddata(data_rdata)  // output wire [255 : 0] douta
      );
*/

    axi2mem #(
        .AXI_ID_WIDTH   ( AXI_ID_WIDTH      ),
        .AXI_ADDR_WIDTH ( AXI_ADDRESS_WIDTH ),
        .AXI_DATA_WIDTH ( AXI_DATA_WIDTH    ),
        .AXI_USER_WIDTH ( AXI_USER_WIDTH    )
    ) i_instr (
        .clk_i  ( clk_i         ),
        .rst_ni ( rst_ni        ),
        .slave  ( instr_if      ),
        .req_o  ( instr_req     ),
        .we_o   ( instr_we      ),
        .addr_o ( instr_address ),
        .be_o   ( instr_be      ),
        .data_o ( instr_wdata   ),
        .data_i ( instr_rdata   )
    );

instr_ram my_instr_ram (
  .clka(clk_i),    // input wire clka
  .ena(instr_req),      // input wire ena
  .wea(instr_we ? instr_be : 8'b0),      // input wire [7 : 0] wea
  .addra(instr_address[16:3]),  // input wire [3 : 0] addra
  .dina(instr_wdata),    // input wire [63 : 0] dina
  .douta(instr_rdata),  // output wire [63 : 0] douta
  .clkb(debug_clk),    // input wire clkb
  .enb(|progmem_enb),      // input wire enb
  .web(progmem_web ? progmem_enb : 8'b0),      // input wire [7 : 0] web
  .addrb(debug_addr[16:3]),  // input wire [3 : 0] addrb
  .dinb(debug_wdata_i),    // input wire [63 : 0] dinb
  .doutb(progmem_doutb)  // output wire [63 : 0] doutb
);

/*   
infer_bram  #(
    .BRAM_SIZE(10),
    .BYTE_WIDTH(8))
    my_instr_ram (
  .ram_clk(clk_i),    // input wire clka
  .ram_en(instr_req),      // input wire ena
  .ram_we(instr_we ? instr_be : 8'b0),   // input wire [31 : 0] wea
  .ram_addr(instr_address[11:3]),  // input wire [8: 0] addra
  .ram_wrdata(instr_wdata),  // input wire [255 : 0] dina
  .ram_rddata(instr_rdata)  // output wire [255 : 0] douta
  );
*/

    always @*
        begin      
        progmem_enb = 8'h0; datamem_enb = 8'h0; sharedmem_en = 8'h0; debug_blocksel = 8'b0;
        casez(debug_addr[23:20])
            4'h0: begin progmem_enb = 8'hff; debug_dout = progmem_doutb; end
            4'h1: begin datamem_enb = 8'hff; debug_dout = datamem_doutb; end
            4'h8: begin sharedmem_en = 8'hff; debug_dout = sharedmem_dout; end
            4'hf: begin debug_blocksel = &debug_addr[31:24]; debug_dout = debug_rdata_o; end
            default: debug_dout = 64'hDEADBEEF;
            endcase
        end

jtag_dummy jtag1(
    .DBG({debug_unused[2:0],debug_halt_i,debug_resume_i,debug_req_i}),
    .WREN(debug_we_i),
    .FROM_MEM(debug_dout),
    .ADDR(debug_addr),
    .TO_MEM(debug_wdata_i),
    .TCK(debug_clk),
    .TCK2(debug_clk2),
    .RESET(debug_reset),
    .RUNTEST(debug_runtest));

   genvar r;

//logic [3:0]  bypass_be;
logic        ce_d;
logic        we_d;

   wire [7:0] m_enb = (we_d ? bypass_be : 8'hFF);
   wire m_web = ce_d & shared_sel & we_d;
   logic i_emdio, o_emdio, oe_emdio, o_emdclk, sync, cooked, tx_enable_old, loopback, loopback2;
   logic [10:0] rx_addr;
   logic [7:0] rx_data;
   logic rx_ena, rx_wea;

   generate for (r = 0; r < 8; r=r+1)
     RAMB16_S9_S9
     RAMB16_S9_S9_inst
       (
        .CLKA   ( debug_clk                ),     // Port A Clock
        .DOA    ( sharedmem_dout[r*8 +: 8] ),     // Port A 1-bit Data Output
        .DOPA   (                          ),
        .ADDRA  ( debug_addr[13:3]         ),     // Port A 14-bit Address Input
        .DIA    ( debug_wdata_i[r*8 +:8]   ),     // Port A 1-bit Data Input
        .DIPA   ( 1'b0                     ),
        .ENA    ( sharedmem_en[r]          ),     // Port A RAM Enable Input
        .SSRA   ( 1'b0                     ),     // Port A Synchronous Set/Reset Input
        .WEA    ( debug_we_i               ),     // Port A Write Enable Input
        .CLKB   ( clk_i                    ),     // Port B Clock
        .DOB    ( bypass_rdata[r*8 +: 8]   ),     // Port B 1-bit Data Output
        .DOPB   (                          ),
        .ADDRB  ( bypass_address[13:3]     ),     // Port B 14-bit Address Input
        .DIB    ( bypass_wdata[r*8 +: 8]   ),     // Port B 1-bit Data Input
        .DIPB   ( 1'b0                     ),
        .ENB    ( m_enb[r]                 ),     // Port B RAM Enable Input
        .SSRB   ( 1'b0                     ),     // Port B Synchronous Set/Reset Input
        .WEB    ( m_web                    )      // Port B Write Enable Input
        );
   endgenerate

endmodule


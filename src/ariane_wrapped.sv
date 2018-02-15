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
        // Core ID, Cluster ID and boot address are considered more or less static
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

    wire [63:0]                    boot_addr_i = 64'h40000000;
 
    localparam int unsigned AXI_NUMBYTES = AXI_DATA_WIDTH/8;

    logic        flush_dcache_ack, flush_dcache;
    logic        flush_dcache_q;

    assign o_led = 'h55;

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
        .AXI_ID_WIDTH     ( AXI_ID_WIDTH     ),
        .AXI_USER_WIDTH   ( AXI_USER_WIDTH   )
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

    logic        master0_req,     master1_req,     master2_req;
    logic [63:0] master0_address, master1_address, master2_address;
    logic        master0_we,      master1_we,      master2_we;
    logic [7:0]  master0_be,      master1_be,      master2_be;
    logic [63:0] master0_wdata,   master1_wdata,   master2_wdata;
    logic [63:0] master0_rdata,   master1_rdata,   master2_rdata;

   // sharedmem shared port
   logic [7:0]  sharedmem_en;
   logic [63:0] sharedmem_dout;
   
        // Debug Interface
         logic                           debug_gnt_o;
         logic                           debug_halt;
         logic                           debug_resume;
         logic                           debug_rvalid_o;
         logic [31:0] debug_addr;
         wire  [15:0]                    debug_addr_i = debug_addr[15:0];
         logic                           debug_we_i;
         logic [63:0]                    debug_wdata_i;
         logic [63:0]                    debug_rdata_o;
         logic                           debug_halted_o;
         logic        debug_req, debug_fetch_disable;
         logic        debug_reset;
         logic        debug_runtest;
         logic        debug_clk, debug_blocksel_i;
         logic [1:0]  debug_unused;
         
         logic [63:0] debug_dout;
        // CPU Control Signals
         wire                            debug_halt_i = debug_blocksel_i && debug_halt;
         wire                            debug_resume_i = debug_blocksel_i && debug_resume;
         wire                            fetch_enable_i = ~(debug_blocksel_i && debug_fetch_disable);
         wire                            debug_req_i = debug_blocksel_i && debug_req;


/*
logic [AXI_ADDR_WIDTH-1:0] aw_addr;
logic [2:0]                aw_prot;
logic [3:0]                aw_region;
logic [7:0]                aw_len;
logic [2:0]                aw_size;
logic [1:0]                aw_burst;
logic                      aw_lock;
logic [3:0]                aw_cache;
logic [3:0]                aw_qos;
logic [AXI_ID_WIDTH-1:0]   aw_id;
logic [AXI_USER_WIDTH-1:0] aw_user;
logic                      aw_ready;
logic                      aw_valid;

logic [AXI_ADDR_WIDTH-1:0] ar_addr;
logic [2:0]                ar_prot;
logic [3:0]                ar_region;
logic [7:0]                ar_len;
logic [2:0]                ar_size;
logic [1:0]                ar_burst;
logic                      ar_lock;
logic [3:0]                ar_cache;
logic [3:0]                ar_qos;
logic [AXI_ID_WIDTH-1:0]   ar_id;
logic [AXI_USER_WIDTH-1:0] ar_user;
logic                      ar_ready;
logic                      ar_valid;

logic                      w_valid;
logic [AXI_DATA_WIDTH-1:0] w_data;
logic [AXI_STRB_WIDTH-1:0] w_strb;
logic [AXI_USER_WIDTH-1:0] w_user;
logic                      w_last;
logic                      w_ready;

logic [AXI_DATA_WIDTH-1:0] r_data;
logic [1:0]                r_resp;
logic                      r_last;
logic [AXI_ID_WIDTH-1:0]   r_id;
logic [AXI_USER_WIDTH-1:0] r_user;
logic                      r_ready;
logic                      r_valid;

logic [1:0]                b_resp;
logic [AXI_ID_WIDTH-1:0]   b_id;
logic [AXI_USER_WIDTH-1:0] b_user;
logic                      b_ready;
logic                      b_valid;
*/

    AXI_BUS #(
        .AXI_ADDR_WIDTH ( 64             ),
        .AXI_DATA_WIDTH ( 64             ),
        .AXI_ID_WIDTH   ( AXI_ID_WIDTH   ),
        .AXI_USER_WIDTH ( AXI_USER_WIDTH )
    ) master0_if(), master1_if(), master2_if();

   crossbar_socip cross1(
                          .data_if    ( data_if    ),
                          .bypass_if  ( bypass_if  ),
                          .instr_if   ( instr_if   ),
                          .master0_if ( master0_if ),
                          .master1_if ( master1_if ),
                          .master2_if ( master2_if ),
                          .clk_i      ( clk_i      ),
                          .rst_ni     ( rst_ni     ));
                          
    axi2mem #(
        .AXI_ID_WIDTH   ( AXI_ID_WIDTH      ),
        .AXI_ADDR_WIDTH ( AXI_ADDRESS_WIDTH ),
        .AXI_DATA_WIDTH ( AXI_DATA_WIDTH    ),
        .AXI_USER_WIDTH ( AXI_USER_WIDTH    )
    ) i_master0 (
        .clk_i  ( clk_i           ),
        .rst_ni ( rst_ni          ),
        .slave  ( master0_if      ),
        .req_o  ( master0_req     ),
        .we_o   ( master0_we      ),
        .addr_o ( master0_address ),
        .be_o   ( master0_be      ),
        .data_o ( master0_wdata   ),
        .data_i ( master0_rdata   )
    ), i_master1 (
        .clk_i  ( clk_i           ),
        .rst_ni ( rst_ni          ),
        .slave  ( master1_if      ),
        .req_o  ( master1_req     ),
        .we_o   ( master1_we      ),
        .addr_o ( master1_address ),
        .be_o   ( master1_be      ),
        .data_o ( master1_wdata   ),
        .data_i ( master1_rdata   )
    ), i_master2 (
        .clk_i  ( clk_i           ),
        .rst_ni ( rst_ni          ),
        .slave  ( master2_if      ),
        .req_o  ( master2_req     ),
        .we_o   ( master2_we      ),
        .addr_o ( master2_address ),
        .be_o   ( master2_be      ),
        .data_o ( master2_wdata   ),
        .data_i ( master2_rdata   )
    );

// Boot memory at location 'h40000000
   
infer_ram  #(
        .RAM_SIZE(14),
        .BYTE_WIDTH(8))
        my_master1_ram (
      .ram_clk(clk_i),    // input wire clka
      .ram_en(master1_req),      // input wire ena
      .ram_we(master1_we ? master1_be : 8'b0),   // input wire [7 : 0] wea
      .ram_addr(master1_address[16:3]),  // input wire [13: 0] addra
      .ram_wrdata(master1_wdata),  // input wire [63 : 0] dina
      .ram_rddata(master1_rdata)  // output wire [63 : 0] douta
      );

// Fake version of DDR memory   
infer_ram  #(
        .RAM_SIZE(24),
        .BYTE_WIDTH(8))
        my_master2_ram (
      .ram_clk(clk_i),    // input wire clka
      .ram_en(master2_req),      // input wire ena
      .ram_we(master2_we ? master2_be : 8'b0),   // input wire [7 : 0] wea
      .ram_addr(master2_address[26:3]),  // input wire [8: 0] addra
      .ram_wrdata(master2_wdata),  // input wire [63 : 0] dina
      .ram_rddata(master2_rdata)  // output wire [63 : 0] douta
      );

always @*
        begin      
        sharedmem_en = 8'h0; debug_blocksel_i = 1'b0;
        casez(debug_addr[23:20])
            4'h8: begin sharedmem_en = 8'hff; debug_dout = sharedmem_dout; end
            4'hf: begin debug_blocksel_i = &debug_addr[31:24]; debug_dout = debug_rdata_o; end
            default: debug_dout = 64'hDEADBEEF;
            endcase
        end

jtag_dummy jtag1(
    .DBG({debug_unused[1:0],debug_resume,debug_halt,debug_fetch_disable,debug_req}),
    .WREN(debug_we_i),
    .FROM_MEM(debug_dout),
    .ADDR(debug_addr),
    .TO_MEM(debug_wdata_i),
    .TCK(debug_clk),
    .TCK2(),
    .RESET(debug_reset),
    .RUNTEST(debug_runtest));

   genvar r;

   wire [7:0] m_enb = master0_req ? (master0_we ? master0_be : 8'hFF) : 8'h00;
   wire m_web = master0_req & master0_we;

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
        .DOB    ( master0_rdata[r*8 +: 8]   ),     // Port B 1-bit Data Output
        .DOPB   (                          ),
        .ADDRB  ( master0_address[13:3]     ),     // Port B 14-bit Address Input
        .DIB    ( master0_wdata[r*8 +: 8]   ),     // Port B 1-bit Data Input
        .DIPB   ( 1'b0                     ),
        .ENB    ( m_enb[r]                 ),     // Port B RAM Enable Input
        .SSRB   ( 1'b0                     ),     // Port B Synchronous Set/Reset Input
        .WEB    ( m_web                    )      // Port B Write Enable Input
        );
   endgenerate

endmodule


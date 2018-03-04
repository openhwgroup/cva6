// See LICENSE for license details.

module spi_wrapper
  #(
    parameter ADDR_WIDTH = 8,
    parameter DATA_WIDTH = 8,
    parameter RESET_ADDR = 0
    )
   (
    input                    clk, rstn,
    nasti_channel.slave nasti,
    input                    io0_i,
    output                   io0_o, io0_t,
    input                    io1_i,
    output                   io1_o, io1_t,
    input                    sck_i,
    output                   sck_o, sck_t,
    input                    ss_i,
    output                   ss_o, ss_t,
    output                   ip2intc_irpt,
    output reg               sd_reset
    );

   // internal AXI signals
   logic [ADDR_WIDTH-1:0]   aw_addr,   ar_addr;
   logic                    aw_valid,  ar_valid;
   logic                    aw_ready,  ar_ready;
   logic [DATA_WIDTH-1:0]   w_data,    r_data;
   logic [DATA_WIDTH/8-1:0] w_strb;
   logic                    w_valid;
   logic                    w_ready;
   logic [1:0]              b_resp,    r_resp;
   logic                    b_valid,   r_valid;
   logic                    b_ready,   r_ready;


   // internal control signals
   logic                    write_addr_match, read_addr_match;
   logic                    read_sel, write_sel, write_enable;

   assign read_addr_match = nasti.ar_valid && (nasti.ar_addr & 8'hff) == RESET_ADDR;
   assign write_addr_match = nasti.aw_valid && (nasti.aw_addr & 8'hff) == RESET_ADDR;

   always_ff @(posedge clk or negedge rstn)
     if(!rstn)
       read_sel <= 1'b0;
     else if(read_addr_match)
       read_sel <= 1'b1;
     else if(nasti.r_valid && nasti.r_ready)
       read_sel <= 1'b0;

   always_ff @(posedge clk or negedge rstn)
     if(!rstn)
       write_sel <= 1'b0;
     else if(write_addr_match)
       write_sel <= 1'b1;
     else if(nasti.b_valid && nasti.b_ready)
       write_sel <= 1'b0;

   always_ff @(posedge clk or negedge rstn)
     if(!rstn)
       sd_reset <= 1'b1;
     else if(write_sel && nasti.w_valid && nasti.w_ready)
       sd_reset <= nasti.w_strb & 1'h1 ? nasti.w_data & 8'hff : sd_reset;

   assign ar_addr = nasti.ar_addr;
   assign ar_valid = nasti.ar_valid && !read_addr_match;
   assign nasti.ar_ready = ar_ready || read_addr_match;

   assign aw_addr = nasti.aw_addr;
   assign aw_valid = nasti.aw_valid && !write_addr_match;
   assign nasti.aw_ready = aw_ready || write_addr_match;

   assign w_data = nasti.w_data;
   assign w_strb = nasti.w_strb;
   assign w_valid = nasti.w_valid && !write_sel;
   assign nasti.w_ready = w_ready || write_sel;

   assign nasti.r_data = read_sel ? sd_reset : r_data;
   assign nasti.r_resp = read_sel ? 0 : r_resp;
   assign nasti.r_valid = r_valid || read_sel;
   assign r_ready = read_sel ? 0 : nasti.r_ready;

   assign nasti.b_resp = write_sel ? 0 : b_resp;
   assign nasti.b_valid = b_valid || write_sel;
   assign b_ready = write_sel ? 0 : nasti.b_ready;

   axi_quad_spi_0 spi_i
     (
      .ext_spi_clk     ( clk          ),
      .s_axi_aclk      ( clk          ),
      .s_axi_aresetn   ( rstn         ),
      .s_axi_araddr    ( ar_addr      ),
      .s_axi_arready   ( ar_ready     ),
      .s_axi_arvalid   ( ar_valid     ),
      .s_axi_awaddr    ( aw_addr      ),
      .s_axi_awready   ( aw_ready     ),
      .s_axi_awvalid   ( aw_valid     ),
      .s_axi_bready    ( b_ready      ),
      .s_axi_bresp     ( b_resp       ),
      .s_axi_bvalid    ( b_valid      ),
      .s_axi_rdata     ( r_data       ),
      .s_axi_rready    ( r_ready      ),
      .s_axi_rresp     ( r_resp       ),
      .s_axi_rvalid    ( r_valid      ),
      .s_axi_wdata     ( w_data       ),
      .s_axi_wready    ( w_ready      ),
      .s_axi_wstrb     ( w_strb       ),
      .s_axi_wvalid    ( w_valid      ),
      .io0_i           ( io0_i        ),
      .io0_o           ( io0_o        ),
      .io0_t           ( io0_t        ),
      .io1_i           ( io1_i        ),
      .io1_o           ( io1_o        ),
      .io1_t           ( io1_t        ),
      .sck_i           ( sck_i        ),
      .sck_o           ( sck_o        ),
      .sck_t           ( sck_t        ),
      .ss_i            ( ss_i         ),
      .ss_o            ( ss_o         ),
      .ss_t            ( ss_t         ),
      .ip2intc_irpt    ( ip2intc_irpt )
      );

endmodule // spi_wrapper

// See LICENSE for license details.
`default_nettype none

module framing_top
  (
  input wire          msoc_clk,
  input wire [14:0]   core_lsu_addr,
  input wire [63:0]   core_lsu_wdata,
  input wire [7:0]    core_lsu_be,
  input wire          ce_d,
  input wire          we_d,
  input wire          framing_sel,
  output logic [63:0] framing_rdata,

    // Internal 125 MHz clock
  input               clk_int,
  input               rst_int,
  input               clk90_int,
  input               clk_200_int,

    /*
     * Ethernet: 1000BASE-T RGMII
     */
  input wire          phy_rx_clk,
  input wire [3:0]    phy_rxd,
  input wire          phy_rx_ctl,
  output wire         phy_tx_clk,
  output wire [3:0]   phy_txd,
  output wire         phy_tx_ctl,
  output wire         phy_reset_n,
  input wire          phy_int_n,
  input wire          phy_pme_n,
   
  input wire          phy_mdio_i,
  output reg          phy_mdio_o,
  output reg          phy_mdio_oen,
  output wire         phy_mdc,

  output reg          eth_irq
   );

// obsolete signals to be removedphy_
//    

   
logic [14:0] core_lsu_addr_dly;   

logic tx_enable_i, mac_gmii_tx_en;
logic [47:0] mac_address, rx_dest_mac;
logic [10:0] tx_frame_addr, rx_length_axis[0:7], tx_packet_length;
logic [12:0] axis_tx_frame_size;
logic        ce_d_dly, avail;
logic [63:0] framing_rdata_pkt, framing_wdata_pkt;
logic [3:0] tx_enable_dly, firstbuf, nextbuf, lastbuf;
logic [2:0] last;
   
reg        byte_sync, sync, irq_en, tx_busy, rx_axis_tvalid_old;

   wire [7:0] m_enb = (we_d ? core_lsu_be : 8'hFF);
   logic phy_mdclk, cooked, tx_enable_old, loopback, promiscuous;
   logic [3:0] spare;   
   logic [10:0] rx_addr_axis;
   
       /*
        * AXI input
        */
        reg         tx_axis_tvalid;
        reg         tx_axis_tvalid_dly;
        reg 	    tx_axis_tlast;
        wire [7:0]  tx_axis_tdata;
        wire        tx_axis_tready;
        wire        tx_axis_tuser = 1'b0;
   
       /*
        * AXI output
        */
       wire [7:0] rx_axis_tdata;
       wire       rx_axis_tvalid;
       wire       rx_axis_tlast;
       wire       rx_axis_tuser;
   
      /*
        * AXIS Status
        */
         wire [31:0] tx_fcs_reg_rev, rx_fcs_reg_rev;
   
   always @(posedge clk_int)
     if (rst_int == 1'b1)
       begin
	  byte_sync <= 1'b0;
       end
     else
       begin
	  if (rx_axis_tvalid && (byte_sync == 0) && (nextbuf != (firstbuf+lastbuf)&15) && ~rx_axis_tvalid_old)
            begin
               byte_sync <= 1'b1;
            end
	  if (rx_axis_tlast && byte_sync && ~rx_axis_tvalid_old)
            begin
               last <= 1'b1;
            end
          else if ((last > 0) && (last < 7))
            begin
	       byte_sync <= 1'b0;
               last <= last + 3'b1;
            end
          else
            begin
               last <= 3'b0;
            end
       end

   logic [1:0] rx_wr = rx_axis_tvalid << rx_addr_axis[2];
   logic [15:0] douta;
   assign tx_axis_tdata = douta >> {tx_frame_addr[2],3'b000};
   assign phy_mdc = phy_mdclk;
   
   dualmem_widen8 RAMB16_inst_rx (
                                    .clka(clk_int),              // Port A Clock
                                    .clkb(msoc_clk),              // Port A Clock
                                    .douta(),                     // Port A 8-bit Data Output
                                    .addra({nextbuf[2:0],rx_addr_axis[10:3],rx_addr_axis[1:0]}),    // Port A 11-bit Address Input
                                    .dina({rx_axis_tdata,rx_axis_tdata}), // Port A 8-bit Data Input
                                    .ena(rx_axis_tvalid),         // Port A RAM Enable Input
                                    .wea(rx_wr),                  // Port A Write Enable Input
                                    .doutb(framing_rdata_pkt),    // Port B 32-bit Data Output
                                    .addrb(core_lsu_addr[13:3]),  // Port B 9-bit Address Input
                                    .dinb(core_lsu_wdata),        // Port B 32-bit Data Input
                                    .enb(ce_d & framing_sel & core_lsu_addr[14]),
                                                                  // Port B RAM Enable Input
                                    .web(we_d ? {(|core_lsu_be[7:4]),(|core_lsu_be[3:0])} : 2'b0) // Port B Write Enable Input
                                    );

    dualmem_widen RAMB16_inst_tx (
                                   .clka(~clk_int),             // Port A Clock
                                   .clkb(msoc_clk),              // Port A Clock
                                   .douta(douta),                // Port A 8-bit Data Output
                                   .addra({1'b0,tx_frame_addr[10:3],tx_frame_addr[1:0]}),  // Port A 11-bit Address Input
                                   .dina(16'b0),                 // Port A 8-bit Data Input
                                   .ena(tx_axis_tvalid),         // Port A RAM Enable Input
                                   .wea(2'b0),                  // Port A Write Enable Input
                                   .doutb(framing_wdata_pkt),    // Port B 32-bit Data Output
                                   .addrb(core_lsu_addr[11:3]),  // Port B 9-bit Address Input
                                   .dinb(core_lsu_wdata), // Port B 32-bit Data Input
                                   .enb(ce_d & framing_sel & (core_lsu_addr[14:12]==3'b001)),
				                                 // Port B RAM Enable Input
                                   .web(we_d ? {(|core_lsu_be[7:4]),(|core_lsu_be[3:0])} : 2'b0) // Port B Write Enable Input
                                   );

always @(posedge msoc_clk)
  if (rst_int)
    begin
    core_lsu_addr_dly <= 0;
    mac_address <= 48'H230100890702;
    tx_packet_length <= 0;
    tx_enable_dly <= 0;
    cooked <= 1'b0;
    loopback <= 1'b0;
    spare <= 4'b0;
    promiscuous <= 1'b0;
    phy_mdio_oen <= 1'b0;
    phy_mdio_o <= 1'b0;
    phy_mdclk <= 1'b0;
    sync <= 1'b0;
    firstbuf <= 4'b0;
    lastbuf <= 4'b0;
    nextbuf <= 4'b0;
    eth_irq <= 1'b0;
    irq_en <= 1'b0;
    ce_d_dly <= 1'b0;
    tx_busy <= 1'b0;
    avail = 1'b0;         
    end
  else
    begin
    core_lsu_addr_dly <= core_lsu_addr;
    ce_d_dly <= ce_d;
    avail = nextbuf != firstbuf;
    eth_irq <= avail & irq_en; // make eth_irq go away immediately if irq_en is low
    if (framing_sel&we_d&(&core_lsu_be[3:0])&(core_lsu_addr[14:11]==4'b0001))
      case(core_lsu_addr[6:3])
        0: mac_address[31:0] <= core_lsu_wdata;
        1: {irq_en,promiscuous,spare,loopback,cooked,mac_address[47:32]} <= core_lsu_wdata;
        2: begin tx_enable_dly <= 10; tx_packet_length <= core_lsu_wdata; end /* tx payload size */
        3: begin tx_enable_dly <= 0; tx_packet_length <= 0; end
        4: begin {phy_mdio_oen,phy_mdio_o,phy_mdclk} <= core_lsu_wdata; end
        5: begin lastbuf <= core_lsu_wdata[3:0]; end
        6: begin firstbuf <= core_lsu_wdata[3:0]; end
        default:;
      endcase
       if ((last > 0) && ~sync)
         begin
         // check broadcast/multicast address
	     sync <= (rx_dest_mac[47:24]==24'h01005E) | (&rx_dest_mac) | (mac_address == rx_dest_mac) | promiscuous;
         end
       else if (!last)
         begin
            if (sync) nextbuf <= nextbuf + 1'b1;
            sync <= 1'b0;
         end
       if (mac_gmii_tx_en && tx_axis_tlast)
         begin
            tx_enable_dly <= 0;
         end
       else if (1'b1 == |tx_enable_dly)
         begin
         tx_busy <= 1'b1;
         tx_enable_dly <= tx_enable_dly + 1'b1;
         end
       else if (~mac_gmii_tx_en)
         tx_busy <= 1'b0;         
    end

always @(posedge clk_int)
  if (rst_int)
    begin
       tx_enable_i <= 1'b0;
    end
  else
    begin
       tx_enable_old <= tx_enable_i;
       if (mac_gmii_tx_en && tx_axis_tlast)
         begin
            tx_enable_i <= 1'b0;
         end
       else if (1'b1 == &tx_enable_dly)
         tx_enable_i <= 1'b1;
    end
   
   always @* casez({ce_d_dly,core_lsu_addr_dly[14:3]})
    13'b10001????0000 : framing_rdata = mac_address[31:0];
    13'b10001????0001 : framing_rdata = {irq_en, promiscuous, spare, loopback, cooked, mac_address[47:32]};
    13'b1000?????0010 : framing_rdata = {tx_busy, 4'b0, tx_frame_addr, 5'b0, tx_packet_length};
    13'b10001????0011 : framing_rdata = tx_fcs_reg_rev;
    13'b10001????0100 : framing_rdata = {phy_mdio_i,phy_mdio_oen,phy_mdio_o,phy_mdclk};
    13'b10001????0101 : framing_rdata = rx_fcs_reg_rev;
    13'b10001????0110 : framing_rdata = {eth_irq, avail, lastbuf, nextbuf, firstbuf};
    13'b10001????1??? : framing_rdata = rx_length_axis[core_lsu_addr_dly[5:3]];
    13'b10010???????? : framing_rdata = framing_wdata_pkt;
    13'b11??????????? : framing_rdata = framing_rdata_pkt;
    default: framing_rdata = 'h0;
    endcase

   parameter dly = 0;
   
   reg [31:0] 	    tx_fcs_reg, rx_fcs_reg;
   assign 	    tx_fcs_reg_rev = {tx_fcs_reg[0],tx_fcs_reg[1],tx_fcs_reg[2],tx_fcs_reg[3],
                                          tx_fcs_reg[4],tx_fcs_reg[5],tx_fcs_reg[6],tx_fcs_reg[7],
                                          tx_fcs_reg[8],tx_fcs_reg[9],tx_fcs_reg[10],tx_fcs_reg[11],
                                          tx_fcs_reg[12],tx_fcs_reg[13],tx_fcs_reg[14],tx_fcs_reg[15],
                                          tx_fcs_reg[16],tx_fcs_reg[17],tx_fcs_reg[18],tx_fcs_reg[19],
                                          tx_fcs_reg[20],tx_fcs_reg[21],tx_fcs_reg[22],tx_fcs_reg[23],
                                          tx_fcs_reg[24],tx_fcs_reg[25],tx_fcs_reg[26],tx_fcs_reg[27],
                                          tx_fcs_reg[28],tx_fcs_reg[29],tx_fcs_reg[30],tx_fcs_reg[31]};
   assign 	    rx_fcs_reg_rev = {rx_fcs_reg[0],rx_fcs_reg[1],rx_fcs_reg[2],rx_fcs_reg[3],
                                          rx_fcs_reg[4],rx_fcs_reg[5],rx_fcs_reg[6],rx_fcs_reg[7],
                                          rx_fcs_reg[8],rx_fcs_reg[9],rx_fcs_reg[10],rx_fcs_reg[11],
                                          rx_fcs_reg[12],rx_fcs_reg[13],rx_fcs_reg[14],rx_fcs_reg[15],
                                          rx_fcs_reg[16],rx_fcs_reg[17],rx_fcs_reg[18],rx_fcs_reg[19],
                                          rx_fcs_reg[20],rx_fcs_reg[21],rx_fcs_reg[22],rx_fcs_reg[23],
                                          rx_fcs_reg[24],rx_fcs_reg[25],rx_fcs_reg[26],rx_fcs_reg[27],
                                          rx_fcs_reg[28],rx_fcs_reg[29],rx_fcs_reg[30],rx_fcs_reg[31]};
   wire axis_tx_byte_sent = &axis_tx_frame_size[1:0];
   
   always @(posedge clk_int)
     if (rst_int)
       begin
          rx_addr_axis <= 'b0;
          tx_axis_tvalid <= 'b0;
	  axis_tx_frame_size <= 0;
	  tx_axis_tvalid_dly <= 'b0;
	  tx_frame_addr <= 'b0;
	  tx_axis_tlast <= 'b0;
          rx_dest_mac <= 'b0;
       end
     else
       begin
	  if (tx_enable_i & (tx_enable_old == 0))
	    begin
	       axis_tx_frame_size <= 'b0;
	       tx_frame_addr <= 'b0;
	    end
	  else if (1'b0 == &axis_tx_frame_size)
            begin
               axis_tx_frame_size <= axis_tx_frame_size + 1;
            end
	  if (tx_axis_tready)
	    begin
	       tx_frame_addr <= tx_frame_addr + 1;
	       tx_axis_tlast <= (tx_frame_addr == tx_packet_length-2) & tx_axis_tvalid_dly;
	    end
          if (axis_tx_byte_sent)
	    begin
	       tx_axis_tvalid <= tx_axis_tvalid_dly;
	       if (tx_enable_old)
		 tx_axis_tvalid_dly <= 1'b1;
	       else if (~tx_axis_tlast)
		 tx_axis_tvalid_dly <= 1'b0;
	    end
	  if (rx_axis_tvalid & ~rx_axis_tvalid_old)
            begin
            rx_addr_axis <= rx_addr_axis + 1;
            if (rx_addr_axis < 6)
              rx_dest_mac <= {rx_dest_mac[39:0],rx_axis_tdata};
            end
	  if (rx_axis_tlast & ~rx_axis_tvalid_old)
            begin
	        rx_length_axis[nextbuf[2:0]] <= rx_addr_axis + 1;
	        rx_addr_axis <= 'b0;
            end
          rx_axis_tvalid_old <= rx_axis_tvalid;
      end
 
rgmii_soc rgmii_soc1
  (
   .rst_int(rst_int),
   .clk_int(clk_int),
   .clk90_int(clk90_int),
   .clk_200_int(clk_200_int),
   /*
    * Ethernet: 1000BASE-T RGMII
    */
   .phy_rx_clk(phy_rx_clk),
   .phy_rxd(phy_rxd),
   .phy_rx_ctl(phy_rx_ctl),
   .phy_tx_clk(phy_tx_clk),
   .phy_txd(phy_txd),
   .phy_tx_ctl(phy_tx_ctl),
   .phy_reset_n(phy_reset_n),
   .phy_int_n(phy_int_n),
   .phy_pme_n(phy_pme_n),
   .mac_gmii_tx_en(mac_gmii_tx_en),
   .tx_axis_tdata(tx_axis_tdata),
   .tx_axis_tvalid(tx_axis_tvalid),
   .tx_axis_tready(tx_axis_tready),
   .tx_axis_tlast(tx_axis_tlast),
   .tx_axis_tuser(tx_axis_tuser),
   .rx_axis_tdata(rx_axis_tdata),
   .rx_axis_tvalid(rx_axis_tvalid),
   .rx_axis_tlast(rx_axis_tlast),
   .rx_axis_tuser(rx_axis_tuser)
);

`ifdef XILINX_ILA
   
ila_2 eth_ila_clk_int (
	.clk(clk_int), // input wire clk
	.probe0(tx_axis_tdata), // input wire [7:0]  probe0  
	.probe1(tx_axis_tvalid), // input wire [0:0]  probe1 
	.probe2(tx_axis_tready), // input wire [0:0]  probe2 
	.probe3(tx_axis_tlast), // input wire [0:0]  probe3 
	.probe4(rx_axis_tdata), // input wire [7:0]  probe4 
	.probe5(rx_axis_tvalid), // input wire [0:0]  probe5 
	.probe6(rx_axis_tlast), // input wire [0:0]  probe6 
	.probe7(rx_axis_tuser), // input wire [0:0]  probe7
        .probe8(byte_sync),
        .probe9(last),
        .probe10(rx_addr_axis),
        .probe11(rx_dest_mac),
        .probe12(tx_enable_i),
	.probe13(axis_tx_frame_size),
	.probe14(tx_axis_tvalid_dly),
	.probe15(tx_frame_addr)
);

ila_3 eth_ila_clk_msoc (
	.clk(msoc_clk), // input wire clk
	.probe0(sync),
	.probe1(avail),
        .probe2(nextbuf),
        .probe3(tx_enable_dly),
        .probe4(tx_busy)
);

`endif
   
endmodule // framing_top
`default_nettype wire

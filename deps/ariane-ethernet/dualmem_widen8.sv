
module dualmem_widen8(clka, clkb, dina, dinb, addra, addrb, wea, web, douta, doutb, ena, enb);

   input wire clka, clkb;
   input  [15:0] dina;
   input  [63:0] dinb;
   input  [12:0] addra;
   input  [10:0] addrb;
   input   [1:0]        wea;
   input   [1:0]        web;
   input   [0:0]        ena, enb;
   output [15:0]      douta;
   output [63:0]      doutb;

   genvar r;
   wire [63:0]        dout0;
   wire [255:0]       dout1;
   wire [7:0] 	      we0, we1, en0, en1;
   wire [63:0]        din0;
   wire [255:0]       din1;
   
   reg [12:0]       addra_dly;
   reg [10:0]       addrb_dly;

/*
`ifndef verilator
 `define RAMB16
`endif
*/
   
`ifdef KINTEX7
 `define RAMB16
`endif

`ifdef RAMB16
   
   assign douta = dout0 >> {addra_dly[12:11],4'b0000};
   assign doutb = dout1 >> {addrb_dly[10:9],6'b000000};
   assign we0 = wea << {addra[12:11],1'b0};
   assign we1 = web << {addrb[10:9],1'b0};
   assign en0 = {ena,ena} << {addra[12:11],1'b0};
   assign en1 = {enb,enb} << {addrb[10:9],1'b0};
   assign din0 = {dina,dina,dina,dina};
   assign din1 = {dinb,dinb,dinb,dinb};
   
   always @(posedge clka)
     begin
	addra_dly <= addra;
	addrb_dly <= addrb;
     end
   
   generate for (r = 0; r < 8; r=r+1)
     RAMB16_S9_S36
     RAMB16_S9_S36_inst
       (
        .CLKA   ( clka                     ),     // Port A Clock
        .DOA    ( dout0[r*8 +: 8]          ),     // Port A 1-bit Data Output
        .DOPA   (                          ),
        .ADDRA  ( addra[10:0]              ),     // Port A 14-bit Address Input
        .DIA    ( din0[r*8 +: 8]           ),     // Port A 1-bit Data Input
        .DIPA   ( 1'b0                     ),
        .ENA    ( en0[r]                   ),     // Port A RAM Enable Input
        .SSRA   ( 1'b0                     ),     // Port A Synchronous Set/Reset Input
        .WEA    ( we0[r]                   ),     // Port A Write Enable Input
        .CLKB   ( clkb                     ),     // Port B Clock
        .DOB    ( dout1[r*32 +: 32]        ),     // Port B 1-bit Data Output
        .DOPB   (                          ),
        .ADDRB  ( addrb[8:0]               ),     // Port B 14-bit Address Input
        .DIB    ( din1[r*32 +: 32]         ),     // Port B 1-bit Data Input
        .DIPB   ( 4'b0                     ),
        .ENB    ( en1[r]                   ),     // Port B RAM Enable Input
        .SSRB   ( 1'b0                     ),     // Port B Synchronous Set/Reset Input
        .WEB    ( we1[r]                   )      // Port B Write Enable Input
        );
   endgenerate

`else // !`ifdef RAMB16

// This bit is a placeholder

infer_dpram #(.RAM_SIZE(11), .BYTE_WIDTH(8)) ram1 // RAM_SIZE is in words
(
.ram_clk_a(clka),
.ram_en_a(|ena),
.ram_we_a({wea[1],wea[1],wea[1],wea[1],wea[0],wea[0],wea[0],wea[0]}),
.ram_addr_a(addra),
.ram_wrdata_a({dina,dina,dina,dina}),
.ram_rddata_a({dout,douta}),
.ram_clk_b(clkb),
.ram_en_b(|enb),
.ram_we_b({web[1],web[1],web[1],web[1],web[0],web[0],web[0],web[0]}),
.ram_addr_b({2'b0,addrb}),
.ram_wrdata_b(dinb),
.ram_rddata_b(doutb)
 );
   
`endif
   
endmodule // dualmem

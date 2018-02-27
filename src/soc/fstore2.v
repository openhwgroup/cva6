/*
Copyright 2015-2017 University of Cambridge
Copyright and related rights are licensed under the Solderpad Hardware
License, Version 0.51 (the “License”); you may not use this file except in
compliance with the License. You may obtain a copy of the License at
http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
or agreed to in writing, software, hardware and materials distributed under
this License is distributed on an “AS IS” BASIS, WITHOUT WARRANTIES OR
CONDITIONS OF ANY KIND, either express or implied. See the License for the
specific language governing permissions and limitations under the License.
*/

// A simple monitor (LCD display) driver with glass TTY behaviour in text mode

module fstore2(
               input             pixel2_clk,
               output reg [7:0]  red,
               output reg [7:0]  green,
               output reg [7:0]  blue,

               output [11:0]     DVI_D,
               output            DVI_DE,
               output            DVI_H,
               output            DVI_V,
               output            DVI_XCLK_N,
               output            DVI_XCLK_P,

               output            vsyn,
               output reg        hsyn,
               output reg        blank,

               output wire [7:0] doutb,
               input wire [7:0]  dinb,
               input wire [12:0] addrb,
               input wire        web, enb,
               input wire        clk_data,
               input wire        irst,

               input             GPIO_SW_C,
               input             GPIO_SW_N,
               input             GPIO_SW_S,
               input             GPIO_SW_E,
               input             GPIO_SW_W
               );

   wire                          clear = GPIO_SW_S & GPIO_SW_N; 
   
   parameter rwidth = 14;

   wire                          m0 = 1'b0;
   wire                          dvi_mux;
   assign DVI_XCLK_P = !dvi_mux;  // Chrontel defaults to clock doubling mode
   assign DVI_XCLK_N = dvi_mux;   // where both edges of this mark a 12-bit word.
   //assign DVI_RESET_B = !dvi_reset;

   assign DVI_D[11:8] = (m0 || blank) ? 4'h0 : (dvi_mux) ? red[7:4]: green[3:0];
   assign DVI_D[7:4]  = (m0 || blank) ? 4'h0 : (dvi_mux) ? red[3:0]: blue[7:4];
   assign DVI_D[3:0]  = (m0 || blank) ? 4'h0 : (dvi_mux) ? green[7:4]: blue[3:0];
   assign DVI_H = hsyn;      
   assign DVI_V = vsyn;

   assign DVI_DE = !blank;
   
   reg                           vblank;

   reg                           hstart, hstop, vstart, vstop;
   reg [12:6]                    offhreg,scrollh;
   reg [5:3]                     offpixel;
   reg [11:5]                    offvreg,scrollv;
   reg [4:1]                     vrow;
   reg [4:0]                     scroll;
   
   wire [7:0]                    dout;
   wire [12:0]                   addra = {offvreg[10:5],offhreg[12:6]};
   
   // 100 MHz / 2100 is 47.6kHz.  Divide by further 788 to get 60.4 Hz.
   // Aim for 1024x768 non interlaced at 60 Hz.  
   
   reg [11:0]                    hreg, vreg;

   reg                           bitmapped_pixel;
   
   wire [7:0]                    red_in, green_in, blue_in;
   assign dvi_mux = hreg[0];

   dualmem ram1(.clka(pixel2_clk),
                .dina(addra[7:0]), .addra(addra), .wea(clear), .douta(dout), .ena(1'b1),
                .clkb(clk_data), .dinb(dinb), .addrb(addrb), .web(web), .doutb(doutb), .enb(enb));
   
   always @(posedge pixel2_clk) // or posedge reset) // JRRK - does this need async ?
   if (irst)
     begin
        hreg <= 0;
        hstart <= 0;
        hsyn <= 0;
        hstop <= 0;
        vreg <= 0;
        vstart <= 0;
        vstop <= 0;
        vblank <= 0;
        red <= 0;
        green <= 0;
        blue <= 0;
        bitmapped_pixel <= 0;
        blank <= 0;
        offhreg <= 0;
        offvreg <= 0;
        offpixel <= 0;
        vrow <= 0;
        scroll <= 0;
        scrollh <= 0;
        scrollv <= 0;
     end
   else
     begin
        hreg <= (hstop) ? 0: hreg + 1;
        hstart <= hreg == 2048;      
        if (hstart) hsyn <= 1; else if (hreg == (2048+20)) hsyn <= 0;
        hstop <= hreg == (2100-1);
        if (hstop) begin
           if (vstop)
             begin
                vreg <= 0;
                scroll <= {GPIO_SW_N,GPIO_SW_S,GPIO_SW_E,GPIO_SW_W,GPIO_SW_C};
                if ((scrollv>0) && GPIO_SW_N & ~scroll[4]) scrollv <= scrollv - 4;
                if ((scrollv<32) && GPIO_SW_S & ~scroll[3]) scrollv <= scrollv + 4;
                if ((scrollh<96) && GPIO_SW_E & ~scroll[2]) scrollh <= scrollh + 4;
                if ((scrollh>0) && GPIO_SW_W & ~scroll[1]) scrollh <= scrollh - 4;
                if (GPIO_SW_C & ~scroll[0]) begin scrollh <= 0; scrollv <= 0; end
             end
           else
             vreg <= vreg + 1;
           vstart <= vreg == 768;
           vstop <= vreg == 768+19;
        end

        vblank <= vreg < 10 || vreg >= 768+10; 
        
        if (dvi_mux) begin
           red <= red_in;         
           blue <= blue_in;
           green <= green_in;
        end

        if (vreg >= 32 && vreg < 32+768)
          begin
             if (hreg >= 128*3 && hreg < (128*3+256*6))
               begin
                  if (&hreg[1:0])
                    begin
                       if (offpixel == 5)
                         begin
                            offpixel <= 0;
                            offhreg <= offhreg+1;
                         end
                       else
                         offpixel <= offpixel+1;
                    end
                  bitmapped_pixel <= 1;
               end
             else
               begin
                  offpixel <= 0;
                  offhreg <= scrollh;
                  if (hstop & vreg[0])
                    begin
                       if (vrow == 11)
                         begin
                            vrow <= 0;
                            offvreg <= offvreg+1;
                         end
                       else
                         begin
                            vrow <= vrow + 1;
                         end
                    end
                  bitmapped_pixel <= 0;
               end
          end
        else
          begin
             vrow <= 0;
             offvreg <= scrollv;
             bitmapped_pixel <= 0;
          end
        
        
        blank<= hsyn | vsyn | vblank;
        
     end

   assign vsyn = vstart;
   
   wire [7:0] pixels_out;
   RAMB16_S9 #(
               // The following INIT_xx declarations specify the initial contents of the character generator RAM
               .INIT_00(256'h000000003E3E3E3E3E3E3E3E3E3E3E3E000000003E3E3E3E3E3E3E3E3E3E3E3E),
               .INIT_01(256'h000000003E3E3E3E3E3E3E3E3E3E3E3E000000003E3E3E3E3E3E3E3E3E3E3E3E),
               .INIT_02(256'h000000003E3E3E3E3E3E3E3E3E3E3E3E000000003E3E3E3E3E3E3E3E3E3E3E3E),
               .INIT_03(256'h000000003E3E3E3E3E3E3E3E3E3E3E3E000000003E3E3E3E3E3E3E3E3E3E3E3E),
               .INIT_04(256'h000000003E3E3E3E3E3E3E3E3E3E3E3E000000003E3E3E3E3E3E3E3E3E3E3E3E),
               .INIT_05(256'h000000003E3E3E3E3E3E3E3E3E3E3E3E000000003E3E3E3E3E3E3E3E3E3E3E3E),
               .INIT_06(256'h000000003E3E3E3E3E3E3E3E3E3E3E3E000000003E3E3E3E3E3E3E3E3E3E3E3E),
               .INIT_07(256'h000000003E3E3E3E3E3E3E3E3E3E3E3E000000003E3E3E3E3E3E3E3E3E3E3E3E),
               .INIT_08(256'h000000003E3E3E3E3E3E3E3E3E3E3E3E000000003E3E3E3E3E3E3E3E3E3E3E3E),
               .INIT_09(256'h000000003E3E3E3E3E3E3E3E3E3E3E3E000000003E3E3E3E3E3E3E3E3E3E3E3E),
               .INIT_0A(256'h000000003E3E3E3E3E3E3E3E3E3E3E3E000000003E3E3E3E3E3E3E3E3E3E3E3E),
               .INIT_0B(256'h000000003E3E3E3E3E3E3E3E3E3E3E3E000000003E3E3E3E3E3E3E3E3E3E3E3E),
               .INIT_0C(256'h000000003E3E3E3E3E3E3E3E3E3E3E3E000000003E3E3E3E3E3E3E3E3E3E3E3E),
               .INIT_0D(256'h000000003E3E3E3E3E3E3E3E3E3E3E3E000000003E3E3E3E3E3E3E3E3E3E3E3E),
               .INIT_0E(256'h000000003E3E3E3E3E3E3E3E3E3E3E3E000000003E3E3E3E3E3E3E3E3E3E3E3E),
               .INIT_0F(256'h000000003E3E3E3E3E3E3E3E3E3E3E3E000000003E3E3E3E3E3E3E3E3E3E3E3E),
               .INIT_10(256'h0000000000000000001000101010101000000000000000000000000000000000),
               .INIT_11(256'h00000000000000000028287C287C282800000000000000000000000000002828),
               .INIT_12(256'h000000000000000000044A241008245200000000000000001078141C70503C10),
               .INIT_13(256'h0000000000000000000000000020181800000000000000000034485420504830),
               .INIT_14(256'h0000000000000000002010080808102000000000000000000008102020201008),
               .INIT_15(256'h00000000000000000010107C101000000000000000000000001054387C385410),
               .INIT_16(256'h00000000000000000000007C0000000000000000000000002018180000000000),
               .INIT_17(256'h0000000000000000004040201008040400000000000000001818000000000000),
               .INIT_18(256'h00000000000000000038101010103010000000000000000000384464544C4438),
               .INIT_19(256'h000000000000000000384404180444380000000000000000007C201008044438),
               .INIT_1A(256'h0000000000000000003844044478407C00000000000000000008087C48281808),
               .INIT_1B(256'h0000000000000000002020201008447C00000000000000000038444478402018),
               .INIT_1C(256'h0000000000000000003008043C44443800000000000000000038444438444438),
               .INIT_1D(256'h0000000000000000201818001818000000000000000000000018180018180000),
               .INIT_1E(256'h000000000000000000007C007C00000000000000000000000008102010080000),
               .INIT_1F(256'h0000000000000000002000203008483000000000000000000020100810200000),
               .INIT_20(256'h0000000000000000004444447C4428100000000000000000001C204C544E221C),
               .INIT_21(256'h0000000000000000003844404040443800000000000000000078242438242478),
               .INIT_22(256'h0000000000000000007C40407840407C00000000000000000078242424242478),
               .INIT_23(256'h0000000000000000003844445C4044380000000000000000004040407840407C),
               .INIT_24(256'h000000000000000000381010101010380000000000000000004444447C444444),
               .INIT_25(256'h000000000000000000444850605048440000000000000000003048080808081C),
               .INIT_26(256'h00000000000000000044444454546C440000000000000000007C404040404040),
               .INIT_27(256'h0000000000000000001028444444281000000000000000000044444C54644444),
               .INIT_28(256'h0000000000000000003C4C444444443800000000000000000040404078444478),
               .INIT_29(256'h0000000000000000003844043840443800000000000000000044485078444478),
               .INIT_2A(256'h000000000000000000384444444444440000000000000000001010101010107C),
               .INIT_2B(256'h000000000000000000446C545444444400000000000000000010102828444444),
               .INIT_2C(256'h0000000000000000001010101028444400000000000000000044442810284444),
               .INIT_2D(256'h000000000000000000382020202020380000000000000000007C40201008047C),
               .INIT_2E(256'h0000000000000000001C04040404041C00000000000000000000040810204000),
               .INIT_2F(256'h0000000000000000FFFF00000000000000000000000000000010101010543810),
               .INIT_30(256'h000000000000003A443C04083000000000000000000000000000000810200000),
               .INIT_31(256'h0000000000000038444044380000000000000000000000986444645840400000),
               .INIT_32(256'h0000000000000038407844380000000000000000000000324C444C3404040000),
               .INIT_33(256'h00000000384404344C4444380000000000000000000000202020207024180000),
               .INIT_34(256'h0000000000000038101010300010000000000000000000444444645840400000),
               .INIT_35(256'h0000000000000044487048444040000000000000003048080808081800080000),
               .INIT_36(256'h0000000000000054545454380000000000000000000000381010101010300000),
               .INIT_37(256'h0000000000000038444444380000000000000000000000444444645800000000),
               .INIT_38(256'h00000000040604344C444C340000000000000000404040586444649800000000),
               .INIT_39(256'h0000000000000038043840380000000000000000000000404040645800000000),
               .INIT_3A(256'h00000000000000344C44444400000000000000000000000C1210103810100000),
               .INIT_3B(256'h0000000000000038545454440000000000000000000000102844444400000000),
               .INIT_3C(256'h0000000038440434444444440000000000000000000000442810284400000000),
               .INIT_3D(256'h000000000000000C10106010100C0000000000000000007C2010087C00000000),
               .INIT_3E(256'h000000000000006010100C101060000000000000000000101010001010100000),
               .INIT_3F(256'h00000000000000007C7C7C7C000000000000000000000000000002027E000000)
               ) RAMB16_S1_inst_0 (
                                   .CLK(pixel2_clk),      // Port A Clock
                                   .DO(pixels_out), // Port A 8-bit Data Output
                                   .ADDR({dout[6:0],vrow}),    // Port A 11-bit Address Input
                                   .DI(8'b0),  // Port A 8-bit Data Input
                                   .EN(1'b1),        // Port A RAM Enable Input
                                   .SSR(1'b0),      // Port A Synchronous Set/Reset Input
                                   .WE(1'b0),        // Port A Write Enable Input
                                   .DIP(1'b0),
                                   .DOP()
                                   );
   
   wire       pixel = pixels_out[3'd7 ^ offpixel] && bitmapped_pixel;

   assign red_in = (pixel ? 8'hff: 8'h00);
   assign green_in = (pixel ? 8'hff: 8'h00);
   assign blue_in   = 8'b0;
   
endmodule

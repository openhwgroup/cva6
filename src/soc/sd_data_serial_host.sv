//////////////////////////////////////////////////////////////////////
////                                                              ////
//// WISHBONE SD Card Controller IP Core                          ////
////                                                              ////
//// sd_data_serial_host.v                                        ////
////                                                              ////
//// This file is part of the WISHBONE SD Card                    ////
//// Controller IP Core project                                   ////
//// http://opencores.org/project,sd_card_controller              ////
////                                                              ////
//// Description                                                  ////
//// Module resposible for sending and receiving data through     ////
//// 4-bit sd card data interface                                 ////
////                                                              ////
//// Author(s):                                                   ////
////     - Marek Czerski, ma.czerski@gmail.com                    ////
////                                                              ////
//////////////////////////////////////////////////////////////////////
////                                                              ////
//// Copyright (C) 2013 Authors                                   ////
////                                                              ////
//// Based on original work by                                    ////
////     Adam Edvardsson (adam.edvardsson@orsoc.se)               ////
////                                                              ////
////     Copyright (C) 2009 Authors                               ////
////                                                              ////
//// This source file may be used and distributed without         ////
//// restriction provided that this copyright statement is not    ////
//// removed from the file and that any derivative work contains  ////
//// the original copyright notice and the associated disclaimer. ////
////                                                              ////
//// This source file is free software; you can redistribute it   ////
//// and/or modify it under the terms of the GNU Lesser General   ////
//// Public License as published by the Free Software Foundation; ////
//// either version 2.1 of the License, or (at your option) any   ////
//// later version.                                               ////
////                                                              ////
//// This source is distributed in the hope that it will be       ////
//// useful, but WITHOUT ANY WARRANTY; without even the implied   ////
//// warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR      ////
//// PURPOSE. See the GNU Lesser General Public License for more  ////
//// details.                                                     ////
////                                                              ////
//// You should have received a copy of the GNU Lesser General    ////
//// Public License along with this source; if not, download it   ////
//// from http://www.opencores.org/lgpl.shtml                     ////
////                                                              ////
//////////////////////////////////////////////////////////////////////
`include "sd_defines.h"

module sd_data_serial_host(
           input 			 sd_clk,
           input 			 rst,
           //Tx Fifo
           input [31:0] 		 data_in,
           output reg 			 rd,
           //Rx Fifo
           output reg [31:0] 		 data_out,
           output reg 			 we,
           //tristate data
           output reg 			 DAT_oe_o,
           output reg [3:0] 		 DAT_dat_o,
           input [3:0] 			 DAT_dat_i,
           //Control signals
           input [`BLKSIZE_W-1:0] 	 blksize,
           input 			 bus_4bit,
           input [`BLKCNT_W-1:0] 	 blkcnt,
           input [1:0] 			 start,
           input [1:0] 			 byte_alignment,
	   input [31:0] 		 timeout_i,
           output 			 sd_data_busy,
           output 			 busy,
           output			 crc_ok,
           output reg 			 finish_o,
	   output reg [31:0] 		 wait_reg_o,
	   output reg [`BLKSIZE_W-1+4:0] transf_cnt_o
       );

reg [4:0] crc_s;
reg [3:0] crc_lane_ok;
reg [15:0]         crc_din[3:0];
wire [15:0]        crc_calc[3:0];
reg [31:0]                                        data_out0;
reg                                               we0;
reg [3:0] DAT_dat_reg;
reg [`BLKSIZE_W-1+4:0] data_cycles;
reg bus_4bit_reg;
//CRC16
   reg [4:0]                                         crc_in;
reg crc_rst;
parameter SIZE = 7;
reg [SIZE-1:0] state;
reg [SIZE-1:0] next_state;
parameter IDLE       = 7'b0000001;
parameter WRITE_DAT  = 7'b0000010;
parameter WRITE_CRC  = 7'b0000100;
parameter WRITE_BUSY = 7'b0001000;
parameter READ_WAIT  = 7'b0010000;
parameter READ_DAT   = 7'b0100000;
parameter FINISH     = 7'b1000000;
reg [2:0] crc_status;
reg busy_int;
reg [`BLKSIZE_W-1:0] blksize_reg;
reg [4:0] crc_c;
   reg [3:0]                                         crnt_din;
reg [4:0] data_index;

   integer                                           k;
genvar i;
generate
    for(i=0; i<4; i=i+1) begin: CRC_16_gen
         sd_crc_16 CRC_16_i (crc_in[i], crc_in[4], ~sd_clk, crc_rst, crc_calc[i]);
    end
endgenerate

assign busy = (state != IDLE) && (state != FINISH);
assign sd_data_busy = !DAT_dat_reg[0];
assign crc_ok = &crc_lane_ok;

always @(posedge sd_clk or posedge rst)
begin: FSM_OUT
    if (rst) begin
        state <= IDLE;
        DAT_oe_o <= 0;
        crc_in <= 0;
        crc_rst <= 1;
        transf_cnt_o <= 0;
        crc_c <= 15;
        rd <= 0;
        crc_c <= 0;
        DAT_dat_o <= 0;
        crc_status <= 0;
        crc_lane_ok <= 0;
        crc_s <= 0;
        we0 <= 0;
        we <= 0;
        data_out0 <= 0;
        busy_int <= 0;
        data_index <= 0;
        data_cycles <= 0;
        bus_4bit_reg <= 0;     
        wait_reg_o <= 0;
        finish_o <= 0;
           DAT_dat_reg <= 0;
           data_out <= 0;
           transf_cnt_o <= 0;
    end
    else begin
           // sd data input pad register
           DAT_dat_reg <= DAT_dat_i;
           crnt_din = 4'hf;
           if (we0) data_out <= data_out0;
           we <= we0;
        case(state)
            IDLE: begin
                for (k = 0; k < 4; k=k+1)
                  crc_din[k] <= 0;
                DAT_oe_o <= 0;
                DAT_dat_o <= 4'b1111;
                crc_in <= 0;
                crc_rst <= 1;
                transf_cnt_o <= 0;
                crc_c <= 16;
                crc_status <= 0;
                crc_lane_ok <= 0;
                crc_s <= 0;
                we0 <= 0;
                rd <= 0;
                data_index <= 0;
                blksize_reg <= blksize;
                data_cycles <= (bus_4bit ? {2'b0,blksize,1'b0} + 'd2 : {blksize,3'b0} + 'd8);
                bus_4bit_reg <= bus_4bit;
	        wait_reg_o <= 0;
	        finish_o <= 0;
                data_out <= 0;
                if (start == 2'b01)
                  state <= WRITE_DAT;
                else if (start == 2'b10)
                  state <= READ_WAIT;
            end
            WRITE_DAT: begin
                transf_cnt_o <= transf_cnt_o + 16'h1;
                rd <= 0;
                //special case
                if (transf_cnt_o == 0) begin
                    crc_rst <= 0;
                   data_index <= 0;
                   crnt_din = bus_4bit_reg ? 4'h0 : 4'he;
                   rd <= 1;
                    DAT_oe_o <= 1;
                   DAT_dat_o <= crnt_din;
                end
                else if (transf_cnt_o < data_cycles+16) begin /* send the write data */
                    if (bus_4bit_reg) begin
                      crnt_din = {
                            data_in[31-({data_index[2:0],2'b00})], 
                            data_in[30-({data_index[2:0],2'b00})], 
                            data_in[29-({data_index[2:0],2'b00})], 
                            data_in[28-({data_index[2:0],2'b00})]
                            };
                      if (data_index[2:0] == 3'h7 && transf_cnt_o < data_cycles-2) begin
                         begin
                            rd <= 1;
                         end
                        end
                    end
                    else begin
                      crnt_din = {3'h7, data_in[31-data_index]};
                        if (data_index == 29/*not 31 - read delay !!!*/) begin
                         begin
                            rd <= 1;
                         end
                        end
                    end
                    data_index <= data_index + 5'h1;
                   if (transf_cnt_o < data_cycles-1)
                     begin
                        crc_in <= {1'b1,crnt_din};
                        DAT_dat_o <= crnt_din;
                end
                   else if (crc_c!=0) begin /* send the CRC */
                      crc_in <= 0;
                    crc_c <= crc_c - 5'h1;
                    DAT_oe_o <= 1;
                      DAT_dat_o[0] <= crc_calc[0][crc_c-1];
                    if (bus_4bit_reg)
                        DAT_dat_o[3:1] <= {crc_calc[3][crc_c-1], crc_calc[2][crc_c-1], crc_calc[1][crc_c-1]};
                    else
                        DAT_dat_o[3:1] <= {3'h7};
                end
                   else /* send the stop bit */
                     begin
                        crc_in <= 0;
                    DAT_oe_o <= 1;
                    DAT_dat_o <= 4'hf;
                end
                end
                else begin /* wait for write ack */
                    DAT_oe_o <= 0;
                    crc_s[4] <= DAT_dat_reg[0];
                    if (!DAT_dat_reg[0])
                        state <= WRITE_CRC;
                end
            end
             WRITE_CRC: begin /* get write ack */
                DAT_oe_o <= 0;
                crc_status <= crc_status + 3'h1;
                crc_s[3-crc_status[1:0]] <= DAT_dat_reg[0];                
                busy_int <= 1;
                if (crc_status == 3)
                  state <= WRITE_BUSY;
            end
             WRITE_BUSY: begin /* wait for write completion */
                busy_int <= !DAT_dat_reg[0];
                if (!busy_int)
                  state <= FINISH;
                end
             READ_WAIT: begin /* wait for a start bit in read mode */
                DAT_oe_o <= 0;
                crc_rst <= 0;
                crc_in <= 0;
                crc_c <= 15;// end
                transf_cnt_o <= 0;
                data_index <= 0;
	        wait_reg_o <= wait_reg_o + 1;
                if ((wait_reg_o >= 3) && !DAT_dat_reg[0]) begin // allow time for bus to change direction
                   state <= READ_DAT;
            end
                else if (wait_reg_o >= timeout_i) begin // prevent hang if card did not respond
                   state <= FINISH;
                end
             end
             READ_DAT: begin /* read the data and calculate CRC */
                we0 <= 0;
                if (transf_cnt_o < data_cycles-2) begin
                    if (bus_4bit_reg) begin
                      if (&data_index[2:0])
                        begin
                           we0 <= 1;
                        end;
                        data_out0[31-({data_index[2:0],2'b00})] <= DAT_dat_reg[3];
                        data_out0[30-({data_index[2:0],2'b00})] <= DAT_dat_reg[2];
                        data_out0[29-({data_index[2:0],2'b00})] <= DAT_dat_reg[1];
                        data_out0[28-({data_index[2:0],2'b00})] <= DAT_dat_reg[0];
                    end
                    else begin
                      if (&data_index)
                        begin
                           we0 <= 1;
                        end;
                        data_out0[31-data_index] <= DAT_dat_reg[0];
                    end
                    data_index <= data_index + 5'h1;
                   crc_in <= {1'b1,DAT_dat_reg};
                   transf_cnt_o <= transf_cnt_o + 16'h1;
                end
                else if (crc_c != 5'h1f) begin
                   for (k = 0; k < 4; k=k+1)
                     begin
                        crc_din[k][crc_c[3:0]] <= DAT_dat_reg[k];
                     end
                   transf_cnt_o <= transf_cnt_o + 16'h1;
                   crc_in <= 0;
                    we0 <=0;
                        crc_c <= crc_c - 5'h1;
                        end
                else
                  begin
                     for (k = 0; k < 4; k=k+1)
                       crc_lane_ok[k] <= crc_calc[k] == crc_din[k];
                     state <= FINISH;
                end
            end // case: READ_DAT
	  FINISH:
               begin
	    finish_o <= 1;
                  if (start == 2'b00)
                    state <= IDLE;
               end
             default:
               state <= IDLE;          
           endcase; // case (state)
           //abort
           if (start == 2'b11)
             state <= IDLE;       
    end
end

endmodule






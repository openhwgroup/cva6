//////////////////////////////////////////////////////////////////////
////                                                              ////
//// WISHBONE SD Card Controller IP Core                          ////
////                                                              ////
//// sd_cmd_serial_host.v                                         ////
////                                                              ////
//// This file is part of the WISHBONE SD Card                    ////
//// Controller IP Core project                                   ////
//// http://opencores.org/project,sd_card_controller              ////
////                                                              ////
//// Description                                                  ////
//// Module resposible for sending and receiving commands         ////
//// through 1-bit sd card command interface                      ////
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

module sd_cmd_serial_host (
           sd_clk,
           rst,
           setting_i,
           cmd_i,
           start_i,
	   timeout_i,
           response_o,
           crc_ok_o,
           index_ok_o,
           finish_o,
	   wait_reg_o,
	   crc_val_o,
	   packet_o,
	   start_data_o,
           cmd_dat_i,
           cmd_out_o,
           cmd_oe_o
       );

//-------------Internal Constant-------------
parameter INIT_DELAY = 74;
parameter BITS_TO_SEND = 48;
parameter CMD_SIZE = 40;
parameter RESP_SIZE_LONG = 127;
parameter RESP_SIZE_SHORT = 39;
//---------------Input ports---------------
input wire sd_clk;
input wire rst;
input [2:0] setting_i;
input [37:0] cmd_i;
input wire start_i;
input wire cmd_dat_i;
input [31:0] timeout_i;   
//---------------Output ports---------------
output reg [BITS_TO_SEND-1:0] packet_o;
output reg [RESP_SIZE_LONG+6:0] response_o;
output reg finish_o;
output reg crc_ok_o;
output reg index_ok_o;
output reg cmd_oe_o;
output reg cmd_out_o;
output reg start_data_o;
output wire [6:0] crc_val_o;
output reg [31:0] wait_reg_o;
//---------------Internal variable-----------
   reg [CMD_SIZE-1:0]  cmd_buff;
   reg 		       cmd_dat_reg;
   reg [7:0] 	       resp_len;
   reg 		       with_response, with_data;
   
//CRC
reg crc_rst;
reg crc_enable;
reg crc_bit;
//-Internal Counterns
reg [7:0] counter;
//-State Machine
parameter STATE_SIZE = 6;
parameter
    INIT = 6'h00,
    IDLE = 6'h01,
    SETUP_CRC = 6'h02,
    WRITE = 6'h04,
    READ_WAIT = 6'h08,
    READ = 6'h10,
    FINISH_RD_WR = 6'h20;
reg [STATE_SIZE-1:0] state;
reg [STATE_SIZE-1:0] next_state;

//------------------------------------------
sd_crc_7 CRC_7(
             crc_bit,
             crc_enable,
             sd_clk,
             crc_rst,
             crc_val_o);

//------------------------------------------
always @(state or counter or start_i or with_response or cmd_dat_reg or resp_len or timeout_i or wait_reg_o)
begin: FSM_COMBO
    case(state)
        INIT: begin
            if (counter >= INIT_DELAY) begin
                next_state = IDLE;
            end
            else begin
                next_state = INIT;
            end
        end
        IDLE: begin
            if (start_i) begin
                next_state = SETUP_CRC;
            end
            else begin
                next_state = IDLE;
            end
        end
        SETUP_CRC:
            next_state = WRITE;
        WRITE:
            if (counter >= BITS_TO_SEND && with_response) begin
                next_state = READ_WAIT;
            end
            else if (counter >= BITS_TO_SEND) begin
                next_state = FINISH_RD_WR;
            end
            else begin
                next_state = WRITE;
            end
        READ_WAIT:
            if ((wait_reg_o >= 3) && !cmd_dat_reg) begin // allow time for bus to change direction
                next_state = READ;
            end
            else if (wait_reg_o >= timeout_i) begin // prevent hang if card did not respond
                next_state = FINISH_RD_WR;
            end
            else begin
                next_state = READ_WAIT;
            end
        READ:
            if (counter >= resp_len+8) begin
                next_state = FINISH_RD_WR;
            end
            else begin
               next_state = READ;
            end
        FINISH_RD_WR:
	    if (start_i)
              next_state = FINISH_RD_WR;
            else
              next_state = IDLE;
        default: 
            next_state = INIT;
    endcase
end

always @(posedge sd_clk or posedge rst)
begin: COMMAND_DECODER
    if (rst) begin
        resp_len <= 0;
        with_response <= 0;
        with_data <= 0;
        cmd_buff <= 0;
    end
    else begin
        if (start_i == 1) begin
            resp_len <= setting_i[1] ? RESP_SIZE_LONG : RESP_SIZE_SHORT;
            with_response <= setting_i[0];
            with_data <= setting_i[2];
            cmd_buff <= {2'b01,cmd_i};
        end
    end
end

//----------------Seq logic------------
always @(posedge sd_clk or posedge rst)
begin: FSM_SEQ
    if (rst) begin
        state <= INIT;
    end
    else begin
        state <= next_state;
    end
end

//-------------OUTPUT_LOGIC-------
always @(posedge sd_clk or posedge rst)
begin: FSM_OUT
    if (rst) begin
       crc_enable <= 0;
       cmd_oe_o = 1;
       cmd_out_o = 1;
       response_o <= 0;
       finish_o <= 0;
       crc_rst <= 1;
       crc_bit <= 0;
       index_ok_o <= 0;
       crc_ok_o <= 0;
       counter <= 0;
       cmd_dat_reg <= 0;
       packet_o <= 0;
       start_data_o <= 0;
       wait_reg_o <= 0;
    end
    else begin
       case(state)
            INIT: begin
               counter <= counter+1;
               cmd_oe_o = 1;
               cmd_out_o = 1;
            end
            IDLE: begin
               cmd_oe_o = 0;      //Put CMD to Z
               counter <= 0;
               crc_rst <= 1;
               crc_enable <= 0;
               index_ok_o <= 0;
               finish_o <= 0;
	       start_data_o <= 0;
            end
            SETUP_CRC: begin
               crc_rst <= 0;
               crc_enable <= 1;
	       response_o <= 0;
	       packet_o <= 0;
               crc_bit <= cmd_buff[CMD_SIZE-1];
            end
            WRITE: begin
	       cmd_dat_reg <= 1'b1;
               if (counter < BITS_TO_SEND-8) begin  // 1->40 CMD, (41 >= CNT && CNT <=47) CRC, 48 stop_bit
                  cmd_oe_o = 1;
                  cmd_out_o = cmd_buff[CMD_SIZE-1-counter];
                  if (counter < BITS_TO_SEND-9) begin //1 step ahead
                     crc_bit <= cmd_buff[CMD_SIZE-2-counter];
                  end else begin
                     crc_enable <= 0;
                  end
               end
               else if (counter < BITS_TO_SEND-1) begin
                  cmd_oe_o = 1;
                  crc_enable <= 0;
                  cmd_out_o = crc_val_o[BITS_TO_SEND-counter-2];
               end
               else if (counter == BITS_TO_SEND-1) begin
                  cmd_oe_o = 1;
                  cmd_out_o = 1'b1;
               end
               else begin
                  cmd_oe_o = 0;
                  cmd_out_o = 1'b1;
               end
               counter <= counter+1;
	       wait_reg_o <= 0;
	       if (cmd_oe_o) packet_o <= {packet_o[BITS_TO_SEND-2:0],cmd_out_o};
            end
            READ_WAIT: begin
	       cmd_dat_reg <= cmd_dat_i;
               crc_enable <= 0;
               crc_rst <= 1;
               counter <= 1;
               cmd_oe_o = 0;
               wait_reg_o <= wait_reg_o + 1;
            end
            READ: begin
	       cmd_dat_reg <= cmd_dat_i;
               crc_rst <= 0;
               crc_enable <= (resp_len != RESP_SIZE_LONG || counter > 7);
               cmd_oe_o = 0;
               if (counter <= resp_len)
                 crc_bit <= cmd_dat_reg;
	       else
		 begin
                    crc_enable <= 0;
		 end
               if (counter <= resp_len+7) begin
                  response_o <= {response_o[RESP_SIZE_LONG+5:0],cmd_dat_reg};
               end
               else begin
                  crc_enable <= 0;
                  crc_ok_o <= (response_o[6:0] == crc_val_o);
                   start_data_o <= with_data;
               end
               counter <= counter + 1;
            end
            FINISH_RD_WR: begin
                index_ok_o <= (cmd_buff[37:32] == response_o[125:120]);
                finish_o <= 1;
                crc_enable <= 0;
                counter <= 0;
                cmd_oe_o = 0;
            end // case: FINISH_RD_WR
	  default:;
        endcase
    end
end

endmodule



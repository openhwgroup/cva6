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
           response_o,
           crc_ok_o,
           index_ok_o,
           finish_o,
           cmd_dat_i,
           cmd_out_o,
           cmd_oe_o
       );

//---------------Input ports---------------
input sd_clk;
input rst;
input [1:0] setting_i;
input [39:0] cmd_i;
input start_i;
input cmd_dat_i;
//---------------Output ports---------------
output reg [119:0] response_o;
output reg finish_o;
output reg crc_ok_o;
output reg index_ok_o;
output reg cmd_oe_o;
output reg cmd_out_o;

//-------------Internal Constant-------------
parameter INIT_DELAY = 4;
parameter BITS_TO_SEND = 48;
parameter CMD_SIZE = 40;
parameter RESP_SIZE = 128;

//---------------Internal variable-----------
reg cmd_dat_reg;
integer resp_len;
reg with_response;
reg [CMD_SIZE-1:0] cmd_buff;
reg [RESP_SIZE-1:0] resp_buff;
integer resp_idx;
//CRC
reg crc_rst;
reg [6:0]crc_in;
wire [6:0] crc_val;
reg crc_enable;
reg crc_bit;
reg crc_ok;
//-Internal Counterns
integer counter;
//-State Machine
parameter STATE_SIZE = 10;
parameter
    INIT = 7'h00,
    IDLE = 7'h01,
    SETUP_CRC = 7'h02,
    WRITE = 7'h04,
    READ_WAIT = 7'h08,
    READ = 7'h10,
    FINISH_WR = 7'h20,
    FINISH_WO = 7'h40;
reg [STATE_SIZE-1:0] state;
reg [STATE_SIZE-1:0] next_state;
//Misc
`define cmd_idx  (CMD_SIZE-1-counter) 

//sd cmd input pad register
always @(posedge sd_clk)
    cmd_dat_reg <= cmd_dat_i;

//------------------------------------------
sd_crc_7 CRC_7(
             crc_bit,
             crc_enable,
             sd_clk,
             crc_rst,
             crc_val);

//------------------------------------------
always @(state or counter or start_i or with_response or cmd_dat_reg or resp_len)
begin: FSM_COMBO
    case(state)
        INIT: begin
            if (counter >= INIT_DELAY) begin
                next_state <= IDLE;
            end
            else begin
                next_state <= INIT;
            end
        end
        IDLE: begin
            if (start_i) begin
                next_state <= SETUP_CRC;
            end
            else begin
                next_state <= IDLE;
            end
        end
        SETUP_CRC:
            next_state <= WRITE;
        WRITE:
            if (counter >= BITS_TO_SEND && with_response) begin
                next_state <= READ_WAIT;
            end
            else if (counter >= BITS_TO_SEND) begin
                next_state <= FINISH_WO;
            end
            else begin
                next_state <= WRITE;
            end
        READ_WAIT:
            if (!cmd_dat_reg) begin
                next_state <= READ;
            end
            else begin
                next_state <= READ_WAIT;
            end
        FINISH_WO:
            next_state <= IDLE;
        READ:
            if (counter >= resp_len+8) begin
                next_state <= FINISH_WR;
            end
            else begin
                next_state <= READ;
            end
        FINISH_WR:
            next_state <= IDLE;
        default: 
            next_state <= INIT;
    endcase
end

always @(posedge sd_clk or posedge rst)
begin: COMMAND_DECODER
    if (rst) begin
        resp_len <= 0;
        with_response <= 0;
        cmd_buff <= 0;
    end
    else begin
        if (start_i == 1) begin
            resp_len <= setting_i[1] ? 127 : 39;
            with_response <= setting_i[0];
            cmd_buff <= cmd_i;
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
        resp_idx <= 0;
        cmd_oe_o <= 1;
        cmd_out_o <= 1;
        resp_buff <= 0;
        finish_o <= 0;
        crc_rst <= 1;
        crc_bit <= 0;
        crc_in <= 0;
        response_o <= 0;
        index_ok_o <= 0;
        crc_ok_o <= 0;
        crc_ok <= 0;
        counter <= 0;
    end
    else begin
        case(state)
            INIT: begin
                counter <= counter+1;
                cmd_oe_o <= 1;
                cmd_out_o <= 1;
            end
            IDLE: begin
                cmd_oe_o <= 0;      //Put CMD to Z
                counter <= 0;
                crc_rst <= 1;
                crc_enable <= 0;
                response_o <= 0;
                resp_idx <= 0;
                crc_ok_o <= 0;
                index_ok_o <= 0;
                finish_o <= 0;
            end
            SETUP_CRC: begin
                crc_rst <= 0;
                crc_enable <= 1;
                crc_bit <= cmd_buff[`cmd_idx];
            end
            WRITE: begin
                if (counter < BITS_TO_SEND-8) begin  // 1->40 CMD, (41 >= CNT && CNT <=47) CRC, 48 stop_bit
                    cmd_oe_o <= 1;
                    cmd_out_o <= cmd_buff[`cmd_idx];
                    if (counter < BITS_TO_SEND-9) begin //1 step ahead
                        crc_bit <= cmd_buff[`cmd_idx-1];
                    end else begin
                        crc_enable <= 0;
                    end
                end
                else if (counter < BITS_TO_SEND-1) begin
                    cmd_oe_o <= 1;
                    crc_enable <= 0;
                    cmd_out_o <= crc_val[BITS_TO_SEND-counter-2];
                end
                else if (counter == BITS_TO_SEND-1) begin
                    cmd_oe_o <= 1;
                    cmd_out_o <= 1'b1;
                end
                else begin
                    cmd_oe_o <= 0;
                    cmd_out_o <= 1'b1;
                end
                counter <= counter+1;
            end
            READ_WAIT: begin
                crc_enable <= 0;
                crc_rst <= 1;
                counter <= 1;
                cmd_oe_o <= 0;
                resp_buff[RESP_SIZE-1] <= cmd_dat_reg;
            end
            FINISH_WO: begin
                finish_o <= 1;
                crc_enable <= 0;
                crc_rst <= 1;
                counter <= 0;
                cmd_oe_o <= 0;
            end
            READ: begin
                crc_rst <= 0;
                crc_enable <= (resp_len != RESP_SIZE-1 || counter > 7);
                cmd_oe_o <= 0;
                if (counter <= resp_len) begin
                    if (counter < 8) //1+1+6 (S,T,Index)
                        resp_buff[RESP_SIZE-1-counter] <= cmd_dat_reg;
                    else begin
                        resp_idx <= resp_idx + 1;
                        resp_buff[RESP_SIZE-9-resp_idx] <= cmd_dat_reg;
                    end
                    crc_bit <= cmd_dat_reg;
                end
                else if (counter-resp_len <= 7) begin
                    crc_in[(resp_len+7)-(counter)] <= cmd_dat_reg;
                    crc_enable <= 0;
                end
                else begin
                    crc_enable <= 0;
                    if (crc_in == crc_val) crc_ok <= 1;
                    else crc_ok <= 0;
                end
                counter <= counter + 1;
            end
            FINISH_WR: begin
                if (cmd_buff[37:32] == resp_buff[125:120])
                    index_ok_o <= 1;
                else
                    index_ok_o <= 0;
                crc_ok_o <= crc_ok;
                finish_o <= 1;
                crc_enable <= 0;
                crc_rst <= 1;
                counter <= 0;
                cmd_oe_o <= 0;
                response_o <= resp_buff[119:0];
            end
        endcase
    end
end

endmodule



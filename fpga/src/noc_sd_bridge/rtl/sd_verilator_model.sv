//////////////////////////////////////////////////////////////////////
////                                                              ////
////  sdModel.v                                                   ////
////                                                              ////
////  This file is part of the SD Card IP core project            ////
////  http://www.opencores.org/                                   ////
////  ?do=project&who=sdcard_mass_storage_controller              ////
////                                                              ////
////  Author(s):                                                  ////
////      - Adam Edvardsson (adam.edvardsson@orsoc.se)            ////
////                                                              ////
//////////////////////////////////////////////////////////////////////
////                                                              ////
//// Copyright (C) 2009 Authors                                   ////
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
//// PURPOSE.  See the GNU Lesser General Public License for more ////
//// details.                                                     ////
////                                                              ////
//// You should have received a copy of the GNU Lesser General    ////
//// Public License along with this source; if not, download it   ////
//// from http://www.opencores.org/lgpl.shtml                     ////
////                                                              ////
//////////////////////////////////////////////////////////////////////

`define CRC_OFF 19
`define BIT_CRC_CYCLE 16

`define tTLH 10 //Clock rise time
`define tHL 10 //Clock fall time
`define tISU 6 //Input setup time
`define tIH 0 //Input hold time
`define tODL 14 //Output delay
`define DLY_TO_OUTP 47 

`define BLOCKSIZE 512
`define MEMSIZE (32<<20)
`define BLOCK_BUFFER_SIZE 1
`define TIME_BUSY 63

`define BIT_BLOCK_REC (BlockSize << 1)
`define BIT_BLOCK (`BIT_BLOCK_REC+`CRC_OFF+1)

`define PRG 7
`define RCV 6
`define DATAS 5
`define TRAN 4

// verilator lint_off MULTIDRIVEN

module sd_verilator_model(
  input 	   sdClk,
  input 	   cmd,
  output reg 	   cmdOut,
  input [3:0] 	   dat,
  output reg [3:0] datOut,
  output reg 	   oeCmd,
  output reg 	   oeDat);

reg [31:0] transf_cnt;
reg [7:0] crnt_word;

    

reg [5:0] lastCMD;
reg cardIdentificationState;
reg CardTransferActive;

reg InbuffStatus;
reg [31:0] BlockAddr;
reg [31:0] BlockSize;
reg [7:0] Inbuff [0:511];
reg [7:0] FLASHmem [0:`MEMSIZE+8+64+1];


reg [46:0]inCmd;
reg [5:0]cmdRead;
reg [7:0] cmdWrite;
reg crcIn;
reg crcEn;
reg crcRst;
reg [31:0] CardStatus;
reg [15:0] RCA;
reg [31:0] OCR;
reg [119:0] CID;
reg [119:0] CSD;
reg Busy; //0 when busy
wire [6:0] crcOut;
reg [4:0] crc_c;
reg [3:0] crc_lane;

`define RCASTART 16'hBEEF
`define OCRSTART 32'hC0ff8000
`define SCRSTART 64'h0235800300000000
`define STATUSSTART 32'h0
`define CIDSTART 120'h534d534d49202010025166450082  //Just some random data not really useful anyway 
`define CSDSTART 120'h0e00325b59050076b27f800a4040

`define outDelay 4 
reg [2:0] outDelayCnt;
reg [9:0] flash_write_cnt;
reg [8:0] flash_blockwrite_cnt;

parameter SIZE = 10;
parameter CONTENT_SIZE = 40;
parameter 
    IDLE   =  10'b0000_0000_01,
    READ_CMD   =  10'b0000_0000_10,
    ANALYZE_CMD	    =  10'b0000_0001_00,
    SEND_CMD	    =  10'b0000_0010_00;
reg [SIZE-1:0] state;
reg [SIZE-1:0] next_state;

parameter 
    DATA_IDLE   =10'b0000_0000_01,    
    READ_WAITS  =10'b0000_0000_10,
    READ_DATA  = 10'b0000_0001_00,
    WRITE_FLASH =10'b0000_0010_00,
    WRITE_DATA  =10'b0000_0100_00;
parameter okcrctoken = 4'b0101;
parameter invalidcrctoken = 4'b1111;
reg [SIZE-1:0] dataState;
reg [SIZE-1:0] next_datastate;

reg ValidCmd;
reg inValidCmd;

reg [7:0] response_S;
reg [135:0] response_CMD;
integer responseType;

     reg [8:0] block_cnt;
     reg wptr;
     reg crc_ok;
     reg [3:0] last_din;
     


reg crcDat_rst;
reg mult_read;
reg mult_write;
reg crcDat_en;
reg [3:0] crcDat_in; 
wire [15:0] crcDat_out [3:0];

genvar i;
generate
for(i=0; i<4; i=i+1) begin:CRC_16_gen
  sd_crc_16 CRC_16_i (crcDat_in[i],crcDat_en, sdClk, crcDat_rst, crcDat_out[i]);
end
endgenerate  
sd_crc_7 crc_7( 
crcIn,
crcEn,
sdClk,
crcRst,
crcOut);

reg stop;

reg appendCrc;
reg [5:0] startUppCnt;

reg q_start_bit;

reg [31:0] k;
   
reg qCmd; 
reg [2:0] crcCnt;

reg add_wrong_cmd_crc;
reg add_wrong_cmd_indx;
reg add_wrong_data_crc;
reg [7:0] tmpscr, masked;
function [31:0] pattern;
   input [31:0] k;

   begin
      pattern = {k[16:13],4'h3,k[12:9],4'hC,1'b1,k[8:6],4'hA,k[5:2],4'h5};
   end

endfunction
   
initial begin
   for (k=0; k < 512; k=k+4) case(k[8:2])			       
     110: {FLASHmem[k+3],FLASHmem[k+2],FLASHmem[k+1],FLASHmem[k]} = 32'H2741F751;
     111: {FLASHmem[k+3],FLASHmem[k+2],FLASHmem[k+1],FLASHmem[k]} = 32'H00000000;
     112: {FLASHmem[k+3],FLASHmem[k+2],FLASHmem[k+1],FLASHmem[k]} = 32'H01270B45;
     113: {FLASHmem[k+3],FLASHmem[k+2],FLASHmem[k+1],FLASHmem[k]} = 32'H4337fe1f;
     114: {FLASHmem[k+3],FLASHmem[k+2],FLASHmem[k+1],FLASHmem[k]} = 32'H0000f2df;
     127: {FLASHmem[k+3],FLASHmem[k+2],FLASHmem[k+1],FLASHmem[k]} = 32'H000055AA;
     default: {FLASHmem[k+3],FLASHmem[k+2],FLASHmem[k+1],FLASHmem[k]} = 0 & pattern(k);			       
     endcase
   for (k=512; k < 1024; k=k+4)
     {FLASHmem[k+3],FLASHmem[k+2],FLASHmem[k+1],FLASHmem[k]} = 32'HFFFFFFFF;
  for (k=1024; k<`MEMSIZE; k=k+4)
    begin
       {FLASHmem[k+3],FLASHmem[k+2],FLASHmem[k+1],FLASHmem[k]} = 0 & pattern(k);
    end
  {FLASHmem[k+3],FLASHmem[k+2],FLASHmem[k+1],FLASHmem[k],FLASHmem[k+7],FLASHmem[k+6],FLASHmem[k+5],FLASHmem[k+4]} = `SCRSTART;
  for (k=`MEMSIZE+8; k<`MEMSIZE+72; k=k+4)
    case(k[5:2])
     0 : {FLASHmem[k+3],FLASHmem[k+2],FLASHmem[k+1],FLASHmem[k]} = 32'H00000000;
     1 : {FLASHmem[k+3],FLASHmem[k+2],FLASHmem[k+1],FLASHmem[k]} = 32'H04000000;
     2 : {FLASHmem[k+3],FLASHmem[k+2],FLASHmem[k+1],FLASHmem[k]} = 32'H04009000;
     3 : {FLASHmem[k+3],FLASHmem[k+2],FLASHmem[k+1],FLASHmem[k]} = 32'H0F050A00;
     4 : {FLASHmem[k+3],FLASHmem[k+2],FLASHmem[k+1],FLASHmem[k]} = 32'H00000000;
     5 : {FLASHmem[k+3],FLASHmem[k+2],FLASHmem[k+1],FLASHmem[k]} = 32'H00000000;
     6 : {FLASHmem[k+3],FLASHmem[k+2],FLASHmem[k+1],FLASHmem[k]} = 32'H00000000;
     7 : {FLASHmem[k+3],FLASHmem[k+2],FLASHmem[k+1],FLASHmem[k]} = 32'H00000000;
     8 : {FLASHmem[k+3],FLASHmem[k+2],FLASHmem[k+1],FLASHmem[k]} = 32'H00000000;
     9 : {FLASHmem[k+3],FLASHmem[k+2],FLASHmem[k+1],FLASHmem[k]} = 32'H00000000;
    10 : {FLASHmem[k+3],FLASHmem[k+2],FLASHmem[k+1],FLASHmem[k]} = 32'H00000000;
    11 : {FLASHmem[k+3],FLASHmem[k+2],FLASHmem[k+1],FLASHmem[k]} = 32'H00000000;
    12 : {FLASHmem[k+3],FLASHmem[k+2],FLASHmem[k+1],FLASHmem[k]} = 32'H00000000;
    13 : {FLASHmem[k+3],FLASHmem[k+2],FLASHmem[k+1],FLASHmem[k]} = 32'H00000000;
    14 : {FLASHmem[k+3],FLASHmem[k+2],FLASHmem[k+1],FLASHmem[k]} = 32'H00000000;
    15 : {FLASHmem[k+3],FLASHmem[k+2],FLASHmem[k+1],FLASHmem[k]} = 32'H00000001;
    endcase; // case (k[5:2])
   FLASHmem[k] = 42;
  add_wrong_data_crc=0;
  add_wrong_cmd_indx=0;
  add_wrong_cmd_crc=0;
   stop=1;
  cardIdentificationState=1;
  state=IDLE;
  dataState=DATA_IDLE;
  Busy=0;
  oeCmd=0;
  crcCnt=0;
  CardTransferActive=0;
  qCmd=1;
  oeDat=0;
  cmdOut=0;
  cmdWrite=0;  
  InbuffStatus=0;
  datOut=0;
  inCmd=0;
  responseType=0;
  mult_read=0;
  mult_write=0;
  crcIn=0;
  response_S=0;
  crcEn=0;
  crcRst=0;
   crc_c=0;
   crc_lane=0;
   crc_ok=0;
   lastCMD=0;
   last_din=0;
   
  cmdRead=0;
  ValidCmd=0;
  inValidCmd=0;
  appendCrc=0;
  RCA= `RCASTART;
  OCR= `OCRSTART;
  CardStatus = `STATUSSTART;
  CID=`CIDSTART;
  CSD=`CSDSTART;
  response_CMD=0;
  outDelayCnt=0;
  crcDat_rst=1;
  crcDat_en=0;
  crcDat_in=0; 
  transf_cnt=0;
  BlockAddr=0;
  block_cnt =0;     
  wptr=0;
  transf_cnt=0;
  crcDat_rst=1;
  crcDat_en=0;
  crcDat_in=0; 
  flash_write_cnt=0;
  startUppCnt=0;
  flash_blockwrite_cnt=0;
end

//CARD logic

always @ (state or cmd or cmdRead or ValidCmd or inValidCmd or cmdWrite or outDelayCnt)
begin : FSM_COMBO
 next_state  = 0;   
case(state)  
IDLE: begin
   if (!cmd) 
     next_state = READ_CMD;
  else
     next_state = IDLE; 
end  
READ_CMD: begin
  if (cmdRead>= 47) 
     next_state = ANALYZE_CMD;
  else
     next_state =  READ_CMD; 
 end
 ANALYZE_CMD: begin
  if ((ValidCmd  )   && (outDelayCnt >= `outDelay ))
     next_state = SEND_CMD;
  else if (inValidCmd)
     next_state =  IDLE; 
 else
    next_state =  ANALYZE_CMD; 
 end 
 SEND_CMD: begin
    if (cmdWrite>= response_S) 
     next_state = IDLE;
  else
     next_state =  SEND_CMD; 
 
 end
 default:
   next_state = state;
 
 endcase
end

always @ (dataState or CardStatus or crc_c or flash_write_cnt or dat[0] or stop or transf_cnt)
begin : FSM_COMBODAT
 next_datastate  = 0;   
case(dataState)  
 DATA_IDLE: begin
   if ((CardStatus[12:9]==`RCV) ||  (mult_read == 1'b1) )  
     next_datastate = READ_WAITS;
   else if ((CardStatus[12:9]==`DATAS )||  (mult_write == 1'b1) ) 
     next_datastate = WRITE_DATA;
   else
     next_datastate = DATA_IDLE; 
 end  
  
 READ_WAITS: begin
   if ( dat[0] == 1'b0 ) 
     next_datastate =  READ_DATA;
   else
     next_datastate =  READ_WAITS; 
 end
 
 READ_DATA : begin  
  if (crc_c==0  ) 
     next_datastate =  WRITE_FLASH;
  else begin
	if (stop == 1'b0)
     next_datastate =  READ_DATA;
    else
     next_datastate =  DATA_IDLE;
    end


 end
  WRITE_FLASH : begin
  if (flash_write_cnt>265 ) 	
     next_datastate =  DATA_IDLE;
  else 
     next_datastate =  WRITE_FLASH;
  
end  

  WRITE_DATA : begin   
    if (transf_cnt >= `BIT_BLOCK) 
       next_datastate= DATA_IDLE;  
    else 
		 begin
			if (stop == 1'b0)
			 next_datastate=WRITE_DATA;  
			else
			 next_datastate =  DATA_IDLE;
        end
  end

 default:
   next_datastate = dataState;
 
 endcase
end

integer outdly_cnt;

always @ (posedge sdClk  )
 begin 
    q_start_bit <= dat[0];
 begin : FSM_SEQ
    state <= next_state; 
 end
 begin : FSM_SEQDAT
    dataState <= next_datastate; 
 end
 if (CardTransferActive) begin
 if (InbuffStatus==0) //empty
   CardStatus[8]<=1;
  else
   CardStatus[8]<=0;
  end
else 
  CardStatus[8]<=1;
     
 startUppCnt<=startUppCnt+1;
 OCR[31]<=Busy;
 if (startUppCnt == `TIME_BUSY)
   Busy <=1;   
 qCmd<=cmd;
 case(state)
   IDLE: begin
      //mult_write <= 0; 
      //mult_read <=0; 
      crcIn<=0;
      crcEn<=0;
      crcRst<=1;
      oeCmd<=0;
      stop<=0;
      cmdRead<=0;
      appendCrc<=0;
      ValidCmd<=0;
      inValidCmd=0;
      cmdWrite<=0;
      crcCnt<=0;
      response_CMD<=0;
      response_S<=0;
      outDelayCnt<=0;
      responseType=0;      
      crnt_word = 0;
    end
   READ_CMD: begin //read cmd
      crcEn<=1;
      crcRst<=0;
      crcIn <= #`tIH qCmd; 
      inCmd[47-cmdRead]  <= #`tIH qCmd;    
      cmdRead <= #1 cmdRead+1;
      if (cmdRead >= 40) 
         crcEn<=0;
         
      if (cmdRead == 46) begin
          oeCmd<=1;
     cmdOut<=1;
      end
   end 
        
   ANALYZE_CMD: begin//check for valid cmd
   //Wrong CRC go idle
    if (inCmd[46] == 0) //start
      inValidCmd=1;
    else if (inCmd[7:1] != crcOut) begin
      inValidCmd=1;
      $write("**sd_Model Commando CRC Error\r\n") ;
    end  
    else if  (inCmd[0] != 1)  begin//stop 
      inValidCmd=1;
      $write("**sd_Model Commando No Stop Bit Error\r\n") ;
    end  
    else begin
      if(outDelayCnt ==0)
        CardStatus[3]<=0;
         case(inCmd[45:40])
       0 : begin
	   response_S <= 0;
	   response_CMD <= 0;
	   cardIdentificationState<=1;
	   add_wrong_data_crc<=0;
	   add_wrong_cmd_indx<=0;
	   add_wrong_cmd_crc<=0;
	   cardIdentificationState<=1;
	   state<=IDLE;
	   dataState<=DATA_IDLE;
	   Busy<=0;
	   oeCmd<=0;
	   crcCnt<=0;
	   CardTransferActive<=0;
	   qCmd<=1;
	   oeDat<=0;
	   cmdOut<=0;
	   cmdWrite<=0;
	   startUppCnt<=0;
	   InbuffStatus<=0;
	   datOut<=4'hf;
	   inCmd<=0;
	   responseType=0;
	   crcIn<=0;
	   response_S<=0;
	   crcEn<=0;
	   crcRst<=0;
	   cmdRead<=0;
	   ValidCmd<=0;
	   inValidCmd=0;
	   appendCrc<=0;
	   RCA<= `RCASTART;
	   OCR<= `OCRSTART;
	   CardStatus <= `STATUSSTART;
	   CID<=`CIDSTART;
	   CSD<=`CSDSTART;
	   response_CMD<=0;
	   outDelayCnt<=0;
	   crcDat_rst<=1;
	   crcDat_en<=0;
	   crcDat_in<=0; 
	   transf_cnt<=0;
	   BlockAddr=0;
	   block_cnt <=0;     
	   wptr<=0;
	   transf_cnt<=0;
	   crcDat_rst<=1;
	   crcDat_en<=0;
	   crcDat_in<=0; 
	   flash_write_cnt<=0;
	   flash_blockwrite_cnt<=0;
        end    
        2 : begin
	   response_S <= 136;
         if (lastCMD != 41 && outDelayCnt==0) begin
               $write("**Error in sequnce, ACMD 41 should precede 2 in Startup state\r\n") ;
               CardStatus[3]<=1;
            end  
        response_CMD[127:8] <= CID;
        appendCrc<=0;
        responseType=2;
        CardStatus[12:9] <=2;
        end
        3 :  begin
	   response_S <= 48;
           if (lastCMD != 2 && outDelayCnt==0 ) begin
               $write("**Error in sequnce, CMD 2 should precede 3 in Startup state\r\n") ;
               CardStatus[3]<=1;
            end  
        response_CMD[127:112] <= RCA[15:0] ;
        response_CMD[111:96] <= CardStatus[15:0] ;
        appendCrc<=1;
        CardStatus[12:9] <=3;
        cardIdentificationState<=0;
       end
        6 : begin         
           if (lastCMD == 55 && outDelayCnt==0) begin             
              if (inCmd[9:8] == 2'b10)
                 $write("**BUS WIDTH 4\r\n") ;
              else
                 $write("**BUS WIDTH 1\r\n") ;
              response_S<=48;
              response_CMD[127:96] <= CardStatus; 
           end   
           else begin
	      response_S <= 48;     
	      if (outDelayCnt==0) begin 
		 if (CardStatus[12:9] == `TRAN) begin //If card is in transferstate                               
		    CardStatus[12:9] <=`DATAS;//Put card in data state
		    response_CMD[127:96] <= CardStatus ;
		    BlockAddr = `MEMSIZE;
	            BlockSize = 8;
		 end
		 else begin
		    response_S <= 0;
		    response_CMD[127:96] <= 0; 
		 end
		 responseType=3; 
		 appendCrc<=1;
	      end
           end
        end   
        7: begin
	   response_S <= 48;
         if (outDelayCnt==0) begin 
          if (inCmd[39:24]== RCA[15:0]) begin
              CardTransferActive <= 1;
              response_CMD[127:96] <= CardStatus ; 
              CardStatus[12:9] <=`TRAN;                            
          end
          else begin
               CardTransferActive <= 0;
               response_CMD[127:96] <= CardStatus ; 
               CardStatus[12:9] <=3;  
          end          
         end        
        end      
        8 :
	  begin
	     response_S <= 48;
	     response_CMD[127:96] <= inCmd[39:8];
	  end
	   9 : begin
	      response_S <= 136;
         if (lastCMD != 41 && outDelayCnt==0) begin
               $write("**Error in sequnce, ACMD 41 should precede 2 in Startup state\r\n") ;
               CardStatus[3]<=1;
            end  
        response_CMD[127:8] <= CSD;
        appendCrc<=0; 
        CardStatus[12:9] <=2;
        end
		
	12: begin
	   response_S <= 48;
          response_CMD[127:96] <= CardStatus ;         
          stop<=1;
	  mult_write <= 0; 
          mult_read <=0; 
         CardStatus[12:9] <= `TRAN;
        end 
		
	13: begin
	   response_S <= 48;
           response_CMD[127:96] <= CardStatus ;         
	   mult_write <= 0; 
           CardStatus[12:9] <= `TRAN;
	   if (outDelayCnt==0) begin 
	      if (CardStatus[12:9] == `TRAN) begin //If card is in transferstate                               
		 CardStatus[12:9] <=`DATAS;//Put card in data state
		 response_CMD[127:96] <= CardStatus ;
		 BlockAddr = `MEMSIZE+8;
	         BlockSize = 64;
	      end
	      else begin
		 response_S <= 0;
		 response_CMD[127:96] <= 0; 
	      end
	      responseType=3; 
	      appendCrc<=1;
	   end 
        end 

        16 : begin
	   response_S <= 48;
          response_CMD[127:96] <= CardStatus ;         
                
        end 

        17 :  begin
	   response_S <= 48;
          if (outDelayCnt==0) begin 
            if (CardStatus[12:9] == `TRAN) begin //If card is in transferstate                               
                CardStatus[12:9] <=`DATAS;//Put card in data state
                response_CMD[127:96] <= CardStatus ;
                BlockAddr = inCmd[39:8];
	        BlockSize = `BLOCKSIZE;
                if (BlockAddr%512 !=0)
                  $write("**Block Misalign Error\r\n");         
          end
           else begin
             response_S <= 0;
             response_CMD[127:96] <= 0; 
           end
         end
    
       end 

     18 :  begin
	response_S <= 48;
          if (outDelayCnt==0) begin 
            if (CardStatus[12:9] == `TRAN) begin //If card is in transferstate                               
                CardStatus[12:9] <=`DATAS;//Put card in data state
                response_CMD[127:96] <= CardStatus ;
			    mult_read <= 1;
                BlockAddr = inCmd[39:8];
	        BlockSize = `BLOCKSIZE;
                if (BlockAddr%512 !=0)
                  $write("**Block Misalign Error\r\n");         
          end
           else begin
             response_S <= 0;
             response_CMD[127:96] <= 0; 
			 
           end
         end
    
       end 
        
        24 : begin
	   response_S <= 48;
          if (outDelayCnt==0) begin 
            if (CardStatus[12:9] == `TRAN) begin //If card is in transferstate
              if (CardStatus[8]) begin //If Free write buffer           
                CardStatus[12:9] <=`RCV;//Put card in Rcv state
                response_CMD[127:96] <= CardStatus ;
                BlockAddr = inCmd[39:8];
	        BlockSize = `BLOCKSIZE;
                if (BlockAddr%512 !=0)
                  $write("**Block Misalign Error\r\n");
              end
              else begin
                response_CMD[127:96] <= CardStatus;
                 $write("**Error Try to blockwrite when No Free Writebuffer\r\n") ;
             end
           end
           else begin
             response_S <= 0;
             response_CMD[127:96] <= 0; 
           end
         end
       end
        25 : begin
	   response_S <= 48;
          if (outDelayCnt==0) begin 
            if (CardStatus[12:9] == `TRAN) begin //If card is in transferstate
              if (CardStatus[8]) begin //If Free write buffer           
                CardStatus[12:9] <=`RCV;//Put card in Rcv state
                response_CMD[127:96] <= CardStatus ;
                BlockAddr = inCmd[39:8];
	        BlockSize = `BLOCKSIZE;
		mult_write <= 1;
                if (BlockAddr%512 !=0)
                  $write("**Block Misalign Error\r\n");
              end
              else begin
                response_CMD[127:96] <= CardStatus;
                 $write("**Error Try to blockwrite when No Free Writebuffer\r\n") ;
             end
           end
           else begin
             response_S <= 0;
             response_CMD[127:96] <= 0; 
           end
         end     
       end

        33 : 
	  begin
	     response_S <= 48;
	     response_CMD[127:96] <= 48;
	  end
        41 : 
          begin
	     response_S <= 48;        
         if (cardIdentificationState) begin
            if (lastCMD != 55 && outDelayCnt==0) begin
               $write("**Error in sequence, CMD 55 should precede 41 in Startup state\r\n") ;
               CardStatus[3]<=1;
            end
            else begin
             responseType=3; 
             response_CMD[127:96] <= OCR;   
             appendCrc<=0;
             CardStatus[5] <=0;  
            if (Busy==1)
              CardStatus[12:9] <=1;
           end 
        end  
	end
        51 : 
          begin
	     response_S <= 48;        
             if (lastCMD != 55 && outDelayCnt==0) begin
		$write("**Error in sequence, CMD 55 should precede 51\r\n") ;
             end
             else begin
		if (outDelayCnt==0) begin 
		   if (CardStatus[12:9] == `TRAN) begin //If card is in transferstate                               
		      CardStatus[12:9] <=`DATAS;//Put card in data state
		      response_CMD[127:96] <= CardStatus ;
		      BlockAddr = `MEMSIZE;
	              BlockSize = 8;
		   end
		   else begin
		      response_S <= 0;
		      response_CMD[127:96] <= 0; 
		   end
		   responseType=3; 
		   appendCrc<=1;
		end 
	     end // else: !if(lastCMD != 55 && outDelayCnt==0)
	  end
        55 : 
          begin
	     response_S <= 48;
          response_CMD[127:96] <= CardStatus ;         
          CardStatus[5] <=1;      //Next CMD is AP specific CMD
          appendCrc<=1;         
        end 
        default:
	      $write("Invalid CMD%d\r\n", inCmd[45:40]);
	 endcase
     ValidCmd<=1;  
     crcIn<=0;
     
     outDelayCnt<=outDelayCnt+1;
     if (outDelayCnt==`outDelay)       
       crcRst<=1;
     oeCmd<=1;
     cmdOut<=1;
     response_CMD[135:134] <=0;
    
    if (responseType != 3 && responseType != 2)
       if (!add_wrong_cmd_indx)
         response_CMD[133:128] <=inCmd[45:40];
       else
         response_CMD[133:128] <=0;
    else
       response_CMD[133:128] <=6'b111111;
       
     lastCMD <=inCmd[45:40];
    end
   end
   
   default:;
   
   
 endcase    
  case (dataState)
  DATA_IDLE: begin

     crcDat_rst<=1;
     crcDat_en<=0;
     crcDat_in<=0;
     oeDat<=0;

  end
  
  READ_WAITS: begin
      oeDat<=0;
      crcDat_rst<=0;
      crcDat_en<=1;
      crcDat_in<=0; 
      crc_c<=15;//
      crc_ok<=1;      
  end       
  READ_DATA: begin
  
     
    InbuffStatus<=1;
    if (transf_cnt<`BIT_BLOCK_REC) begin
       if (wptr)
         Inbuff[block_cnt][3:0] <= dat;
       else
          Inbuff[block_cnt][7:4] <= dat;       
       
       if (!add_wrong_data_crc) 
          crcDat_in<=dat;
        else
          crcDat_in<=4'b1010;
          
       crc_ok<=1;
       transf_cnt<=transf_cnt+1; 
       if (wptr)
         block_cnt<=block_cnt+1;     
       wptr<=~wptr;
       
       
    end
    else if  ( transf_cnt <= (`BIT_BLOCK_REC +`BIT_CRC_CYCLE-1)) begin
       transf_cnt<=transf_cnt+1; 
       crcDat_en<=0;  
       last_din <=dat; 
       
       if (transf_cnt> `BIT_BLOCK_REC) begin       
        crc_c<=crc_c-1;
	  for (int i = 0; i < 4; i=i+1)
	    crc_lane[i] = crcDat_out[i][crc_c[3:0]];
	  for (int i = 0; i < 4; i=i+1)
            if (crc_lane[i] != last_din[i])
              crc_ok<=0;
      end                 
    end 
  end 
  WRITE_FLASH: begin
     oeDat<=1;
     block_cnt <=0;     
     wptr<=0;
     transf_cnt<=0;
     crcDat_rst<=1;
     crcDat_en<=0;
     crcDat_in<=0; 
     
    
  end // case: WRITE_FLASH
    default:;
    
  endcase  
end

always @ ( negedge sdClk) begin
 case(state)

SEND_CMD: begin
     crcRst<=0;
     crcEn<=1;
    cmdWrite<=cmdWrite+1;    
    if (response_S!=0)
     cmdOut<=0;   
   else
      cmdOut<=1;  
       
    if ((cmdWrite>0) &&  (cmdWrite < response_S-8)) begin
      cmdOut<=response_CMD[135-cmdWrite];
      crcIn<=response_CMD[134-cmdWrite];
      if (response_S == 136) 
        crcEn<=(cmdWrite >= 7);
      if (cmdWrite >= response_S-9)
       crcEn<=0;
    end
   else if (cmdWrite!=0) begin
     crcEn<=0;
     if (add_wrong_cmd_crc) begin
        cmdOut<=0;
        crcCnt<=crcCnt+1; 
     end 
     else begin   
     cmdOut<=crcOut[6-crcCnt];
     crcCnt<=crcCnt+1; 
     if (responseType == 3)
           cmdOut<=1;
    end     
   end
  if (cmdWrite == response_S-1)
    cmdOut<=1;
     
  end
   default:;
 
endcase
end

reg data_send_index;
integer write_out_index;
always @ (negedge sdClk) begin
  
  case (dataState)
  DATA_IDLE: begin
     write_out_index<=0;
     transf_cnt<=0;
     data_send_index<=0; 
     outdly_cnt<=0;
     flash_write_cnt<=0;
  end
  
  
   WRITE_DATA: begin
      oeDat<=1;
      outdly_cnt<=outdly_cnt+1;
     
      if ( outdly_cnt > `DLY_TO_OUTP) begin
         transf_cnt <= transf_cnt+1;
         crcDat_en<=1;
         crcDat_rst<=0;
         
      end   
      else begin
        crcDat_en<=0;
        crcDat_rst<=1;          
        oeDat<=1;   
        crc_c<=16; 
     end   
      crnt_word = FLASHmem[BlockAddr+write_out_index];
      if (transf_cnt==1) begin                 
          last_din <= crnt_word[7:4];           
          datOut<=0;
          crcDat_in<= crnt_word[7:4];  
          data_send_index<=1;    
        end
        else if ( (transf_cnt>=2) && (transf_cnt<=`BIT_BLOCK-`CRC_OFF )) begin                 
          data_send_index<=~data_send_index;
          if (!data_send_index) begin
             last_din<=crnt_word[7:4];
             crcDat_in<= crnt_word[7:4];
          end
          else begin
             last_din<=crnt_word[3:0];
             if (!add_wrong_data_crc)
               crcDat_in<= crnt_word[3:0];
             else
               crcDat_in<=4'b1010; 
             write_out_index<=write_out_index+1;
             
         end       
                 
                                    
          datOut<= last_din; 
                      
                    
          if ( transf_cnt >=`BIT_BLOCK-`CRC_OFF ) begin
             crcDat_en<=0;             
         end
         
       end
       else if (transf_cnt>`BIT_BLOCK-`CRC_OFF & crc_c!=0) begin
         datOut<= last_din; 
         crcDat_en<=0;
         crc_c<=crc_c-1; 
         if (crc_c<= 16) begin         
         datOut[0]<=crcDat_out[0][crc_c-1];
         datOut[1]<=crcDat_out[1][crc_c-1];
         datOut[2]<=crcDat_out[2][crc_c-1];
         datOut[3]<=crcDat_out[3][crc_c-1];       
       end  
       end
       else if (transf_cnt==`BIT_BLOCK-2) begin     
          datOut<=4'b1111;          
      end   
       else if ((transf_cnt !=0) && (crc_c == 0 ))begin
         oeDat<=0; 
         CardStatus[12:9] <= `TRAN;
         end
      
      
      
  end
  
  
  
  WRITE_FLASH: begin
    flash_write_cnt<=flash_write_cnt+1;
     CardStatus[12:9] <= `PRG;
      datOut[0]<=0;
       datOut[1]<=1;
       datOut[2]<=1;
       datOut[3]<=1;
    if (flash_write_cnt == 0)
      datOut<=1;
    else if(flash_write_cnt == 1)
     datOut[0]<=1;
    else if(flash_write_cnt == 2)
     datOut[0]<=0;
      
     
    else if ((flash_write_cnt > 2) && (flash_write_cnt < 7)) begin
      if (crc_ok) 
        datOut[0] <=okcrctoken[6-flash_write_cnt];
      else
        datOut[0] <= invalidcrctoken[6-flash_write_cnt];
    end
    else if  ((flash_write_cnt >= 7) && (flash_write_cnt < 264)) begin
       datOut[0]<=0;
      
      flash_blockwrite_cnt<=flash_blockwrite_cnt+2;
       FLASHmem[BlockAddr+{23'b0,flash_blockwrite_cnt}]<=Inbuff[flash_blockwrite_cnt];
       FLASHmem[BlockAddr+{23'b0,flash_blockwrite_cnt}+1]<=Inbuff[flash_blockwrite_cnt+1];
		
    end
    else begin
      datOut<=1;      
      InbuffStatus<=0;
      CardStatus[12:9] <= `TRAN;
    end  
  end
    default:;

endcase
end

endmodule

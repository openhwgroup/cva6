// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Igor Loi <igor.loi@unibo.it>

module generic_fifo_adv 
#( 
   parameter int unsigned          DATA_WIDTH = 32,
   parameter int unsigned          DATA_DEPTH = 8
   )
   (
    input  logic                                    clk,
    input  logic                                    rst_n,
    input  logic                                    clear_i,
    
    //PUSH SIDE
    input  logic [DATA_WIDTH-1:0]                   data_i,
    input  logic                                    valid_i,
    output logic                                    grant_o,
    
    //POP SIDE
    output logic [DATA_WIDTH-1:0]                   data_o,
    output logic                                    valid_o,
    input  logic                                    grant_i,
    
    input  logic                                    test_mode_i
    );
   
   
   // Local Parameter
   localparam  int 				    unsigned ADDR_DEPTH = $clog2(DATA_DEPTH);
   enum 					    logic [1:0] { EMPTY, FULL, MIDDLE } CS, NS;
   // Internal Signals
   
   logic 					    gate_clock;
   logic 					    clk_gated;
   
   logic [ADDR_DEPTH-1:0] 			    Pop_Pointer_CS,  Pop_Pointer_NS;
   logic [ADDR_DEPTH-1:0] 			    Push_Pointer_CS, Push_Pointer_NS;
   logic [DATA_WIDTH-1:0] 			    FIFO_REGISTERS[DATA_DEPTH-1:0];
   int 						    unsigned                    i;
   
   // Parameter Check
   // synopsys translate_off
   initial
   begin : parameter_check
      integer param_err_flg;
      param_err_flg = 0;
      
      if (DATA_WIDTH < 1)
	begin
           param_err_flg = 1;
           $display("ERROR: %m :\n  Invalid value (%d) for parameter DATA_WIDTH (legal range: greater than 1)", DATA_WIDTH );
	end
      
      if (DATA_DEPTH < 1)
	begin
           param_err_flg = 1;
           $display("ERROR: %m :\n  Invalid value (%d) for parameter DATA_DEPTH (legal range: greater than 1)", DATA_DEPTH );
	end                   
   end
   // synopsys translate_on
   
`ifndef PULP_FPGA_EMUL
   cluster_clock_gating cg_cell
     (
      .clk_i     ( clk         ),
      .en_i      (~gate_clock  ),
      .test_en_i ( test_mode_i ),
      .clk_o     ( clk_gated   )
      );
`else
   assign clk_gated = clk;
`endif
   
   // UPDATE THE STATE
   always_ff @(posedge clk, negedge rst_n)
     begin
	if(rst_n == 1'b0)
	  begin
             CS              <= EMPTY;
             Pop_Pointer_CS  <= {ADDR_DEPTH {1'b0}};
             Push_Pointer_CS <= {ADDR_DEPTH {1'b0}};
	  end
	else
	  begin
             if(clear_i)
               begin
		  CS              <= EMPTY;
		  Pop_Pointer_CS  <= {ADDR_DEPTH {1'b0}};
		  Push_Pointer_CS <= {ADDR_DEPTH {1'b0}};
               end
             else
               begin
		  CS              <= NS;
		  Pop_Pointer_CS  <= Pop_Pointer_NS;
		  Push_Pointer_CS <= Push_Pointer_NS;
               end
	  end
     end
   
   
   // Compute Next State
   always_comb
     begin
	gate_clock      = 1'b0;
	
	case(CS)
	  
	  EMPTY:
	    begin
               grant_o = 1'b1;
               valid_o = 1'b0;
	       
               case(valid_i)
		 1'b0 : 
		   begin 
                      NS              = EMPTY;
                      Push_Pointer_NS = Push_Pointer_CS;
                      Pop_Pointer_NS  = Pop_Pointer_CS;
                      gate_clock      = 1'b1;
		   end
		 
		 1'b1: 
		   begin 
                      NS              = MIDDLE;
                      Push_Pointer_NS = Push_Pointer_CS + 1'b1;
                      Pop_Pointer_NS  = Pop_Pointer_CS;
		   end
		 
               endcase
	    end//~EMPTY
	  
	  MIDDLE:
	    begin
               grant_o = 1'b1;
               valid_o = 1'b1;
	       
               case({valid_i,grant_i})
		 
		 2'b01:
		   begin
                      gate_clock      = 1'b1;
		      
                      if((Pop_Pointer_CS == Push_Pointer_CS -1 ) || ((Pop_Pointer_CS == DATA_DEPTH-1) && (Push_Pointer_CS == 0) ))
                        NS              = EMPTY;
                      else
                        NS              = MIDDLE;
		      
                      Push_Pointer_NS = Push_Pointer_CS;
		      
                      if(Pop_Pointer_CS == DATA_DEPTH-1)
                        Pop_Pointer_NS  = 0;
                      else
                        Pop_Pointer_NS  = Pop_Pointer_CS + 1'b1;
		   end
		 
		 2'b00 : 
		   begin
                      gate_clock      = 1'b1; 
                      NS              = MIDDLE;
                      Push_Pointer_NS = Push_Pointer_CS;
                      Pop_Pointer_NS  = Pop_Pointer_CS;
		   end
		 
		 2'b11: 
		   begin
                      NS              = MIDDLE;
		      
                      if(Push_Pointer_CS == DATA_DEPTH-1)
                        Push_Pointer_NS = 0;
                      else
                        Push_Pointer_NS = Push_Pointer_CS + 1'b1;
		      
                      if(Pop_Pointer_CS == DATA_DEPTH-1)
                        Pop_Pointer_NS  = 0;
                      else
                        Pop_Pointer_NS  = Pop_Pointer_CS  + 1'b1;
		   end
		 
		 2'b10:
		   begin 
                      if(( Push_Pointer_CS == Pop_Pointer_CS - 1) || ( (Push_Pointer_CS == DATA_DEPTH-1) && (Pop_Pointer_CS == 0) ))
                        NS              = FULL;
                      else
                        NS        = MIDDLE;
		      
                      if(Push_Pointer_CS == DATA_DEPTH - 1)
                        Push_Pointer_NS = 0;
                      else
                        Push_Pointer_NS = Push_Pointer_CS + 1'b1;
		      
                      Pop_Pointer_NS  = Pop_Pointer_CS;
		   end
		 
               endcase                     
	    end
	  
	  FULL:
	    begin
               grant_o     = 1'b0;
               valid_o     = 1'b1;
               gate_clock  = 1'b1;
	       
               case(grant_i)
		 1'b1: 
		   begin 
                      NS              = MIDDLE;
		      
                      Push_Pointer_NS = Push_Pointer_CS;
		      
                      if(Pop_Pointer_CS == DATA_DEPTH-1)
                        Pop_Pointer_NS  = 0;
                      else
                        Pop_Pointer_NS  = Pop_Pointer_CS  + 1'b1;
		   end
		 
		 1'b0:
		   begin 
                      NS              = FULL;
                      Push_Pointer_NS = Push_Pointer_CS;
                      Pop_Pointer_NS  = Pop_Pointer_CS;
		   end
               endcase                 
	       
	    end // end of FULL
	  
	  default :
	    begin
               gate_clock      = 1'b1;
               grant_o         = 1'b0;
               valid_o         = 1'b0;
               NS              = EMPTY;
               Pop_Pointer_NS  = 0;
               Push_Pointer_NS = 0;
	    end
	  
	endcase
     end
   
   always_ff @(posedge clk_gated, negedge rst_n)
     begin
	if(rst_n == 1'b0)
	  begin
	     for (i=0; i< DATA_DEPTH; i++)
               FIFO_REGISTERS[i] <= {DATA_WIDTH {1'b0}};
	  end
	else
	  begin
             if((grant_o == 1'b1) && (valid_i == 1'b1))
               FIFO_REGISTERS[Push_Pointer_CS] <= data_i;
	  end
     end
   
   assign data_o = FIFO_REGISTERS[Pop_Pointer_CS];
   
endmodule // generic_fifo

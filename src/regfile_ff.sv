////////////////////////////////////////////////////////////////////////////////
// Copyright (C) 2017 ETH Zurich, University of Bologna                       //
// All rights reserved.                                                       //
//                                                                            //
// This code is under development and not yet released to the public.         //
// Until it is released, the code is under the copyright of ETH Zurich        //
// and the University of Bologna, and may contain unpublished work.           //
// Any reuse/redistribution should only be under explicit permission.         //
//                                                                            //
// Bug fixes and contributions will eventually be released under the          //
// SolderPad open hardware license and under the copyright of ETH Zurich      //
// and the University of Bologna.                                             //
//                                                                            //
// Engineer:       Francesco Conti - f.conti@unibo.it                         //
//                                                                            //
// Additional contributions by:                                               //
//                 Markus Wegmann - markus.wegmann@technokrat.ch              //
//                                                                            //
// Design Name:    RISC-V register file                                       //
// Project Name:   zero-riscy                                                 //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Register file with 31 or 15x 32 bit wide registers.        //
//                 Register 0 is fixed to 0. This register file is based on   //
//                 flip flops.                                                //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

module regfile_ff
#(
  parameter DATA_WIDTH    = 32
)
(
  // Clock and Reset
  input  logic                   clk,
  input  logic                   rst_n,

  input  logic                   test_en_i,

  //Read port R1
  input  logic [4:0]             raddr_a_i,
  output logic [DATA_WIDTH-1:0]  rdata_a_o,

  //Read port R2
  input  logic [4:0]             raddr_b_i,
  output logic [DATA_WIDTH-1:0]  rdata_b_o,


  // Write port W1
  input  logic [4:0]              waddr_a_i,
  input  logic [DATA_WIDTH-1:0]   wdata_a_i,
  input  logic                    we_a_i

);

  localparam    ADDR_WIDTH = 5;
  localparam    NUM_WORDS  = 2**ADDR_WIDTH;

  logic [NUM_WORDS-1:0][DATA_WIDTH-1:0] rf_reg;
  logic [NUM_WORDS-1:0]                 we_a_dec;

  always_comb
  begin : we_a_decoder
    for (int i = 0; i < NUM_WORDS; i++) begin
      if (waddr_a_i == i)
        we_a_dec[i] = we_a_i;
      else
        we_a_dec[i] = 1'b0;
    end
  end


  genvar i;
  generate

    // loop from 1 to NUM_WORDS-1 as R0 is nil
    for (i = 1; i < NUM_WORDS; i++)
    begin : rf_gen

      always_ff @(posedge clk, negedge rst_n)
      begin : register_write_behavioral
        if (rst_n==1'b0) begin
          rf_reg[i] <= 'b0;
        end else begin
          if (we_a_dec[i])
            rf_reg[i] <= wdata_a_i;
        end
      end

    end

    // R0 is nil
    assign rf_reg[0] = '0;

  endgenerate

  assign rdata_a_o = rf_reg[raddr_a_i];
  assign rdata_b_o = rf_reg[raddr_b_i];

endmodule
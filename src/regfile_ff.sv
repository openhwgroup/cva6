// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// Engineer:       Francesco Conti - f.conti@unibo.it
//
// Additional contributions by:
//                 Markus Wegmann - markus.wegmann@technokrat.ch
//
// Design Name:    RISC-V register file
// Project Name:   zero-riscy
// Language:       SystemVerilog
//
// Description:    Register file with 31 or 15x 32 bit wide registers.
//                 Register 0 is fixed to 0. This register file is based on
//                 flip flops.
//

module regfile
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
  input  logic                    we_a_i,
  
  // Debug ports
  output logic [DATA_WIDTH-1:0]  ra, sp, gp, tp, t0, t1, t2, s0, s1,
  output logic [DATA_WIDTH-1:0]  a0, a1, a2, a3, a4, a5, a6, a7,
  output logic [DATA_WIDTH-1:0]  s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, t3, t4, t5, t6

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
    `ifdef verilator
    always_ff @(posedge clk, negedge rst_n)
    begin
      rf_reg[0] <= '0;
    end
    `else
    assign rf_reg[0] = '0;
    `endif

  endgenerate

  assign rdata_a_o = rf_reg[raddr_a_i];
  assign rdata_b_o = rf_reg[raddr_b_i];

  // Debug outputs
  assign ra = rf_reg[1];
  assign sp = rf_reg[2];
  assign gp = rf_reg[3];
  assign tp = rf_reg[4];
  assign t0 = rf_reg[5];
  assign t1 = rf_reg[6];
  assign t2 = rf_reg[7];
  assign s0 = rf_reg[8];
  assign s1 = rf_reg[9];
  assign a0 = rf_reg[10];
  assign a1 = rf_reg[11];
  assign a2 = rf_reg[12];
  assign a3 = rf_reg[13];
  assign a4 = rf_reg[14];
  assign a5 = rf_reg[15];
  assign a6 = rf_reg[16];
  assign a7 = rf_reg[17];
  assign s2 = rf_reg[18];
  assign s3 = rf_reg[19];
  assign s4 = rf_reg[20];
  assign s5 = rf_reg[21];
  assign s6 = rf_reg[22];
  assign s7 = rf_reg[23];
  assign s8 = rf_reg[24];
  assign s9 = rf_reg[25];
  assign s10 = rf_reg[26];
  assign s11 = rf_reg[27];
  assign t3 = rf_reg[28];
  assign t4 = rf_reg[29];
  assign t5 = rf_reg[30];
  assign t6 = rf_reg[31];
  
endmodule

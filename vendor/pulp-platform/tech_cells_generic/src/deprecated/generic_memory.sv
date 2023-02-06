// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

module generic_memory
#(
  parameter ADDR_WIDTH = 12,
  parameter DATA_WIDTH = 32,
  parameter BE_WIDTH   = DATA_WIDTH/8
)
(
  input  logic                  CLK,
  input  logic                  INITN,

  input  logic                  CEN,
  input  logic [ADDR_WIDTH-1:0] A,
  input  logic                  WEN,
  input  logic [DATA_WIDTH-1:0] D,
  input  logic [BE_WIDTH-1:0]   BEN,

  output logic [DATA_WIDTH-1:0] Q
);

   localparam   NUM_WORDS = 2**ADDR_WIDTH;

   logic [DATA_WIDTH-1:0]                   MEM [NUM_WORDS-1:0];
   logic [DATA_WIDTH-1:0]                   M;
   genvar                         i,j;

   generate
      for (i=0; i<BE_WIDTH; i++)
        begin
           for (j=0; j<8; j++)
             begin
                assign M[i*8+j] = BEN[i];
             end
        end
   endgenerate

   generate
      for (i=0; i < DATA_WIDTH ; i++)
        begin
           always @ (posedge CLK)
             begin
                if ( INITN == 1'b1 )
                  begin
                     if ( CEN == 1'b0 )
                       begin
                          if ( WEN == 1'b0 )
                            begin
                               if ( M[i] == 1'b0 )
                                 begin
                                    MEM[A][i] <= D[i];
                                 end
                            end
                          else if(WEN == 1'b1)
                            begin
                               Q[i] <= MEM[A][i];
                            end
                       end
                  end
             end
        end
   endgenerate

endmodule
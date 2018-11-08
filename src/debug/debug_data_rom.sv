// Copyright 2017, 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// Date: 13.10.2017
// Description: Fake cache RAM using debug_rom

module debug_data_rom #(
    int unsigned DATA_WIDTH = 64,
    int unsigned NUM_WORDS  = 1024
)(
   input  logic                          clk_i,
   input  logic                          rst_ni,
   input  logic                          req_i,
   input  logic                          we_i,
   input  logic [$clog2(NUM_WORDS)-1:0]  addr_i,
   input  logic [DATA_WIDTH-1:0]         wdata_i,
   input  logic [DATA_WIDTH/8-1:0]       be_i,
   output logic [DATA_WIDTH-1:0]         rdata_o,
   input  logic                          resumereq_i,
   input  logic                          cmdbusy_i,
   input  logic                          transfer_i
);

   localparam DbgAddressBits  = 12;
   localparam logic [DbgAddressBits-1:0] ProgBufBase = (dm::DataAddr - 4*dm::ProgBufSize);
   localparam logic [DbgAddressBits-1:0] AbstractCmdBase = (ProgBufBase - 4*6);
   
   logic [DATA_WIDTH-1:0]                rdata;
   
    debug_rom i_debug_rom_lo (
        .clk_i,
        .req_i,
        .addr_i({53'b0,addr_i[6:0],4'b0000}),
        .rdata_o(rdata[63:0])
    );
   
    debug_rom i_debug_rom_hi (
        .clk_i,
        .req_i,
        .addr_i({53'b0,addr_i[6:0],4'b1000}),
        .rdata_o(rdata[127:64])
    );

   always_comb
     if (addr_i[7:0] == 'h300)
       begin
          // variable ROM content
          // variable jump to abstract cmd, program_buffer or resume
          if (resumereq_i)
            begin
               rdata_o = {96'b0, riscv::jalr(0, 0, dm::ResumeAddress[11:0])};
            end
        
          // there is a command active so jump there
          if (cmdbusy_i)
            begin
               // transfer not set is a shortcut to the program buffer
               if (transfer_i)
                 begin
                    rdata_o = {96'b0, riscv::jalr(0, 0, ProgBufBase)};
                    // this is a legit abstract cmd -> execute it
                 end
               else
                 begin
                    rdata_o = {96'b0, riscv::jalr(0, 0, AbstractCmdBase)};
                 end
            end // if (cmdbusy_i)
       end
    else
        rdata_o = rdata;
                   
endmodule

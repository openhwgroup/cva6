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
// Description: Fake cache tag used during debugging

module debug_tag_rom #(
    int unsigned DATA_WIDTH = 64,
    int unsigned NUM_WORDS  = 1024
)(
   input  logic                          clk_i,
   input  logic                          rst_ni,
   input  logic                          req_i,
   input  logic                          we_i,
   input  logic [$clog2(NUM_WORDS)-1:0]  addr_i,
   input  logic [DATA_WIDTH-1:0]         wdata_i,
   input  logic [DATA_WIDTH-1:0]         be_i,
   output logic [DATA_WIDTH-1:0]         rdata_o
);

    struct packed {
        logic                 valid;
        logic [DATA_WIDTH-2:0] tag;
    } tag_rdata;
   
   always_ff @(posedge clk_i) if (!rst_ni)
     tag_rdata = 'b0;
   else
     begin
        if (req_i) begin
           if (!we_i)
             begin
                tag_rdata.valid = (addr_i[7:4] == 3) || (addr_i[7:4] == 8);
                tag_rdata.tag = 0;
             end
        end
     end

   assign rdata_o = tag_rdata;

endmodule

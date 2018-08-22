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
// Author: Florian Zaruba    <zarubaf@iis.ee.ethz.ch>, ETH Zurich
//         Michael Schaffner <schaffner@iis.ee.ethz.ch>, ETH Zurich
// Date: 15.08.2018
// Description: SRAM wrapper for FPGA (requires the fpga-support submodule)
//
// Note: the wrapped module contains two different implementations for 
// ALTERA and XILINX tools, since these follow different coding styles for 
// inferrable RAMS with byte enable. define `FPGA_TARGET_XILINX or 
// `FPGA_TARGET_ALTERA in your build environment (default is ALTERA)
        
module regfile #(
    parameter DATA_WIDTH = 64,
    parameter DATA_DEPTH = 1024
)(
    input  logic                          clk_i,
    input  logic                          rst_ni,
    input  logic                          we_i,
    input  logic [$clog2(DATA_DEPTH)-1:0] addr_i,
    input  logic [DATA_WIDTH-1:0]         wdata_i,
    input  logic [DATA_WIDTH-1:0]         biten_i, // bit enable
    output logic [DATA_WIDTH-1:0]         rdata_o
);

logic [DATA_DEPTH-1:0] regs_d[DATA_WIDTH-1:0];
logic [DATA_DEPTH-1:0] regs_q[DATA_WIDTH-1:0];

genvar k;
generate 
    for(k=0;k<DATA_DEPTH;k++) begin
        for (i;i<DATA_WIDTH;i++) begin
            assign regs_d[k][i] = (we_i & biten_i[i]) ? wdata_i[i] : regs_q[k][i];  
        end       
    end
endgenerate

assign rdata_o = regs_q[addr_i]; 

always_ff @(posedge clk_i or negedge rst_ni) begin : p_regs
    if(~rst_ni) begin
        regs_q <= '0;
    end else begin
        regs_q <= regs_d;
    end
end

endmodule : sram_wrap

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

module sram #(
    parameter DATA_WIDTH = 64,
    parameter USER_WIDTH = 1,
    parameter USER_EN    = 0,
    parameter NUM_WORDS  = 1024,
    parameter SIM_INIT   = "none",
    parameter OUT_REGS   = 0,    // enables output registers in FPGA macro (read lat = 2)
    parameter DROMAJO_RAM  = 0
)(
   input  logic                          clk_i,
   input  logic                          rst_ni,
   input  logic                          req_i,
   input  logic                          we_i,
   input  logic [$clog2(NUM_WORDS)-1:0]  addr_i,
   input  logic [USER_WIDTH-1:0]         wuser_i,
   input  logic [DATA_WIDTH-1:0]         wdata_i,
   input  logic [(DATA_WIDTH+7)/8-1:0]   be_i,
   output logic [USER_WIDTH-1:0]         ruser_o,
   output logic [DATA_WIDTH-1:0]         rdata_o
);

localparam DATA_WIDTH_ALIGNED = ((DATA_WIDTH+63)/64)*64;
localparam USER_WIDTH_ALIGNED = DATA_WIDTH_ALIGNED; // To be fine tuned to reduce memory size
localparam BE_WIDTH_ALIGNED   = (((DATA_WIDTH+7)/8+7)/8)*8;

logic [DATA_WIDTH_ALIGNED-1:0]  wdata_aligned;
logic [USER_WIDTH_ALIGNED-1:0]  wuser_aligned;
logic [BE_WIDTH_ALIGNED-1:0]    be_aligned;
logic [DATA_WIDTH_ALIGNED-1:0]  rdata_aligned;
logic [USER_WIDTH_ALIGNED-1:0]  ruser_aligned;

// align to 64 bits for inferrable macro below
always_comb begin : p_align
    wdata_aligned                    ='0;
    wuser_aligned                    ='0;
    be_aligned                       ='0;
    wdata_aligned[DATA_WIDTH-1:0]    = wdata_i;
    wuser_aligned[USER_WIDTH-1:0]    = wuser_i;
    be_aligned[BE_WIDTH_ALIGNED-1:0] = be_i;

    rdata_o = rdata_aligned[DATA_WIDTH-1:0];
    ruser_o = ruser_aligned[USER_WIDTH-1:0];
end

  for (genvar k = 0; k<(DATA_WIDTH+63)/64; k++) begin : gen_cut
    if (DROMAJO_RAM) begin : gen_dromajo
      dromajo_ram #(
        .ADDR_WIDTH($clog2(NUM_WORDS)),
        .DATA_DEPTH(NUM_WORDS),
        .OUT_REGS (0)
      ) i_ram (
          .Clk_CI    ( clk_i                     ),
          .Rst_RBI   ( rst_ni                    ),
          .CSel_SI   ( req_i                     ),
          .WrEn_SI   ( we_i                      ),
          .BEn_SI    ( be_aligned[k*8 +: 8]      ),
          .WrData_DI ( wdata_aligned[k*64 +: 64] ),
          .Addr_DI   ( addr_i                    ),
          .RdData_DO ( rdata_aligned[k*64 +: 64] )
      );
      if (USER_EN) begin : gen_dromajo_user
        dromajo_ram #(
          .ADDR_WIDTH($clog2(NUM_WORDS)),
          .DATA_DEPTH(NUM_WORDS),
          .OUT_REGS (0)
        ) i_ram_user (
            .Clk_CI    ( clk_i                     ),
            .Rst_RBI   ( rst_ni                    ),
            .CSel_SI   ( req_i                     ),
            .WrEn_SI   ( we_i                      ),
            .BEn_SI    ( be_aligned[k*8 +: 8]      ),
            .WrData_DI ( wuser_aligned[k*64 +: 64] ),
            .Addr_DI   ( addr_i                    ),
            .RdData_DO ( ruser_aligned[k*64 +: 64] )
        );
      end
    end else begin : gen_mem
      // unused byte-enable segments (8bits) are culled by the tool
      tc_sram_wrapper #(
        .NumWords(NUM_WORDS),           // Number of Words in data array
        .DataWidth(64),                 // Data signal width
        .ByteWidth(32'd8),              // Width of a data byte
        .NumPorts(32'd1),               // Number of read and write ports
        .Latency(32'd1),                // Latency when the read data is available
        .SimInit(SIM_INIT),             // Simulation initialization
        .PrintSimCfg(1'b0)              // Print configuration
      ) i_tc_sram_wrapper (
          .clk_i    ( clk_i                     ),
          .rst_ni   ( rst_ni                    ),
          .req_i    ( req_i                     ),
          .we_i     ( we_i                      ),
          .be_i     ( be_aligned[k*8 +: 8]      ),
          .wdata_i  ( wdata_aligned[k*64 +: 64] ),
          .addr_i   ( addr_i                    ),
          .rdata_o  ( rdata_aligned[k*64 +: 64] )
      );
      if (USER_EN) begin : gen_mem_user
        tc_sram_wrapper #(
          .NumWords(NUM_WORDS),           // Number of Words in data array
          .DataWidth(64),                 // Data signal width
          .ByteWidth(32'd8),              // Width of a data byte
          .NumPorts(32'd1),               // Number of read and write ports
          .Latency(32'd1),                // Latency when the read data is available
          .SimInit(SIM_INIT),             // Simulation initialization
          .PrintSimCfg(1'b0)              // Print configuration
        ) i_tc_sram_wrapper_user (
            .clk_i    ( clk_i                     ),
            .rst_ni   ( rst_ni                    ),
            .req_i    ( req_i                     ),
            .we_i     ( we_i                      ),
            .be_i     ( be_aligned[k*8 +: 8]      ),
            .wdata_i  ( wuser_aligned[k*64 +: 64] ),
            .addr_i   ( addr_i                    ),
            .rdata_o  ( ruser_aligned[k*64 +: 64] )
        );
      end else begin
        assign ruser_aligned[k*64 +: 64] = '0;
      end
    end
  end
endmodule : sram

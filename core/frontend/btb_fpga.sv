// Copyright 2018 - 2019 ETH Zurich and University of Bologna.
// Copyright 2022 Thales Research and Technology
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 2.0 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-2.0. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// Author: Florian Zaruba, ETH Zurich
// Date: 08.02.2018
// Migrated: Luis Vitorio Cargnini, IEEE
// Date: 09.06.2018
//
//
// Additional contributions by:
//         Sebastien Jacq, Thales - sjthales on github.com
//         Date: 2022-12-01
//
// Description: This module is an adaptation of the BTB (Branch Target Buffer)
//              module for FPGA targets.
//              Prediction target address is stored in BRAM on FPGA while for
//              original module, target address is stored in D flip-flop.
//              Flushing is not supported because the front module flushing 
//              signal is not connected.


// branch target buffer for FPGA target
module btb_fpga #(
    parameter int NR_ENTRIES = 1024
)(
    input  logic                        clk_i,           // Clock
    input  logic                        rst_ni,          // Asynchronous reset active low
    input  logic                        flush_i,         // flush the btb --> not used
    input  logic                        debug_mode_i,

    input  logic [riscv::VLEN-1:0]      vpc_i,           // virtual PC from IF stage
    input  ariane_pkg::btb_update_t     btb_update_i,    // update btb with this information
    output ariane_pkg::btb_prediction_t [ariane_pkg::INSTR_PER_FETCH-1:0] btb_prediction_o // prediction from btb
);
    
    
    // the last bit is always zero, we don't need it for indexing
    localparam OFFSET = ariane_pkg::RVC == 1'b1 ? 1 : 2;
    // re-shape the branch history table
    localparam NR_ROWS = NR_ENTRIES / ariane_pkg::INSTR_PER_FETCH;
    // number of bits needed to index the row
    localparam ROW_ADDR_BITS = $clog2(ariane_pkg::INSTR_PER_FETCH);
    localparam ROW_INDEX_BITS = ariane_pkg::RVC == 1'b1 ? $clog2(ariane_pkg::INSTR_PER_FETCH) : 1;
    // number of bits we should use for prediction
    localparam PREDICTION_BITS = $clog2(NR_ROWS) + OFFSET + ROW_ADDR_BITS;
    // prevent aliasing to degrade performance
    localparam ANTIALIAS_BITS = 8;
    // number of bits par word in the bram 
    localparam BRAM_WORD_BITS = $bits(ariane_pkg::btb_prediction_t);
    
    // we are not interested in all bits of the address
    unread i_unread (.d_i(|vpc_i));

    logic [$clog2(NR_ROWS)-1:0]  index, update_pc;
    logic [ROW_INDEX_BITS-1:0]   update_row_index;
    
    logic [ariane_pkg::INSTR_PER_FETCH-1:0]                  btb_ram_csel_prediction;
    logic [ariane_pkg::INSTR_PER_FETCH-1:0]                  btb_ram_we_prediction;
    logic [ariane_pkg::INSTR_PER_FETCH*$clog2(NR_ROWS)-1:0]  btb_ram_addr_prediction;
    logic [ariane_pkg::INSTR_PER_FETCH*BRAM_WORD_BITS-1:0]   btb_ram_wdata_prediction; 
    logic [ariane_pkg::INSTR_PER_FETCH*BRAM_WORD_BITS-1:0]   btb_ram_rdata_prediction;
    
    logic [ariane_pkg::INSTR_PER_FETCH-1:0]                  btb_ram_csel_update;
    logic [ariane_pkg::INSTR_PER_FETCH-1:0]                  btb_ram_we_update;
    logic [ariane_pkg::INSTR_PER_FETCH*$clog2(NR_ROWS)-1:0]  btb_ram_addr_update;
    logic [ariane_pkg::INSTR_PER_FETCH*BRAM_WORD_BITS-1:0]   btb_ram_wdata_update; 

    
    assign index     = vpc_i[PREDICTION_BITS - 1:ROW_ADDR_BITS + OFFSET];
    assign update_pc = btb_update_i.pc[PREDICTION_BITS - 1:ROW_ADDR_BITS + OFFSET];
    if (ariane_pkg::RVC == 1'b1) begin
      assign update_row_index = btb_update_i.pc[ROW_ADDR_BITS + OFFSET - 1:OFFSET];
    end else begin
      assign update_row_index = '0;
    end
    
    // output matching prediction
    for (genvar i = 0; i < ariane_pkg::INSTR_PER_FETCH; i++) begin : gen_btb_output
      assign btb_ram_csel_prediction[i] = 1'b1;
      assign btb_ram_we_prediction[i] = 1'b0;
      assign btb_ram_wdata_prediction = '0;
      assign btb_ram_addr_prediction[i*$clog2(NR_ROWS) +: $clog2(NR_ROWS)] = index;
      assign btb_prediction_o[i] = btb_ram_rdata_prediction[i*BRAM_WORD_BITS +: BRAM_WORD_BITS];
    end
    
    // -------------------------
    // Update Branch Prediction
    // -------------------------
    // update on a mis-predict
    always_comb begin : update_branch_predict
      btb_ram_csel_update = '0;
      btb_ram_we_update = '0;
      btb_ram_addr_update = '0;
      btb_ram_wdata_update = '0;
        
      if (btb_update_i.valid && !debug_mode_i) begin
        for (int i = 0; i < ariane_pkg::INSTR_PER_FETCH; i++) begin
          if (update_row_index == i) begin
            btb_ram_csel_update[i] = 1'b1;
            btb_ram_we_update[i] = 1'b1;
            btb_ram_addr_update[i*$clog2(NR_ROWS) +: $clog2(NR_ROWS)] = update_pc;
            btb_ram_wdata_update[i*BRAM_WORD_BITS +: BRAM_WORD_BITS] = {1'b1 , btb_update_i.target_address};
          end
        end       
      end
    end
      
    for (genvar i = 0; i < ariane_pkg::INSTR_PER_FETCH; i++) begin : gen_btb_ram
      SyncDpRam #(
        .ADDR_WIDTH($clog2(NR_ROWS)),
        .DATA_DEPTH(NR_ROWS),
        .DATA_WIDTH(BRAM_WORD_BITS),
        .OUT_REGS (0),
        .SIM_INIT (1)
      ) i_btb_ram (
          .Clk_CI    ( clk_i                                                          ),
          .Rst_RBI   ( rst_ni                                                         ),
          //----------------------------
          .CSelA_SI   ( btb_ram_csel_update[i]                                        ),
          .WrEnA_SI   ( btb_ram_we_update[i]                                          ),
          .AddrA_DI   ( btb_ram_addr_update[i*$clog2(NR_ROWS) +: $clog2(NR_ROWS)]     ),
          .WrDataA_DI ( btb_ram_wdata_update[i*BRAM_WORD_BITS +: BRAM_WORD_BITS]      ),
          .RdDataA_DO (                                                               ),
          //-----------------------------
          .CSelB_SI   ( btb_ram_csel_prediction[i]                                    ),
          .WrEnB_SI   ( btb_ram_we_prediction[i]                                      ),
          .AddrB_DI   ( btb_ram_addr_prediction[i*$clog2(NR_ROWS) +: $clog2(NR_ROWS)] ),
          .WrDataB_DI ( btb_ram_wdata_prediction[i*BRAM_WORD_BITS +: BRAM_WORD_BITS]  ),
          .RdDataB_DO ( btb_ram_rdata_prediction[i*BRAM_WORD_BITS +: BRAM_WORD_BITS]  )
      );
    end    
endmodule

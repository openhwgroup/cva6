// Copyright 2018 - 2019 ETH Zurich and University of Bologna.
// Copyright 2023 - Thales for additionnal conribution.
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
// FPGA optimization: Sebastien Jacq, Thales
// Date: 2023-01-30

// branch history table - 2 bit saturation counter

module bht #(
    parameter int unsigned NR_ENTRIES = 1024
)(
    input  logic                        clk_i,
    input  logic                        rst_ni,
    input  logic                        flush_i,
    input  logic                        debug_mode_i,
    input  logic [riscv::VLEN-1:0]      vpc_i,
    input  ariane_pkg::bht_update_t     bht_update_i,
    // we potentially need INSTR_PER_FETCH predictions/cycle
    output ariane_pkg::bht_prediction_t [ariane_pkg::INSTR_PER_FETCH-1:0] bht_prediction_o
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
    // we are not interested in all bits of the address
    unread i_unread (.d_i(|vpc_i));

    struct packed {
        logic       valid;
        logic [1:0] saturation_counter;
    } bht_d[NR_ROWS-1:0][ariane_pkg::INSTR_PER_FETCH-1:0], bht_q[NR_ROWS-1:0][ariane_pkg::INSTR_PER_FETCH-1:0];

    logic [$clog2(NR_ROWS)-1:0]  index, update_pc;
    logic [ROW_INDEX_BITS-1:0]   update_row_index;

    assign index     = vpc_i[PREDICTION_BITS - 1:ROW_ADDR_BITS + OFFSET];
    assign update_pc = bht_update_i.pc[PREDICTION_BITS - 1:ROW_ADDR_BITS + OFFSET];
    if (ariane_pkg::RVC) begin : gen_update_row_index
      assign update_row_index = bht_update_i.pc[ROW_ADDR_BITS + OFFSET - 1:OFFSET];
    end else begin
      assign update_row_index = '0;
    end

    if (!ariane_pkg::FPGA_EN) begin : gen_asic_bht // ASIC TARGET

      logic [1:0] saturation_counter;
      // prediction assignment
      for (genvar i = 0; i < ariane_pkg::INSTR_PER_FETCH; i++) begin : gen_bht_output
        assign bht_prediction_o[i].valid = bht_q[index][i].valid;
        assign bht_prediction_o[i].taken = bht_q[index][i].saturation_counter[1] == 1'b1;
      end

      always_comb begin : update_bht
        bht_d = bht_q;
        saturation_counter = bht_q[update_pc][update_row_index].saturation_counter;

        if (bht_update_i.valid && !debug_mode_i) begin
          bht_d[update_pc][update_row_index].valid = 1'b1;

          if (saturation_counter == 2'b11) begin
            // we can safely decrease it
            if (!bht_update_i.taken)
              bht_d[update_pc][update_row_index].saturation_counter = saturation_counter - 1;
          // then check if it saturated in the negative regime e.g.: branch not taken
          end else if (saturation_counter == 2'b00) begin
            // we can safely increase it
            if (bht_update_i.taken)
              bht_d[update_pc][update_row_index].saturation_counter = saturation_counter + 1;
          end else begin // otherwise we are not in any boundaries and can decrease or increase it
            if (bht_update_i.taken)
              bht_d[update_pc][update_row_index].saturation_counter = saturation_counter + 1;
            else
              bht_d[update_pc][update_row_index].saturation_counter = saturation_counter - 1;
          end
        end
      end

      always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
          for (int unsigned i = 0; i < NR_ROWS; i++) begin
            for (int j = 0; j < ariane_pkg::INSTR_PER_FETCH; j++) begin
              bht_q[i][j] <= '0;
            end
          end
        end else begin
          // evict all entries
          if (flush_i) begin
            for (int i = 0; i < NR_ROWS; i++) begin
              for (int j = 0; j < ariane_pkg::INSTR_PER_FETCH; j++) begin
                bht_q[i][j].valid <=  1'b0;
                bht_q[i][j].saturation_counter <= 2'b10;
              end
            end
          end else begin
            bht_q <= bht_d;
          end
        end
      end

    end else begin : gen_fpga_bht //FPGA TARGETS

      // number of bits par word in the bram 
      localparam BRAM_WORD_BITS = $bits(ariane_pkg::bht_t);
      logic [ROW_INDEX_BITS-1:0]                                 row_index;
      logic [ariane_pkg::INSTR_PER_FETCH-1:0]                    bht_ram_we;
      logic [ariane_pkg::INSTR_PER_FETCH*$clog2(NR_ROWS)-1:0]    bht_ram_read_address_0;
      logic [ariane_pkg::INSTR_PER_FETCH*$clog2(NR_ROWS)-1:0]    bht_ram_read_address_1;
      logic [ariane_pkg::INSTR_PER_FETCH*$clog2(NR_ROWS)-1:0]    bht_ram_write_address;
      logic [ariane_pkg::INSTR_PER_FETCH*BRAM_WORD_BITS-1:0]     bht_ram_wdata;
      logic [ariane_pkg::INSTR_PER_FETCH*BRAM_WORD_BITS-1:0]     bht_ram_rdata_0;
      logic [ariane_pkg::INSTR_PER_FETCH*BRAM_WORD_BITS-1:0]     bht_ram_rdata_1;

      ariane_pkg::bht_t [ariane_pkg::INSTR_PER_FETCH-1:0]        bht;
      ariane_pkg::bht_t [ariane_pkg::INSTR_PER_FETCH-1:0]        bht_updated;

      if (ariane_pkg::RVC) begin : gen_row_index
        assign row_index        = vpc_i[ROW_ADDR_BITS + OFFSET - 1:OFFSET];
      end else begin
        assign row_index = '0;
      end

      // -------------------------
      // prediction assignment & update Branch History Table
      // -------------------------
      always_comb begin : prediction_update_bht
        bht_ram_we = '0;
        bht_ram_read_address_0 = '0;
        bht_ram_read_address_1 = '0;
        bht_ram_write_address = '0;
        bht_ram_wdata ='0;
        bht_updated = '0;
        bht = '0;

        for (int i = 0; i < ariane_pkg::INSTR_PER_FETCH; i++) begin
          if (row_index == i) begin
            bht_ram_read_address_0[i*$clog2(NR_ROWS) +: $clog2(NR_ROWS)] = index;
            bht_prediction_o[i].valid = bht_ram_rdata_0[i*BRAM_WORD_BITS+2] ;
            bht_prediction_o[i].taken = bht_ram_rdata_0[i*BRAM_WORD_BITS+1] ;
          end
        end

        if (bht_update_i.valid && !debug_mode_i) begin
          for (int i = 0; i < ariane_pkg::INSTR_PER_FETCH; i++) begin
            if (update_row_index == i) begin
              bht_ram_read_address_1[i*$clog2(NR_ROWS) +: $clog2(NR_ROWS)] = update_pc;
              bht[i].saturation_counter = bht_ram_rdata_1[i*BRAM_WORD_BITS +: 2];
            
              if (bht[i].saturation_counter == 2'b11) begin
                // we can safely decrease it
                if (!bht_update_i.taken)
                  bht_updated[i].saturation_counter = bht[i].saturation_counter - 1;
                else
                  bht_updated[i].saturation_counter = 2'b11;
              // then check if it saturated in the negative regime e.g.: branch not taken
              end else if (bht[i].saturation_counter == 2'b00) begin
                // we can safely increase it
                if (bht_update_i.taken)
                  bht_updated[i].saturation_counter = bht[i].saturation_counter + 1;
                else
                  bht_updated[i].saturation_counter = 2'b00;
              end else begin // otherwise we are not in any boundaries and can decrease or increase it
                if (bht_update_i.taken)
                  bht_updated[i].saturation_counter = bht[i].saturation_counter + 1;
                else
                  bht_updated[i].saturation_counter = bht[i].saturation_counter - 1;
              end
            
              bht_updated[i].valid = 1'b1;
              bht_ram_we[i] = 1'b1;
              bht_ram_write_address[i*$clog2(NR_ROWS) +: $clog2(NR_ROWS)] = update_pc;
              //bht_ram_wdata[(i+1)*BRAM_WORD_BITS-1] =  1'b1; //valid
              bht_ram_wdata[i*BRAM_WORD_BITS +: BRAM_WORD_BITS] =  {bht_updated[i].valid , bht_updated[i].saturation_counter}; 
            
            end
          end
        end
      end

      for (genvar i = 0; i < ariane_pkg::INSTR_PER_FETCH; i++) begin : gen_bht_ram
        AsyncThreePortRam #(
          .ADDR_WIDTH($clog2(NR_ROWS)),
          .DATA_DEPTH (NR_ROWS),
          .DATA_WIDTH(BRAM_WORD_BITS)
        ) i_bht_ram (
          .Clk_CI       ( clk_i                                                        ),  
          .WrEn_SI      ( bht_ram_we[i]                                                ),
          .WrAddr_DI    ( bht_ram_write_address[i*$clog2(NR_ROWS) +: $clog2(NR_ROWS)]  ),
          .WrData_DI    ( bht_ram_wdata[i*BRAM_WORD_BITS +: BRAM_WORD_BITS]            ),
          .RdAddr_DI_0  ( bht_ram_read_address_0[i*$clog2(NR_ROWS) +: $clog2(NR_ROWS)] ),
          .RdAddr_DI_1  ( bht_ram_read_address_1[i*$clog2(NR_ROWS) +: $clog2(NR_ROWS)] ),
          .RdData_DO_0  ( bht_ram_rdata_0[i*BRAM_WORD_BITS +: BRAM_WORD_BITS]          ),
          .RdData_DO_1  ( bht_ram_rdata_1[i*BRAM_WORD_BITS +: BRAM_WORD_BITS]          )
        );
      end

    end
endmodule

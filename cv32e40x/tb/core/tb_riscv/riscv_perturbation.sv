// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

//////////////////////////////////////////////////////////////////////////////////////////////
//                                                                                          //
// Author:                      Francesco Minervini - minervif@student.ethz.ch              //
//                                                                                          //
// Additional contributions by:                                                             //
// Design Name:                 Perturbation Unit                                           //
// Project Name:                RI5CY, Zeroriscy                                            //
// Language:                    SystemVerilog                                               //
//                                                                                          //
// Description:                 This module instantiates both data and instructions stalls  //
//                              generators as well as the random interrupt generator        //
//                                                                                          //
//////////////////////////////////////////////////////////////////////////////////////////////

import riscv_defines::*;
`include "riscv_config.sv"

module riscv_perturbation
#(
    parameter PERT_REGS         = 15,
    parameter INSTR_RDATA_WIDTH = 32
)

(
    input logic                             rst_ni,
    input logic                             clk_i,

    //Instruction interface
    input logic                             pert_instr_req_i,
    output logic                            pert_instr_req_o,
    input logic                             pert_instr_grant_i,
    output logic                            pert_instr_grant_o,
    input logic                             pert_instr_rvalid_i,
    output logic                            pert_instr_rvalid_o,
    input logic  [31:0]                     pert_instr_addr_i,
    output logic [31:0]                     pert_instr_addr_o,
    input logic  [INSTR_RDATA_WIDTH-1:0]    pert_instr_rdata_i,
    output logic [INSTR_RDATA_WIDTH-1:0]    pert_instr_rdata_o,

    //Data interface
    input logic                             pert_data_req_i,
    output logic                            pert_data_req_o,
    input logic                             pert_data_grant_i,
    output logic                            pert_data_grant_o,
    input logic                             pert_data_rvalid_i,
    output logic                            pert_data_rvalid_o,
    input logic                             pert_data_we_i,
    output logic                            pert_data_we_o,
    input logic  [3:0]                      pert_data_be_i,
    output logic [3:0]                      pert_data_be_o,
    input logic  [31:0]                     pert_data_addr_i,
    output logic [31:0]                     pert_data_addr_o,
    input logic  [31:0]                     pert_data_wdata_i,
    output logic [31:0]                     pert_data_wdata_o,
    input logic  [INSTR_RDATA_WIDTH-1:0]    pert_data_rdata_i,
    output logic [INSTR_RDATA_WIDTH-1:0]    pert_data_rdata_o,

    //Debug-perturbation interface
    input logic                             pert_debug_req_i,
    output logic                            pert_debug_req_o,
    input logic                             pert_debug_gnt_i,
    output logic                            pert_debug_gnt_o,
    input logic                             pert_debug_rvalid_i,
    output logic                            pert_debug_rvalid_o,
    input logic                             pert_debug_we_i,
    output logic                            pert_debug_we_o,
    input logic  [14:0]                     pert_debug_addr_i,
    output logic [14:0]                     pert_debug_addr_o,
    input logic  [31:0]                     pert_debug_wdata_i,
    output logic [31:0]                     pert_debug_wdata_o,
    input logic  [31:0]                     pert_debug_rdata_i,
    output logic [31:0]                     pert_debug_rdata_o,

    //Interrupt interface
    input logic                             pert_irq_i,
    output logic                            pert_irq_o,
    input logic   [4:0]                     pert_irq_id_i,
    output logic  [4:0]                     pert_irq_id_o,
    input logic                             pert_irq_ack_i,
    output logic                            pert_irq_ack_o,
    input logic   [4:0]                     pert_irq_core_resp_id_i,
    output logic  [4:0]                     pert_irq_core_resp_id_o,
    input logic  [31:0]                     pert_pc_id_i
    );

  logic [31:0]       pert_regs [0:PERT_REGS-1];
  logic [3:0]        pert_addr_int;
  logic [31:0]      irq_act_id_int;
  logic                  irq_id_resp_we_i;
  //Signals for instruction stalls generator
  logic [31:0] pert_instr_mode, pert_instr_max_stall, pert_instr_grant_stall, pert_instr_valid_stall;
  //Signals for data stalls generator
  logic [31:0] pert_data_mode, pert_data_max_stall, pert_data_grant_stall, pert_data_valid_stall;
  //Signals for interrupt generator
  logic [31:0] pert_irq_mode, pert_irq_min_cycles, pert_irq_max_cycles, pert_irq_min_id, pert_irq_max_id, pert_irq_pc_trig;

  logic is_perturbation;

  riscv_random_stall instr_random_stalls
  (
    .clk_i               ( clk_i                                ),
    .rst_ni              ( rst_ni                               ),

    .grant_per_i         ( pert_instr_grant_i                   ),
    .grant_per_o         ( pert_instr_grant_o                   ),

    .rvalid_per_i        ( pert_instr_rvalid_i                  ),
    .rvalid_per_o        ( pert_instr_rvalid_o                  ),

    .rdata_per_i         ( pert_instr_rdata_i                   ),
    .rdata_per_o         ( pert_instr_rdata_o                   ),

    .req_per_i           ( pert_instr_req_i                     ),
    .req_mem_o           ( pert_instr_req_o                     ),

    .addr_per_i          ( pert_instr_addr_i                    ),
    .addr_mem_o          ( pert_instr_addr_o                    ),

    .wdata_per_i         (                                      ),
    .wdata_mem_o         (                                      ),

    .we_per_i            (                                      ),
    .we_mem_o            (                                      ),

    .be_per_i            (                                      ),
    .be_mem_o            (                                      ),

    .dbg_req_i           ( pert_debug_req_i                     ),
    .dbg_we_i            ( pert_debug_we_i                      ),

    .dbg_mode_i          ( pert_instr_mode                      ),
    .dbg_max_stall_i     ( pert_instr_max_stall                 ),

    .dbg_gnt_stall_i     ( pert_instr_grant_stall               ),
    .dbg_valid_stall_i   ( pert_instr_valid_stall               )
  );

  riscv_random_stall data_random_stalls
  (
    .clk_i               ( clk_i                                ),
    .rst_ni              ( rst_ni                               ),

    .grant_per_i         ( pert_data_grant_i                    ),
    .grant_per_o         ( pert_data_grant_o                    ),

    .rvalid_per_i        ( pert_data_rvalid_i                   ),
    .rvalid_per_o        ( pert_data_rvalid_o                   ),

    .rdata_per_i         ( pert_data_rdata_i                    ),
    .rdata_per_o         ( pert_data_rdata_o                    ),

    .req_per_i           ( pert_data_req_i                      ),
    .req_mem_o           ( pert_data_req_o                      ),

    .addr_per_i          ( pert_data_addr_i                     ),
    .addr_mem_o          ( pert_data_addr_o                     ),

    .wdata_per_i         ( pert_data_wdata_i                    ),
    .wdata_mem_o         ( pert_data_wdata_o                    ),

    .we_per_i            ( pert_data_we_i                       ),
    .we_mem_o            ( pert_data_we_o                       ),

    .be_per_i            ( pert_data_be_i                       ),
    .be_mem_o            ( pert_data_be_o                       ),

    .dbg_req_i           ( pert_debug_req_i                     ),
    .dbg_we_i            ( pert_debug_we_i                      ),

    .dbg_mode_i          ( pert_data_mode                       ),
    .dbg_max_stall_i     ( pert_data_max_stall                  ),

    .dbg_gnt_stall_i     ( pert_data_grant_stall                ),
    .dbg_valid_stall_i   ( pert_data_valid_stall                )
  );


  riscv_random_interrupt_generator riscv_random_interrupt_generator_i
  (
    .rst_ni                   ( rst_ni                          ),
    .clk_i                    ( clk_i                           ),
    .irq_i                    ( pert_irq_i                      ),
    .irq_id_i                 ( pert_irq_id_i                   ),
    .irq_ack_i                ( pert_irq_ack_i                  ),
    .irq_ack_o                ( pert_irq_ack_o                  ),
    .irq_o                    ( pert_irq_o                      ),
    .irq_id_o                 ( pert_irq_id_o                   ),
    .irq_mode_i               ( pert_irq_mode                   ),
    .irq_min_cycles_i         ( pert_irq_min_cycles             ),
    .irq_max_cycles_i         ( pert_irq_max_cycles             ),
    .irq_min_id_i             ( pert_irq_min_id                 ),
    .irq_max_id_i             ( pert_irq_max_id                 ),
    .irq_act_id_o             ( irq_act_id_int                  ),
    .irq_id_we_o              ( irq_id_resp_we_i                ),
    .irq_pc_id_i              ( pert_pc_id_i                    ),
    .irq_pc_trig_i            ( pert_irq_pc_trig                )
    );

assign pert_addr_int = pert_debug_addr_i[5:2];

assign is_perturbation = pert_debug_addr_i[13:8] == 6'b000110;

always_ff @(posedge clk_i or negedge rst_ni) begin
    if(~rst_ni) begin
        for(int i=0; i<PERT_REGS; i++) begin
            pert_regs[i] <= '0;
        end

        pert_debug_req_o   <=   1'b0;
        pert_debug_we_o    <=   1'b0;
        pert_debug_addr_o  <=     '0;
        pert_debug_wdata_o <=     '0;
        pert_debug_rdata_o <=     'z;

    end else begin  //No reset

        if(pert_debug_req_i) begin

            if(is_perturbation) begin //Perturbation registers address space

                if(pert_debug_we_i) begin //Write operation
                    pert_regs[pert_addr_int] <= pert_debug_wdata_i;

                end else begin  //Read opeartion
                    pert_debug_rdata_o <= pert_regs[pert_addr_int];

                end

            end else begin
                pert_debug_req_o   <= pert_debug_req_i;
                pert_debug_we_o    <= pert_debug_we_i;
                pert_debug_wdata_o <= pert_debug_wdata_i;
                pert_debug_addr_o  <= pert_debug_addr_i;
                pert_debug_rdata_o <= pert_debug_rdata_i;
            end

        end else begin  //No debug requests
            pert_debug_req_o   <=   1'b0;
            pert_debug_we_o    <=   1'b0;
            pert_debug_addr_o  <=     '0;
            pert_debug_wdata_o <=     '0;
            pert_debug_rdata_o <=     '0;
        end

    end
end //always_ff


always_comb begin  //Grant generation
    pert_debug_gnt_o = 1'b0;
    if(pert_debug_req_i) begin

        if(is_perturbation) begin  //Grant the access to perturbation regs
            pert_debug_gnt_o = 1'b1;

        end else begin
            pert_debug_gnt_o = pert_debug_gnt_i;
        end

    end else begin  //No requests
        pert_debug_gnt_o = 1'b0;
    end

end //always_comb


always_ff @(posedge clk_i or negedge rst_ni) begin //Valid generation
    if(~rst_ni) begin
        pert_debug_rvalid_o <= 1'b0;

    end else begin
        if(is_perturbation) begin
            pert_debug_rvalid_o <= pert_debug_gnt_o;

        end else begin
            pert_debug_rvalid_o <= pert_debug_rvalid_i;
        end
    end
end //always_ff


always_ff @(posedge clk_i or negedge rst_ni) begin
    if(rst_ni) begin
        if(irq_id_resp_we_i) begin
            pert_regs[13]           <= pert_irq_core_resp_id_i;
            pert_irq_core_resp_id_o <= pert_irq_core_resp_id_i;
        end else begin
            pert_irq_core_resp_id_o <= pert_irq_core_resp_id_i;
        end
    end
end

//Fixed assignments
assign pert_data_mode             =  pert_regs[0];
assign pert_data_max_stall        =  pert_regs[1];
assign pert_data_grant_stall      =  pert_regs[2];
assign pert_data_valid_stall      =  pert_regs[3];
assign pert_instr_mode            =  pert_regs[4];
assign pert_instr_max_stall       =  pert_regs[5];
assign pert_instr_grant_stall     =  pert_regs[6];
assign pert_instr_valid_stall     =  pert_regs[7];
assign pert_irq_mode              =  pert_regs[8];
assign pert_irq_min_cycles        =  pert_regs[9];
assign pert_irq_max_cycles        =  pert_regs[10];
assign pert_irq_min_id            =  pert_regs[11];
assign pert_irq_max_id            =  pert_regs[12];
//Register 13 is written by the interrupt generator
assign pert_irq_pc_trig           =  pert_regs[14];



endmodule
//
// Copyright 2020 OpenHW Group
// Copyright 2020 Datum Technologies
// 
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
// 
//     https://solderpad.org/licenses/
// 
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
// 
///////////////////////////////////////////////////////////////////////////////
//
// Modified version of the wrapper for a RI5CY testbench, containing RI5CY,
// plus Memory and stdout virtual peripherals.
// Contributor: Robert Balas <balasr@student.ethz.ch>
// Copyright 2018 Robert Balas <balasr@student.ethz.ch>
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//


`ifndef __UVMT_CV32_DUT_WRAP_SV__
`define __UVMT_CV32_DUT_WRAP_SV__


/**
 * Module wrapper for CV32 RTL DUT.
 */
module uvmt_cv32_dut_wrap #(parameter INSTR_RDATA_WIDTH =  128,
                                      RAM_ADDR_WIDTH    =   20,
                                      PULP_SECURE       =    1
                           )
                           (
                            uvmt_cv32_clk_gen_if         clk_gen_if,
                            uvmt_cv32_vp_status_if       vp_status_if,
                            uvmt_cv32_core_cntrl_if      core_cntrl_if,
                            uvmt_cv32_core_status_if     core_status_if,
                            uvmt_cv32_core_interrupts_if core_interrupts_if
                           );

    // signals connecting core to memory
    logic                         instr_req;
    logic                         instr_gnt;
    logic                         instr_rvalid;
    logic [31:0]                  instr_addr;
    logic [INSTR_RDATA_WIDTH-1:0] instr_rdata;

    logic                         data_req;
    logic                         data_gnt;
    logic                         data_rvalid;
    logic [31:0]                  data_addr;
    logic                         data_we;
    logic [3:0]                   data_be;
    logic [31:0]                  data_rdata;
    logic [31:0]                  data_wdata;

    // signals to debug unit
    logic                         debug_req_i;

    assign debug_req_i = 1'b0;

    // instantiate the core
    riscv_core #(.INSTR_RDATA_WIDTH (INSTR_RDATA_WIDTH),
                 .PULP_SECURE       (PULP_SECURE),
                 .FPU               (0)
                )
    riscv_core_i
        (
         .clk_i                  ( clk_gen_if.core_clock          ),
         .rst_ni                 ( clk_gen_if.core_reset_n        ),

         .clock_en_i             ( core_cntrl_if.clock_en         ),
         .test_en_i              ( core_cntrl_if.test_en          ),

         .boot_addr_i            ( core_cntrl_if.boot_addr        ),
         .core_id_i              ( core_cntrl_if.core_id          ),
         .cluster_id_i           ( core_cntrl_if.cluster_id       ),

         .instr_addr_o           ( instr_addr                     ),
         .instr_req_o            ( instr_req                      ),
         .instr_rdata_i          ( instr_rdata                    ),
         .instr_gnt_i            ( instr_gnt                      ),
         .instr_rvalid_i         ( instr_rvalid                   ),

         .data_addr_o            ( data_addr                      ),
         .data_wdata_o           ( data_wdata                     ),
         .data_we_o              ( data_we                        ),
         .data_req_o             ( data_req                       ),
         .data_be_o              ( data_be                        ),
         .data_rdata_i           ( data_rdata                     ),
         .data_gnt_i             ( data_gnt                       ),
         .data_rvalid_i          ( data_rvalid                    ),

         .apu_master_req_o       (                                ),
         .apu_master_ready_o     (                                ),
         .apu_master_gnt_i       (                                ),
         .apu_master_operands_o  (                                ),
         .apu_master_op_o        (                                ),
         .apu_master_type_o      (                                ),
         .apu_master_flags_o     (                                ),
         .apu_master_valid_i     (                                ),
         .apu_master_result_i    (                                ),
         .apu_master_flags_i     (                                ),

         // TODO: interrupts significantly updated for CV32E40P
         //       Connect all interrupt signals to an SV interface
         //       and pass to ENV for an INTERRUPT AGENT to drive/monitor.
         //.irq_i                  ( irq                            ),
         //.irq_id_i               ( irq_id_in                      ),
         .irq_ack_o              ( irq_ack                           ),
         .irq_id_o               ( irq_id_out                        ),
         .irq_sec_i              ( (core_interrupts_if.irq_sec||irq) ),
         .irq_software_i         ( core_interrupts_if.irq_software   ),
         .irq_timer_i            ( core_interrupts_if.irq_timer      ),
         .irq_external_i         ( core_interrupts_if.irq_external   ),
         .irq_fast_i             ( core_interrupts_if.irq_fast       ),
         .irq_nmi_i              ( core_interrupts_if.irq_nmi        ),
         .irq_fastx_i            ( core_interrupts_if.irq_fastx      ),

         .sec_lvl_o              ( core_status_if.sec_lvl            ),

         .debug_req_i            ( core_cntrl_if.debug_req           ),

         .fetch_enable_i         ( core_cntrl_if.fetch_en            ),
         .core_busy_o            ( core_status_if.core_busy          ),

         .ext_perf_counters_i    ( core_cntrl_if.ext_perf_counters   ),
         .fregfile_disable_i     ( core_cntrl_if.fregfile_disable    )
        ); //riscv_core_i

    // this handles read to RAM and memory mapped virtual (pseudo) peripherals
    mm_ram #(.RAM_ADDR_WIDTH    (RAM_ADDR_WIDTH),
             .INSTR_RDATA_WIDTH (INSTR_RDATA_WIDTH)
            )
    ram_i
        (.clk_i          ( clk_gen_if.core_clock          ),
         .rst_ni         ( clk_gen_if.core_reset_n        ),

         .instr_req_i    ( instr_req                      ),
         .instr_addr_i   ( instr_addr[RAM_ADDR_WIDTH-1:0] ),
         .instr_rdata_o  ( instr_rdata                    ),
         .instr_rvalid_o ( instr_rvalid                   ),
         .instr_gnt_o    ( instr_gnt                      ),

         .data_req_i     ( data_req                       ),
         .data_addr_i    ( data_addr                      ),
         .data_we_i      ( data_we                        ),
         .data_be_i      ( data_be                        ),
         .data_wdata_i   ( data_wdata                     ),
         .data_rdata_o   ( data_rdata                     ),
         .data_rvalid_o  ( data_rvalid                    ),
         .data_gnt_o     ( data_gnt                       ),

         .irq_id_i       ( irq_id_out                     ),
         .irq_ack_i      ( irq_ack                        ),
         .irq_id_o       ( irq_id_in                      ),
         .irq_o          ( irq                            ),

         .pc_core_id_i   ( riscv_core_i.pc_id             ),

         .tests_passed_o ( vp_status_if.tests_passed      ),
         .tests_failed_o ( vp_status_if.tests_failed      ),
         .exit_valid_o   ( vp_status_if.exit_valid        ),
         .exit_value_o   ( vp_status_if.exit_value        )
        ); //ram_i

endmodule : uvmt_cv32_dut_wrap

`endif // __UVMT_CV32_DUT_WRAP_SV__


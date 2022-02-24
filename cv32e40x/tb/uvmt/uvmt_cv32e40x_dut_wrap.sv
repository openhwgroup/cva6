//
// Copyright 2020 OpenHW Group
// Copyright 2020 Datum Technology Corporation
// Copyright 2020 Silicon Labs, Inc.
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


`ifndef __UVMT_CV32E40X_DUT_WRAP_SV__
`define __UVMT_CV32E40X_DUT_WRAP_SV__


/**
 * Module wrapper for CV32E40X RTL DUT.
 */
module uvmt_cv32e40x_dut_wrap
  import cv32e40x_pkg::*;

  #(// DUT (riscv_core) parameters.
    parameter NUM_MHPMCOUNTERS    =  1,
    parameter cv32e40x_pkg::b_ext_e B_EXT  = cv32e40x_pkg::B_NONE,
    parameter int          PMA_NUM_REGIONS =  0,
    parameter pma_region_t PMA_CFG[PMA_NUM_REGIONS-1 : 0] = '{default:PMA_R_DEFAULT},
    // Remaining parameters are used by TB components only
              INSTR_ADDR_WIDTH    =  32,
              INSTR_RDATA_WIDTH   =  32,
              RAM_ADDR_WIDTH      =  20
   )
  (
    uvma_clknrst_if              clknrst_if,
    uvma_interrupt_if            interrupt_if,
    uvmt_cv32e40x_vp_status_if   vp_status_if,
    uvme_cv32e40x_core_cntrl_if  core_cntrl_if,
    uvmt_cv32e40x_core_status_if core_status_if,
    uvma_obi_memory_if           obi_instr_if_i,
    uvma_obi_memory_if           obi_data_if_i,
    uvma_fencei_if               fencei_if_i
  );

    import uvm_pkg::*; // needed for the UVM messaging service (`uvm_info(), etc.)

    // signals connecting core to memory
    logic                         instr_req;
    logic                         instr_gnt;
    logic                         instr_rvalid;
    logic [INSTR_ADDR_WIDTH-1 :0] instr_addr;
    logic [INSTR_RDATA_WIDTH-1:0] instr_rdata;

    logic                         data_req;
    logic                         data_gnt;
    logic                         data_rvalid;
    logic [31:0]                  data_addr;
    logic                         data_we;
    logic [3:0]                   data_be;
    logic [31:0]                  data_rdata;
    logic [31:0]                  data_wdata;

    logic [31:0]                  irq;

    logic                         debug_havereset;
    logic                         debug_running;
    logic                         debug_halted;

    // eXtension interface
    // todo: Connect to TB when implemented.
    // Included to allow core-v-verif to compile with RTL including
    // interface definition.
    if_xif xif();

    assign debug_if.clk      = clknrst_if.clk;
    assign debug_if.reset_n  = clknrst_if.reset_n;

    // --------------------------------------------
    // OBI Instruction agent v1.2 signal tie-offs
    assign obi_instr_if_i.we        = 'b0;
    assign obi_instr_if_i.be        = 'hf; // Always assumes 32-bit full bus reads on instruction OBI
    assign obi_instr_if_i.auser     = 'b0;
    assign obi_instr_if_i.wuser     = 'b0;
    assign obi_instr_if_i.aid       = 'b0;
    assign obi_instr_if_i.atop      = 'b0;
    assign obi_instr_if_i.wdata     = 'b0;
    assign obi_instr_if_i.reqpar    = ~obi_instr_if_i.req;
    assign obi_instr_if_i.achk      = 'b0;
    assign obi_instr_if_i.rchk      = 'b0;
    assign obi_instr_if_i.rready    = 1'b1;
    assign obi_instr_if_i.rreadypar = 1'b0;

    // --------------------------------------------
    // OBI Data agent v12.2 signal tie-offs
    assign obi_data_if_i.auser      = 'b0;
    assign obi_data_if_i.wuser      = 'b0;
    assign obi_data_if_i.aid        = 'b0;
    assign obi_data_if_i.reqpar     = ~obi_data_if_i.req;
    assign obi_data_if_i.achk       = 'b0;
    assign obi_data_if_i.rchk       = 'b0;
    assign obi_data_if_i.rready     = 1'b1;
    assign obi_data_if_i.rreadypar  = 1'b0;

    // --------------------------------------------
    // Connect to uvma_interrupt_if
    assign interrupt_if.clk                     = clknrst_if.clk;
    assign interrupt_if.reset_n                 = clknrst_if.reset_n;
    assign interrupt_if.irq_id                  = cv32e40x_wrapper_i.core_i.irq_id;
    assign interrupt_if.irq_ack                 = cv32e40x_wrapper_i.core_i.irq_ack;

    // --------------------------------------------
    // Connect to core_cntrl_if
    assign core_cntrl_if.num_mhpmcounters = NUM_MHPMCOUNTERS;
    assign core_cntrl_if.b_ext = B_EXT;
    initial begin
      core_cntrl_if.pma_cfg = new[PMA_NUM_REGIONS];
      foreach (core_cntrl_if.pma_cfg[i]) begin
        core_cntrl_if.pma_cfg[i].word_addr_low  = PMA_CFG[i].word_addr_low;
        core_cntrl_if.pma_cfg[i].word_addr_high = PMA_CFG[i].word_addr_high;
        core_cntrl_if.pma_cfg[i].main           = PMA_CFG[i].main;
        core_cntrl_if.pma_cfg[i].bufferable     = PMA_CFG[i].bufferable;
        core_cntrl_if.pma_cfg[i].cacheable      = PMA_CFG[i].cacheable;
        core_cntrl_if.pma_cfg[i].atomic         = PMA_CFG[i].atomic;
      end
    end

    // --------------------------------------------
    // instantiate the core
    cv32e40x_wrapper #(
                      .NUM_MHPMCOUNTERS (NUM_MHPMCOUNTERS),
                      .B_EXT            (B_EXT),
                      .PMA_NUM_REGIONS  (PMA_NUM_REGIONS),
                      .PMA_CFG          (PMA_CFG)
                      )
    cv32e40x_wrapper_i
        (
         .clk_i                  ( clknrst_if.clk                 ),
         .rst_ni                 ( clknrst_if.reset_n             ),

         .scan_cg_en_i           ( core_cntrl_if.scan_cg_en       ),

         .boot_addr_i            ( core_cntrl_if.boot_addr        ),
         .mtvec_addr_i           ( core_cntrl_if.mtvec_addr       ),
         .dm_halt_addr_i         ( core_cntrl_if.dm_halt_addr     ),
         .nmi_addr_i             ( core_cntrl_if.nmi_addr         ),
         .mhartid_i              ( core_cntrl_if.mhartid          ),
         .mimpid_i               ( core_cntrl_if.mimpid           ),
         .dm_exception_addr_i    ( core_cntrl_if.dm_exception_addr),

         .instr_req_o            ( obi_instr_if_i.req             ),
         .instr_gnt_i            ( obi_instr_if_i.gnt             ),
         .instr_addr_o           ( obi_instr_if_i.addr            ),
         .instr_prot_o           ( obi_instr_if_i.prot            ),
         .instr_dbg_o            ( /* obi_instr_if_i.dbg */       ), // todo: Support OBI 1.3
         .instr_memtype_o        ( obi_instr_if_i.memtype         ),
         .instr_rdata_i          ( obi_instr_if_i.rdata           ),
         .instr_rvalid_i         ( obi_instr_if_i.rvalid          ),
         .instr_err_i            ( obi_instr_if_i.err             ),

         .data_req_o             ( obi_data_if_i.req              ),
         .data_gnt_i             ( obi_data_if_i.gnt              ),
         .data_rvalid_i          ( obi_data_if_i.rvalid           ),
         .data_we_o              ( obi_data_if_i.we               ),
         .data_be_o              ( obi_data_if_i.be               ),
         .data_addr_o            ( obi_data_if_i.addr             ),
         .data_wdata_o           ( obi_data_if_i.wdata            ),
         .data_prot_o            ( obi_data_if_i.prot             ),
         .data_dbg_o             ( /* obi_data_if_i.dbg */        ), // todo: Support OBI 1.3
         .data_memtype_o         ( obi_data_if_i.memtype          ),
         .data_rdata_i           ( obi_data_if_i.rdata            ),
         .data_atop_o            ( obi_data_if_i.atop             ),
         .data_err_i             ( obi_data_if_i.err              ),
         .data_exokay_i          ( obi_data_if_i.exokay           ),

         .mcycle_o               (      /*todo: connect */        ),

         .xif_compressed_if      ( xif.cpu_compressed             ),
         .xif_issue_if           ( xif.cpu_issue                  ),
         .xif_commit_if          ( xif.cpu_commit                 ),
         .xif_mem_if             ( xif.cpu_mem                    ),
         .xif_mem_result_if      ( xif.cpu_mem_result             ),
         .xif_result_if          ( xif.cpu_result                 ),

         .irq_i                  ( interrupt_if.irq               ),

         .clic_irq_i             ( '0   /*todo: connect */        ),
         .clic_irq_id_i          ( '0   /*todo: connect */        ),
         .clic_irq_il_i          ( '0   /*todo: connect */        ),
         .clic_irq_priv_i        ( '0   /*todo: connect */        ),
         .clic_irq_hv_i          ( '0   /*todo: connect */        ),
         .clic_irq_id_o          (      /*todo: connect */        ),
         .clic_irq_mode_o        (      /*todo: connect */        ),
         .clic_irq_exit_o        (      /*todo: connect */        ),

         .fencei_flush_req_o     ( fencei_if_i.flush_req          ),
         .fencei_flush_ack_i     ( fencei_if_i.flush_ack          ),

         .debug_req_i            ( debug_if.debug_req             ),
         .debug_havereset_o      ( debug_havereset                ),
         .debug_running_o        ( debug_running                  ),
         .debug_halted_o         ( debug_halted                   ),

         .fetch_enable_i         ( core_cntrl_if.fetch_en         ),
         .core_sleep_o           ( core_status_if.core_busy       )
        );

endmodule : uvmt_cv32e40x_dut_wrap

`endif // __UVMT_CV32E40X_DUT_WRAP_SV__

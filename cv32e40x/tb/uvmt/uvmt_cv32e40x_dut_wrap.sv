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
    parameter int unsigned PMA_NUM_REGIONS =  0,
    parameter pma_region_t PMA_CFG[(PMA_NUM_REGIONS ? (PMA_NUM_REGIONS-1) : 0):0] = '{default:PMA_R_DEFAULT},
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
    uvma_obi_memory_if           obi_data_if_i
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
    logic                         irq_ack;
    logic [ 4:0]                  irq_id;

    logic                         debug_havereset;
    logic                         debug_running;
    logic                         debug_halted;

    assign debug_if.clk      = clknrst_if.clk;
    assign debug_if.reset_n  = clknrst_if.reset_n;

    // Load the Instruction Memory 
    // initial begin: load_instruction_memory
    //   string firmware;
    //   int    fd;
    //    int   fill_cnt;
    //    bit [7:0] rnd_byte;
    //   `uvm_info("DUT_WRAP", "waiting for load_instr_mem to be asserted.", UVM_DEBUG)
    //   wait(core_cntrl_if.load_instr_mem !== 1'bX);
    //   if(core_cntrl_if.load_instr_mem === 1'b1) begin
    //     `uvm_info("DUT_WRAP", "load_instr_mem asserted!", UVM_NONE)

    //     // Load the pre-compiled firmware
    //     if($value$plusargs("firmware=%s", firmware)) begin
    //       // First, check if it exists...
    //       fd = $fopen (firmware, "r");   
    //       if (fd)  `uvm_info ("DUT_WRAP", $sformatf("%s was opened successfully : (fd=%0d)", firmware, fd), UVM_DEBUG)
    //       else     `uvm_fatal("DUT_WRAP", $sformatf("%s was NOT opened successfully : (fd=%0d)", firmware, fd))
    //       $fclose(fd);
    //       // Now load it...
    //       `uvm_info("DUT_WRAP", $sformatf("loading firmware %0s", firmware), UVM_NONE)
    //       $readmemh(firmware, uvmt_cv32e40x_tb.dut_wrap.ram_i.dp_ram_i.mem);
    //       // Initialize RTL and ISS memory with (the same) random value to
    //       // prevent X propagation through the core RTL.
    //       fill_cnt = 0;
    //       for (int index=0; index < 2**RAM_ADDR_WIDTH; index++) begin
    //          if (uvmt_cv32e40x_tb.dut_wrap.ram_i.dp_ram_i.mem[index] === 8'hXX) begin
    //             fill_cnt++;
    //             rnd_byte = $random();
    //             uvmt_cv32e40x_tb.dut_wrap.ram_i.dp_ram_i.mem[index]=rnd_byte;
    //             if ($test$plusargs("USE_ISS")) begin
    //               uvmt_cv32e40x_tb.iss_wrap.ram.memory.mem[index/4][((((index%4)+1)*8)-1)-:8]=rnd_byte; // convert byte to 32-bit addressing
    //             end
    //          end
    //       end
    //       if ($test$plusargs("USE_ISS")) begin
    //          `uvm_info("DUT_WRAP", $sformatf("Filled 0d%0d RTL and ISS memory bytes with random values", fill_cnt), UVM_LOW)
    //       end
    //       else begin
    //          `uvm_info("DUT_WRAP", $sformatf("Filled 0d%0d RTL memory bytes with random values", fill_cnt), UVM_LOW)
    //       end
    //     end
    //     else begin
    //       `uvm_error("DUT_WRAP", "No firmware specified!")
    //     end
    //   end
    //   else begin
    //     `uvm_info("DUT_WRAP", "NO TEST PROGRAM", UVM_NONE)
    //   end
    // end

    // --------------------------------------------
    // OBI Instruction agent v1.0 signal tie-offs
    assign obi_instr_if_i.gntpar    = 'b0;
    assign obi_instr_if_i.err       = 'b0;
    assign obi_instr_if_i.ruser     = 'b0;
    assign obi_instr_if_i.rid       = 'b0;
    assign obi_instr_if_i.exokay    = 'b0;
    assign obi_instr_if_i.rvalidpar = 'b0;
    assign obi_instr_if_i.rchk      = 'b0;
    assign obi_instr_if_i.auser     = 'b0;
    assign obi_instr_if_i.ruser     = 'b0;
    assign obi_instr_if_i.wuser     = 'b0;
    assign obi_instr_if_i.aid       = 'b0;
    assign obi_instr_if_i.rid       = 'b0;
    assign obi_instr_if_i.we        = 'b0;    
    assign obi_instr_if_i.be        = 'hf; // Always assumes 32-bit full bus reads on instruction OBI

    // --------------------------------------------
    // OBI Data agent v1.0 signal tie-offs
    assign obi_data_if_i.gntpar     = 'b0;
    assign obi_data_if_i.err        = 'b0;
    assign obi_data_if_i.ruser      = 'b0;
    assign obi_data_if_i.rid        = 'b0;
    assign obi_data_if_i.exokay     = 'b0;
    assign obi_data_if_i.rvalidpar  = 'b0;
    assign obi_data_if_i.rchk       = 'b0;
    assign obi_data_if_i.auser      = 'b0;
    assign obi_data_if_i.ruser      = 'b0;
    assign obi_data_if_i.wuser      = 'b0;
    assign obi_data_if_i.aid        = 'b0;
    assign obi_data_if_i.rid        = 'b0;

    // --------------------------------------------
    // Connect to uvma_interrupt_if
    assign interrupt_if.clk                     = clknrst_if.clk;
    assign interrupt_if.reset_n                 = clknrst_if.reset_n;
    assign interrupt_if.irq_id                  = irq_id;
    assign interrupt_if.irq_ack                 = irq_ack;

    // --------------------------------------------
    // Connect to core_cntrl_if
    assign core_cntrl_if.num_mhpmcounters = NUM_MHPMCOUNTERS;
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
         .hart_id_i              ( core_cntrl_if.hart_id          ),
         .dm_exception_addr_i    ( core_cntrl_if.dm_exception_addr),

         .instr_req_o            ( obi_instr_if_i.req             ),
         .instr_gnt_i            ( obi_instr_if_i.gnt             ),
         .instr_rvalid_i         ( obi_instr_if_i.rvalid          ),
         .instr_addr_o           ( obi_instr_if_i.addr            ),
         .instr_rdata_i          ( obi_instr_if_i.rdata           ),
         .instr_err_i            ( '0                             ), //TODO: Temp tie off to get "debug_test" to pass

         .data_req_o             ( obi_data_if_i.req              ),
         .data_gnt_i             ( obi_data_if_i.gnt              ),
         .data_rvalid_i          ( obi_data_if_i.rvalid           ),
         .data_we_o              ( obi_data_if_i.we               ),
         .data_be_o              ( obi_data_if_i.be               ),
         .data_addr_o            ( obi_data_if_i.addr             ),
         .data_wdata_o           ( obi_data_if_i.wdata            ),
         .data_rdata_i           ( obi_data_if_i.rdata            ),
         .data_atop_o            (                                ), //TODO: Temp ignore
         .data_err_i             ( '0                             ), //TODO: Temp tie off
         .data_exokay_i          ( '0                             ), //TODO: Temp tie off

         .irq_i                  ( interrupt_if.irq               ),
         .irq_ack_o              ( irq_ack                        ),
         .irq_id_o               ( irq_id                         ),

         .debug_req_i            ( debug_if.debug_req             ),
         .debug_havereset_o      ( debug_havereset                ),
         .debug_running_o        ( debug_running                  ),
         .debug_halted_o         ( debug_halted                   ),

         .fetch_enable_i         ( core_cntrl_if.fetch_en         ),
         .core_sleep_o           ( core_status_if.core_busy       )
        ); //riscv_core_i

    

    // this handles read to RAM and memory mapped virtual (pseudo) peripherals
    /*
    mm_ram #(.RAM_ADDR_WIDTH    (RAM_ADDR_WIDTH),
             .INSTR_RDATA_WIDTH (INSTR_RDATA_WIDTH)
            )
    ram_i
        (.clk_i          ( clknrst_if.clk                  ),
         .rst_ni         ( clknrst_if.reset_n              ),
         .dm_halt_addr_i ( core_cntrl_if.dm_halt_addr      ),

         .instr_req_i    ( instr_req                       ),
         .instr_addr_i   ( instr_addr                      ),
         .instr_rdata_o  ( instr_rdata                     ),
         .instr_rvalid_o ( instr_rvalid                    ),
         .instr_gnt_o    ( instr_gnt                       ),

         .data_req_i     ( data_req                        ),
         .data_addr_i    ( data_addr                       ),
         .data_we_i      ( data_we                         ),
         .data_be_i      ( data_be                         ),
         .data_wdata_i   ( data_wdata                      ),
         .data_rdata_o   ( data_rdata                      ),
         .data_rvalid_o  ( data_rvalid                     ),
         .data_gnt_o     ( data_gnt                        ),

         .irq_id_i       ( irq_id                          ),
         .irq_ack_i      ( irq_ack                         ),
         .irq_o          ( irq_vp                          ),

         .debug_req_o    ( debug_req_vp                       ),

         .pc_core_id_i   ( cv32e40x_wrapper_i.core_i.if_id_pipe.pc ),

         .tests_passed_o ( vp_status_if.tests_passed       ),
         .tests_failed_o ( vp_status_if.tests_failed       ),
         .exit_valid_o   ( vp_status_if.exit_valid         ),
         .exit_value_o   ( vp_status_if.exit_value         )
        ); //ram_i
    */

endmodule : uvmt_cv32e40x_dut_wrap

`endif // __UVMT_CV32E40X_DUT_WRAP_SV__



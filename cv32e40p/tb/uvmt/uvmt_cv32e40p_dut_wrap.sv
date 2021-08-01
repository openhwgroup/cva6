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


`ifndef __UVMT_CV32E40P_DUT_WRAP_SV__
`define __UVMT_CV32E40P_DUT_WRAP_SV__


/**
 * Module wrapper for CV32E40P RTL DUT.
 */
module uvmt_cv32e40p_dut_wrap #(
                            // CV32E40P parameters.  See User Manual.
                            parameter PULP_XPULP          =  0,
                                      PULP_CLUSTER        =  0,
                                      FPU                 =  0,
                                      PULP_ZFINX          =  0,
                                      NUM_MHPMCOUNTERS    =  1,
                            // Remaining parameters are used by TB components only
                                      INSTR_ADDR_WIDTH    =  32,
                                      INSTR_RDATA_WIDTH   =  32,
                                      RAM_ADDR_WIDTH      =  20
                           )

                           (
                            uvma_clknrst_if              clknrst_if,
                            uvma_interrupt_if            interrupt_if,
`ifdef USE_OBI_MEM_AGENT
                            // vp_status_if is driven by ENV and used in TB
                            uvma_interrupt_if            vp_interrupt_if,
`else
                            uvmt_cv32e40p_vp_status_if   vp_status_if,
`endif
                            uvmt_cv32e40p_core_cntrl_if  core_cntrl_if,
                            uvmt_cv32e40p_core_status_if core_status_if,
                            uvma_obi_memory_if           obi_memory_instr_if,
                            uvma_obi_memory_if           obi_memory_data_if
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

    logic [31:0]                  irq_vp;
    logic [31:0]                  irq_uvma;
    logic [31:0]                  irq;
    logic                         irq_ack;
    logic [ 4:0]                  irq_id;

    logic                         debug_req_vp;
    logic                         debug_req_uvma;
    logic                         debug_req;
    logic                         debug_havereset;
    logic                         debug_running;
    logic                         debug_halted;

    assign debug_if.clk      = clknrst_if.clk;
    assign debug_if.reset_n  = clknrst_if.reset_n;
    assign debug_req_uvma    = debug_if.debug_req;

    assign debug_req = debug_req_vp | debug_req_uvma;

    
    
    // Load the Instruction Memory 
`ifndef USE_OBI_MEM_AGENT
    initial begin: load_instruction_memory
      string firmware;
      int    fd;
       int   fill_cnt;
       bit [7:0]  rnd_byte;

      `uvm_info("DUT_WRAP", "waiting for load_instr_mem to be asserted.", UVM_DEBUG)
      wait(core_cntrl_if.load_instr_mem !== 1'bX);
      if(core_cntrl_if.load_instr_mem === 1'b1) begin
        `uvm_info("DUT_WRAP", "load_instr_mem asserted!", UVM_NONE)

        // Load the pre-compiled firmware
        if($value$plusargs("firmware=%s", firmware)) begin
          // First, check if it exists...
          fd = $fopen (firmware, "r");   
          if (fd)  `uvm_info ("DUT_WRAP", $sformatf("%s was opened successfully : (fd=%0d)", firmware, fd), UVM_DEBUG)
          else     `uvm_fatal("DUT_WRAP", $sformatf("%s was NOT opened successfully : (fd=%0d)", firmware, fd))
          $fclose(fd);
          // Now load it...
          `uvm_info("DUT_WRAP", $sformatf("loading firmware %0s", firmware), UVM_NONE)
          $readmemh(firmware, uvmt_cv32e40p_tb.dut_wrap.ram_i.dp_ram_i.mem);
          // Initialize RTL and ISS memory with (the same) random value to
          // prevent X propagation through the core RTL.
          fill_cnt = 0;
          for (int index=0; index < 2**RAM_ADDR_WIDTH; index++) begin
             if (uvmt_cv32e40p_tb.dut_wrap.ram_i.dp_ram_i.mem[index] === 8'hXX) begin
                fill_cnt++;
                rnd_byte = $random();
                uvmt_cv32e40p_tb.dut_wrap.ram_i.dp_ram_i.mem[index]=rnd_byte;
                if ($test$plusargs("USE_ISS")) begin
                  uvmt_cv32e40p_tb.iss_wrap.ram.memory.mem[index/4][((((index%4)+1)*8)-1)-:8]=rnd_byte; // convert byte to 32-bit addressing
                end
             end
          end
          if ($test$plusargs("USE_ISS")) begin
             `uvm_info("DUT_WRAP", $sformatf("Filled 0d%0d RTL and ISS memory bytes with random values", fill_cnt), UVM_LOW)
          end
          else begin
             `uvm_info("DUT_WRAP", $sformatf("Filled 0d%0d RTL memory bytes with random values", fill_cnt), UVM_LOW)
          end
        end
        else begin
          `uvm_error("DUT_WRAP", "No firmware specified!")
        end
      end
      else begin
        `uvm_info("DUT_WRAP", "NO TEST PROGRAM", UVM_NONE)
      end
    end
`endif // USE_OBI_MEM_AGENT

    // --------------------------------------------
    // Connect clk and reset for OBI MEM Agent
    assign obi_memory_instr_if.clk       = clknrst_if.clk;
    assign obi_memory_instr_if.reset_n   = clknrst_if.reset_n;
    assign obi_memory_data_if.clk        = clknrst_if.clk;
    assign obi_memory_data_if.reset_n    = clknrst_if.reset_n;
    // Instruction bus is read-only, OBI v1.0
    assign obi_memory_instr_if.gntpar    = 'b0;
    assign obi_memory_instr_if.err       = 'b0;
    assign obi_memory_instr_if.ruser     = 'b0;
    assign obi_memory_instr_if.rid       = 'b0;
    assign obi_memory_instr_if.exokay    = 'b0;
    assign obi_memory_instr_if.rvalidpar = 'b0;
    assign obi_memory_instr_if.rchk      = 'b0;
    assign obi_memory_instr_if.auser     = 'b0;
    assign obi_memory_instr_if.ruser     = 'b0;
    assign obi_memory_instr_if.wuser     = 'b0;
    assign obi_memory_instr_if.aid       = 'b0;
    assign obi_memory_instr_if.rid       = 'b0;
    assign obi_memory_instr_if.we        = 'b0;
    // Data bus is read/write, OBI v1.0
    assign obi_memory_data_if.gntpar     = 'b0;
    assign obi_memory_data_if.err        = 'b0;
    assign obi_memory_data_if.ruser      = 'b0;
    assign obi_memory_data_if.rid        = 'b0;
    assign obi_memory_data_if.exokay     = 'b0;
    assign obi_memory_data_if.rvalidpar  = 'b0;
    assign obi_memory_data_if.rchk       = 'b0;
    assign obi_memory_data_if.auser      = 'b0;
    assign obi_memory_data_if.ruser      = 'b0;
    assign obi_memory_data_if.wuser      = 'b0;
    assign obi_memory_data_if.aid        = 'b0;
    assign obi_memory_data_if.rid        = 'b0;

    // --------------------------------------------
    // Connect to uvma_interrupt_if
    assign interrupt_if.clk                     = clknrst_if.clk;
    assign interrupt_if.reset_n                 = clknrst_if.reset_n;
    assign irq_uvma                             = interrupt_if.irq;
`ifdef USE_OBI_MEM_AGENT
    assign vp_interrupt_if.clk                  = clknrst_if.clk;
    assign vp_interrupt_if.reset_n              = clknrst_if.reset_n;
    assign irq_vp                               = vp_interrupt_if.irq;
`else
    // irq_vp is driven by mm_ram
`endif
    assign interrupt_if.irq_id                  = irq_id;
    assign interrupt_if.irq_ack                 = irq_ack;

    assign irq = irq_uvma | irq_vp;

    // --------------------------------------------
    // instantiate the core
    cv32e40p_wrapper #(
                 .PULP_XPULP       (PULP_XPULP),
                 .PULP_CLUSTER     (PULP_CLUSTER),
                 .FPU              (FPU),
                 .PULP_ZFINX       (PULP_ZFINX),
                 .NUM_MHPMCOUNTERS (NUM_MHPMCOUNTERS)
                )
    cv32e40p_wrapper_i
        (
         .clk_i                  ( clknrst_if.clk                 ),
         .rst_ni                 ( clknrst_if.reset_n             ),

         .pulp_clock_en_i        ( core_cntrl_if.pulp_clock_en    ),
         .scan_cg_en_i           ( core_cntrl_if.scan_cg_en       ),

         .boot_addr_i            ( core_cntrl_if.boot_addr        ),
         .mtvec_addr_i           ( core_cntrl_if.mtvec_addr       ),
         .dm_halt_addr_i         ( core_cntrl_if.dm_halt_addr     ),
         .hart_id_i              ( core_cntrl_if.hart_id          ),
         .dm_exception_addr_i    ( core_cntrl_if.dm_exception_addr),

`ifndef USE_OBI_MEM_AGENT
         .instr_req_o            ( instr_req                      ),
         .instr_gnt_i            ( instr_gnt                      ),
         .instr_rvalid_i         ( instr_rvalid                   ),
         .instr_addr_o           ( instr_addr                     ),
         .instr_rdata_i          ( instr_rdata                    ),

         .data_req_o             ( data_req                       ),
         .data_gnt_i             ( data_gnt                       ),
         .data_rvalid_i          ( data_rvalid                    ),
         .data_we_o              ( data_we                        ),
         .data_be_o              ( data_be                        ),
         .data_addr_o            ( data_addr                      ),
         .data_wdata_o           ( data_wdata                     ),
         .data_rdata_i           ( data_rdata                     ),
`else // USE_OBI_MEM_AGENT
         .instr_req_o            ( obi_memory_instr_if.req        ), // core to agent
         .instr_gnt_i            ( obi_memory_instr_if.gnt        ), // agent to core
         .instr_rvalid_i         ( obi_memory_instr_if.rvalid     ),
         .instr_addr_o           ( obi_memory_instr_if.addr       ),
         .instr_rdata_i          ( obi_memory_instr_if.rdata      ),

         .data_req_o             ( obi_memory_data_if.req         ),
         .data_gnt_i             ( obi_memory_data_if.gnt         ),
         .data_rvalid_i          ( obi_memory_data_if.rvalid      ),
         .data_we_o              ( obi_memory_data_if.we          ),
         .data_be_o              ( obi_memory_data_if.be          ),
         .data_addr_o            ( obi_memory_data_if.addr        ),
         .data_wdata_o           ( obi_memory_data_if.wdata       ),
         .data_rdata_i           ( obi_memory_data_if.rdata       ),
`endif // USE_OBI_MEM_AGENT

         // APU not verified in cv32e40p (future work)
         .apu_req_o              (                                ),
         .apu_gnt_i              ( 1'b0                           ),
         .apu_operands_o         (                                ),
         .apu_op_o               (                                ),
         .apu_flags_o            (                                ),
         .apu_rvalid_i           ( 1'b0                           ),
         .apu_result_i           ( {32{1'b0}}                     ),
         .apu_flags_i            ( {5{1'b0}}                      ), // APU_NUSFLAGS_CPU

`ifndef USE_OBI_MEM_AGENT
         .irq_i                  ( irq                            ),
         .irq_ack_o              ( irq_ack                        ),
         .irq_id_o               ( irq_id                         ),

         .debug_req_i            ( debug_req                      ),
`else // USE_OBI_MEM_AGENT
         .irq_i                  ( irq_uvma                       ),
         .irq_ack_o              ( irq_ack                        ),
         .irq_id_o               ( irq_id                         ),

         .debug_req_i            ( debug_req_uvma                 ),
`endif // USE_OBI_MEM_AGENT
         .debug_havereset_o      ( debug_havereset                ),
         .debug_running_o        ( debug_running                  ),
         .debug_halted_o         ( debug_halted                   ),

         .fetch_enable_i         ( core_cntrl_if.fetch_en         ),
         .core_sleep_o           ( core_status_if.core_busy       )
        ); // cv32e40p_wrapper_i

`ifndef USE_OBI_MEM_AGENT
    // this handles read to RAM and memory mapped virtual (pseudo) peripherals
    mm_ram #(
        .RAM_ADDR_WIDTH    (RAM_ADDR_WIDTH),
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

         .debug_req_o    ( debug_req_vp                    ),

         .pc_core_id_i   ( cv32e40p_wrapper_i.core_i.pc_id ),

`ifndef USE_OBI_MEM_AGENT
         .tests_passed_o ( vp_status_if.tests_passed       ),
         .tests_failed_o ( vp_status_if.tests_failed       ),
         .exit_valid_o   ( vp_status_if.exit_valid         ),
         .exit_value_o   ( vp_status_if.exit_value         )
`else // USE_OBI_MEM_AGENT
         .tests_passed_o (                                 ),
         .tests_failed_o (                                 ),
         .exit_valid_o   (                                 ),
         .exit_value_o   (                                 )
`endif // USE_OBI_MEM_AGENT
        ); //ram_i
`endif // USE_OBI_MEM_AGENT

/*
`ifdef USE_OBI_MEM_AGENT
initial begin
   force obi_memory_data_if.gnt = 1'b1;
   force obi_memory_data_if.rvalid = 1'b0;
   force obi_memory_data_if.rdata = 32'h0000_0000;
   wait (obi_memory_data_if.reset_n == 1'b0);
   release obi_memory_data_if.gnt;
   release obi_memory_data_if.rvalid;
   release obi_memory_data_if.rdata;
end
`endif
*/


endmodule : uvmt_cv32e40p_dut_wrap

`endif // __UVMT_CV32E40P_DUT_WRAP_SV__



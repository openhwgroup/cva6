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
// Author: Florian Zaruba, ETH Zurich
// Date: 15/04/2017
// Description: Top level testbench module. Instantiates the top level DUT, configures
//              the virtual interfaces and starts the test passed by +UVM_TEST+

`timescale 1ps/1ps

import ariane_pkg::*;
import uvm_pkg::*;

`include "uvm_macros.svh"

import "DPI-C" function read_elf(input string filename);
import "DPI-C" function byte get_section(output longint address, output longint len);
import "DPI-C" context function byte read_section(input longint address, inout byte buffer[]);

module ariane_tb;

    static uvm_cmdline_processor uvcl = uvm_cmdline_processor::get_inst();

    localparam int unsigned CLOCK_PERIOD = 56832ps;
    // toggle with RTC period
    localparam int unsigned RTC_CLOCK_PERIOD = 30.517us;

    localparam NUM_WORDS = 2**25;
    logic clk_i;
    logic rst_ni;
    logic rtc_i;
    logic rst_DTM;
   
   
    parameter  USE_HYPER_MODELS    = 1;

  `ifdef jtag_rbb_enable 
    parameter int   jtag_enable = '1 ;
  `else  
    parameter int   jtag_enable = '0 ;
  `endif
    
    wire                  s_dmi_req_valid;
    wire                  s_dmi_req_ready;
    wire [ 6:0]           s_dmi_req_bits_addr;
    wire [ 1:0]           s_dmi_req_bits_op;
    wire [31:0]           s_dmi_req_bits_data;
    wire                  s_dmi_resp_valid;
    wire                  s_dmi_resp_ready;
    wire [ 1:0]           s_dmi_resp_bits_resp;
    wire [31:0]           s_dmi_resp_bits_data;   
    wire                  s_dmi_exit;
   
    wire                  s_jtag_TCK       ;
    wire                  s_jtag_TMS       ;
    wire                  s_jtag_TDI       ;
    wire                  s_jtag_TRSTn     ;
    wire                  s_jtag_TDO_data  ;
    wire                  s_jtag_TDO_driven;
    wire                  s_jtag_exit      ;
   
    wire [7:0]            w_hyper_dq0    ;
    wire [7:0]            w_hyper_dq1    ;
    wire                  w_hyper_ck     ;
    wire                  w_hyper_ckn    ;
    wire                  w_hyper_csn0   ;
    wire                  w_hyper_csn1   ;
    wire                  w_hyper_rwds0  ;
    wire                  w_hyper_rwds1  ;
    wire                  w_hyper_reset  ;

    wire [63:0]           w_gpios        ; 

    wire                  w_cva6_uart_rx ;
    wire                  w_cva6_uart_tx ;
   
    wire [7:0]            w_axi_hyper_dq0    ;
    wire [7:0]            w_axi_hyper_dq1    ;
    wire                  w_axi_hyper_ck     ;
    wire                  w_axi_hyper_ckn    ;
    wire                  w_axi_hyper_csn0   ;
    wire                  w_axi_hyper_csn1   ;
    wire                  w_axi_hyper_rwds0  ;
    wire                  w_axi_hyper_rwds1  ;
    wire                  w_axi_hyper_reset  ;
  
    longint unsigned cycles;
    longint unsigned max_cycles;

    logic [31:0] exit_o;

    string binary = "";

    genvar j;
    generate
       for (j=0; j<32; j++) begin
          assign w_gpios[63-j] = w_gpios[j] ? 1 : 0 ;          
        end
    endgenerate

  assign exit_o              = (jtag_enable[0]) ? s_jtag_exit          : s_dmi_exit;
   
  if (1) begin
    SimDTM i_SimDTM (
      .clk                  ( clk_i                 ),
      .reset                ( ~rst_DTM              ),
      .debug_req_valid      ( s_dmi_req_valid       ),
      .debug_req_ready      ( s_dmi_req_ready       ),
      .debug_req_bits_addr  ( s_dmi_req_bits_addr   ),
      .debug_req_bits_op    ( s_dmi_req_bits_op     ),
      .debug_req_bits_data  ( s_dmi_req_bits_data   ),
      .debug_resp_valid     ( s_dmi_resp_valid      ),
      .debug_resp_ready     ( s_dmi_resp_ready      ),
      .debug_resp_bits_resp ( s_dmi_resp_bits_resp  ),
      .debug_resp_bits_data ( s_dmi_resp_bits_data  ), 
      .exit                 ( s_dmi_exit            )
    );
  end else begin
    assign dmi_req_valid = '0;
    assign debug_req_bits_op = '0;
    assign dmi_exit = 1'b0;
  end   
   
  // SiFive's SimJTAG Module
  // Converts to DPI calls
  SimJTAG i_SimJTAG (
    .clock                ( clk_i                ),
    .reset                ( ~rst_ni              ),
    .enable               ( jtag_enable[0]       ),
    .init_done            ( rst_ni               ),
    .jtag_TCK             ( s_jtag_TCK           ),
    .jtag_TMS             ( s_jtag_TMS           ),
    .jtag_TDI             ( s_jtag_TDI           ),
    .jtag_TRSTn           ( s_jtag_TRSTn         ),
    .jtag_TDO_data        ( s_jtag_TDO_data      ),
    .jtag_TDO_driven      ( s_jtag_TDO_driven    ),
    .exit                 ( s_jtag_exit          )
  );
   
    al_saqr #(
        .NUM_WORDS         ( NUM_WORDS     ),
        .InclSimDTM        ( 1'b1          ),
        .StallRandomOutput ( 1'b1          ),
        .StallRandomInput  ( 1'b1          ),
        .JtagEnable        ( jtag_enable[0])
    ) dut (
        .rst_ni,
        .rtc_i,
        .dmi_req_valid        ( s_dmi_req_valid        ),
        .dmi_req_ready        ( s_dmi_req_ready        ),
        .dmi_req_bits_addr    ( s_dmi_req_bits_addr    ),
        .dmi_req_bits_op      ( s_dmi_req_bits_op      ),
        .dmi_req_bits_data    ( s_dmi_req_bits_data    ),
        .dmi_resp_valid       ( s_dmi_resp_valid       ),
        .dmi_resp_ready       ( s_dmi_resp_ready       ),
        .dmi_resp_bits_resp   ( s_dmi_resp_bits_resp   ),
        .dmi_resp_bits_data   ( s_dmi_resp_bits_data   ),                      
        .jtag_TCK             ( s_jtag_TCK             ),
        .jtag_TMS             ( s_jtag_TMS             ),
        .jtag_TDI             ( s_jtag_TDI             ),
        .jtag_TRSTn           ( s_jtag_TRSTn           ),
        .jtag_TDO_data        ( s_jtag_TDO_data        ),
        .jtag_TDO_driven      ( s_jtag_TDO_driven      ),
        .pad_hyper_dq0        ( w_hyper_dq0            ),
        .pad_hyper_dq1        ( w_hyper_dq1            ),
        .pad_hyper_ck         ( w_hyper_ck             ),
        .pad_hyper_ckn        ( w_hyper_ckn            ),
        .pad_hyper_csn0       ( w_hyper_csn0           ),
        .pad_hyper_csn1       ( w_hyper_csn1           ),
        .pad_hyper_rwds0      ( w_hyper_rwds0          ),
        .pad_hyper_rwds1      ( w_hyper_rwds1          ),
        .pad_hyper_reset      ( w_hyper_reset          ),
        .pad_gpio             ( w_gpios                ),
        .cva6_uart_rx_i       ( w_cva6_uart_rx         ),
        .cva6_uart_tx_o       ( w_cva6_uart_tx         ),
        .pad_axi_hyper_dq0        ( w_axi_hyper_dq0            ),
        .pad_axi_hyper_dq1        ( w_axi_hyper_dq1            ),
        .pad_axi_hyper_ck         ( w_axi_hyper_ck             ),
        .pad_axi_hyper_ckn        ( w_axi_hyper_ckn            ),
        .pad_axi_hyper_csn0       ( w_axi_hyper_csn0           ),
        .pad_axi_hyper_csn1       ( w_axi_hyper_csn1           ),
        .pad_axi_hyper_rwds0      ( w_axi_hyper_rwds0          ),
        .pad_axi_hyper_rwds1      ( w_axi_hyper_rwds1          ),
        .pad_axi_hyper_reset      ( w_axi_hyper_reset          )
   );

   s27ks0641 #(
         /*.mem_file_name ( "s27ks0641.mem"    ),*/
         .TimingModel   ( "S27KS0641DPBHI020"    )
     ) i_s27ks0641 (
            .DQ7      ( w_axi_hyper_dq0[7] ),
            .DQ6      ( w_axi_hyper_dq0[6] ),
            .DQ5      ( w_axi_hyper_dq0[5] ),
            .DQ4      ( w_axi_hyper_dq0[4] ),
            .DQ3      ( w_axi_hyper_dq0[3] ),
            .DQ2      ( w_axi_hyper_dq0[2] ),
            .DQ1      ( w_axi_hyper_dq0[1] ),
            .DQ0      ( w_axi_hyper_dq0[0] ),
            .RWDS     ( w_axi_hyper_rwds0  ),
            .CSNeg    ( w_axi_hyper_csn0   ),
            .CK       ( w_axi_hyper_ck     ),
            .CKNeg    ( w_axi_hyper_ckn    ),
            .RESETNeg ( w_axi_hyper_reset  )
     );
   
// Hyperram and hyperflash modules
   generate
      if(USE_HYPER_MODELS == 1) begin
         s27ks0641 #(
            .TimingModel  ("S27KS0641DPBHI020")
         ) hyperram_model (
            .DQ7      ( w_hyper_dq0[7] ),
            .DQ6      ( w_hyper_dq0[6] ),
            .DQ5      ( w_hyper_dq0[5] ),
            .DQ4      ( w_hyper_dq0[4] ),
            .DQ3      ( w_hyper_dq0[3] ),
            .DQ2      ( w_hyper_dq0[2] ),
            .DQ1      ( w_hyper_dq0[1] ),
            .DQ0      ( w_hyper_dq0[0] ),
            .RWDS     ( w_hyper_rwds0  ),
            .CSNeg    ( w_hyper_csn1   ),
            .CK       ( w_hyper_ck     ),
            .CKNeg    ( w_hyper_ckn    ),
            .RESETNeg ( w_hyper_reset  )
         );
         s26ks512s #(
            .TimingModel   ( "S26KS512SDPBHI000"),
            .mem_file_name ( "./vectors/hyper_stim.slm" )
         ) hyperflash_model (
            .DQ7      ( w_hyper_dq0[7] ),
            .DQ6      ( w_hyper_dq0[6] ),
            .DQ5      ( w_hyper_dq0[5] ),
            .DQ4      ( w_hyper_dq0[4] ),
            .DQ3      ( w_hyper_dq0[3] ),
            .DQ2      ( w_hyper_dq0[2] ),
            .DQ1      ( w_hyper_dq0[1] ),
            .DQ0      ( w_hyper_dq0[0] ),
            .RWDS     ( w_hyper_rwds0  ),
            .CSNeg    ( w_hyper_csn0   ),
            .CK       ( w_hyper_ck     ),
            .CKNeg    ( w_hyper_ckn    ),
            .RESETNeg ( w_hyper_reset  )
         );
      end
   endgenerate

   uart_bus #(.BAUD_RATE(115200), .PARITY_EN(0)) i_uart_bus (.rx(w_cva6_uart_tx), .tx(w_cva6_uart_rx), .rx_en(1'b1));

`ifdef SPIKE_TANDEM
    spike #(
        .Size ( NUM_WORDS * 8 )
    ) i_spike (
        .clk_i,
        .rst_ni,
        .clint_tick_i   ( rtc_i                               ),
        .commit_instr_i ( dut.i_ariane.commit_instr_id_commit ),
        .commit_ack_i   ( dut.i_ariane.commit_ack             ),
        .exception_i    ( dut.i_ariane.ex_commit              ),
        .waddr_i        ( dut.i_ariane.waddr_commit_id        ),
        .wdata_i        ( dut.i_ariane.wdata_commit_id        ),
        .priv_lvl_i     ( dut.i_ariane.priv_lvl               )
    );
    initial begin
        $display("Running binary in tandem mode");
    end
`endif

    // Clock process
    initial begin
        clk_i = 1'b0;
        rst_ni = 1'b0;
        rst_DTM = 1'b0;
        repeat(8)
            #(CLOCK_PERIOD/2) clk_i = ~clk_i;
        rst_ni = 1'b1;
        repeat(200)
           #(CLOCK_PERIOD/2) clk_i = ~clk_i;
        rst_DTM = 1'b1;       
        forever begin
            #(CLOCK_PERIOD/2) clk_i = 1'b1;
            #(CLOCK_PERIOD/2) clk_i = 1'b0;

            //if (cycles > max_cycles)
            //    $fatal(1, "Simulation reached maximum cycle count of %d", max_cycles);

            cycles++;
        end
    end

    initial begin
        forever begin
            rtc_i = 1'b1;
            #(RTC_CLOCK_PERIOD/2) rtc_i = 1'b0;
            #(RTC_CLOCK_PERIOD/2) rtc_i = 1'b1;
        end
    end
   
   
   
    initial begin
        forever begin

            wait (exit_o[0]);

            if ((exit_o >> 1)) begin
                `uvm_error( "Core Test",  $sformatf("*** FAILED *** (tohost = %0d)", (exit_o >> 1)))
            end else begin
                `uvm_info( "Core Test",  $sformatf("*** SUCCESS *** (tohost = %0d)", (exit_o >> 1)), UVM_LOW)
            end

            $finish();
        end
    end

    // for faster simulation we can directly preload the ELF
    // Note that we are loosing the capabilities to use risc-fesvr though
    // TODO : preload the ELF on the hyperram instead of the legacy DRAM
    initial begin
        automatic logic [7:0][7:0] mem_row;
        longint address, len;
        byte buffer[];
        void'(uvcl.get_arg_value("+PRELOAD=", binary));

        if (binary != "") begin
            `uvm_info( "Core Test", $sformatf("Preloading ELF: %s", binary), UVM_LOW)

            void'(read_elf(binary));
            // wait with preloading, otherwise randomization will overwrite the existing value
            wait(rst_DTM);

           
            // while there are more sections to process
            while (get_section(address, len)) begin
                automatic int num_words = (len+7)/8;
                `uvm_info( "Core Test", $sformatf("Loading Address: %x, Length: %x", address, len),
UVM_LOW)
                buffer = new [num_words*8];
                void'(read_section(address, buffer));
                // preload memories
                // 64-bit
                for (int i = 0; i < num_words; i++) begin
                    mem_row = '0;
                    for (int j = 0; j < 8; j++) begin
                        mem_row[j] = buffer[i*8 + j];
                    end
                end
            end
        end
    end
endmodule // ariane_tb


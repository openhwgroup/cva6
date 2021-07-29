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

    localparam int unsigned CLOCK_PERIOD   = 56832ps;
    localparam int unsigned REFClockPeriod = 56832ps;
    // toggle with RTC period
    localparam int unsigned RTC_CLOCK_PERIOD = 30.517us;

    localparam NUM_WORDS = 2**25;
    logic clk_i;
    logic rst_ni;
    logic rtc_i;
    logic rst_DTM;

    localparam ENABLE_DM_TESTS = 0;
   
    parameter  USE_HYPER_MODELS    = 1;
    parameter  LOCAL_JTAG          = 1;
    parameter  CHECK_LOCAL_JTAG    = 0; 
   
  `ifdef POSTLAYOUT
    localparam int unsigned JtagSampleDelay = (REFClockPeriod < 10ns) ? 2 : 1;
  `else
    localparam int unsigned JtagSampleDelay = 0;
  `endif    

  `ifdef jtag_rbb 
    parameter int   jtag_enable = '1 ;
  `else  
    parameter int   jtag_enable = '0 ;
  `endif

    localparam logic [15:0] PartNumber = 1; 
    logic program_loaded = 0;
    logic  eoc;
    logic [31:0]  retval = 32'h0;  // Store return value
    localparam logic [31:0] dm_idcode  = (dm::DbgVersion013 << 28) | (PartNumber << 12) | 32'b1; 
    localparam AxiWideBeWidth    = ariane_axi_soc::DataWidth / 8;
    localparam AxiWideByteOffset = $clog2(AxiWideBeWidth);
    typedef logic [ariane_axi_soc::AddrWidth-1:0] addr_t;
    typedef logic [ariane_axi_soc::DataWidth-1:0] data_t;   
    data_t memory[bit [31:0]];
    int sections [bit [31:0]];
    
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
  
    string                stimuli_file      ;
    logic                 s_tck         ;
    logic                 s_tms         ;
    logic                 s_tdi         ;
    logic                 s_trstn       ;
    logic                 s_tdo         ;

    wire                  s_jtag2alsaqr_tck       ;
    wire                  s_jtag2alsaqr_tms       ;
    wire                  s_jtag2alsaqr_tdi       ;
    wire                  s_jtag2alsaqr_trstn     ;
    wire                  s_jtag2alsaqr_tdo       ;
   
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

    string binary = "../software/hello/hello.riscv";

    genvar j;
    generate
       for (j=0; j<32; j++) begin
          assign w_gpios[63-j] = w_gpios[j] ? 1 : 0 ;          
        end
    endgenerate

  assign exit_o              = (jtag_enable[0]) ? s_jtag_exit          : s_dmi_exit;

  assign s_jtag2alsaqr_tck    = LOCAL_JTAG  ?  s_tck   : s_jtag_TCK   ;
  assign s_jtag2alsaqr_tms    = LOCAL_JTAG  ?  s_tms   : s_jtag_TMS   ;
  assign s_jtag2alsaqr_tdi    = LOCAL_JTAG  ?  s_tdi   : s_jtag_TDI   ;
  assign s_jtag2alsaqr_trstn  = LOCAL_JTAG  ?  s_trstn : s_jtag_TRSTn ;
  assign s_jtag_TDO_data      = s_jtag2alsaqr_tdo       ;
  assign s_tdo                = s_jtag2alsaqr_tdo       ;
  
  if (~jtag_enable[0] & !LOCAL_JTAG) begin
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
        .NUM_WORDS         ( NUM_WORDS                   ),
        .InclSimDTM        ( 1'b1                        ),
        .StallRandomOutput ( 1'b1                        ),
        .StallRandomInput  ( 1'b1                        ),
        .JtagEnable        ( jtag_enable[0] | LOCAL_JTAG )
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
        .jtag_TCK             ( s_jtag2alsaqr_tck      ),
        .jtag_TMS             ( s_jtag2alsaqr_tms      ),
        .jtag_TDI             ( s_jtag2alsaqr_tdi      ),
        .jtag_TRSTn           ( s_jtag2alsaqr_trstn    ),
        .jtag_TDO_data        ( s_jtag2alsaqr_tdo      ),
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
         .TimingModel   ( "S27KS0641DPBHI020"    ),
         .UserPreload   ( 1'b0                   ),
         .mem_file_name ( "hyper.mem"            )
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
            .TimingModel   ( "S27KS0641DPBHI020" ),
            .UserPreload   ( 1'b0                ),
            .mem_file_name ( "hyper.mem"         )
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
            .UserPreload   ( 1'b0               ),
            .mem_file_name ( "hyper.mem"        )
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

    initial begin: reset_jtag
      jtag_mst.tdi = 0;
      jtag_mst.tms = 0;
    end
  
    // JTAG Definition
    typedef jtag_test::riscv_dbg #(
      .IrLength       (5                 ),
      .TA             (REFClockPeriod*0.1),
      .TT             (REFClockPeriod*0.9),
      .JtagSampleDelay(JtagSampleDelay   )
    ) riscv_dbg_t;
  
    // JTAG driver
    JTAG_DV jtag_mst (s_tck);
    riscv_dbg_t::jtag_driver_t jtag_driver = new(jtag_mst);
    riscv_dbg_t riscv_dbg = new(jtag_driver);
  
    assign s_trstn      = jtag_mst.trst_n;
    assign s_tms        = jtag_mst.tms;
    assign s_tdi        = jtag_mst.tdi;
    assign jtag_mst.tdo = s_tdo;

    // Clock process
    initial begin
        clk_i = 1'b0;
        rst_ni = 1'b0;
        rst_DTM = 1'b0;
        jtag_mst.trst_n = 1'b0;
       
        repeat(8)
            #(CLOCK_PERIOD/2) clk_i = ~clk_i;
        rst_ni = 1'b1;
        repeat(200)
           #(CLOCK_PERIOD/2) clk_i = ~clk_i;
        rst_DTM = 1'b1;
        jtag_mst.trst_n = 1'b1;       
        forever begin
            #(CLOCK_PERIOD/2) clk_i = 1'b1;
            #(CLOCK_PERIOD/2) clk_i = 1'b0;

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
   

   assign s_tck = clk_i;
   
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


   initial  begin: memory_init

      repeat(30000)
            #(CLOCK_PERIOD/2);
      debug_module_init();
      load_binary(binary);
      #(REFClockPeriod);
      jtag_ariane_wakeup();
      jtag_read_eoc();
      
   end
   
  task debug_module_init;
    logic [31:0]  idcode;
    automatic dm::sbcs_t sbcs;

`ifdef POSTLAYOUT
    #(0.05 * REFClockPeriod);
`endif

    $info(" JTAG Preloading start time");
    riscv_dbg.wait_idle(300);

`ifdef POSTLAYOUT
    #(0.05 * REFClockPeriod);
`endif

    $info(" Start getting idcode of JTAG");
    riscv_dbg.get_idcode(idcode);

    // Check Idcode
    assert (idcode == dm_idcode)
    else $error(" Wrong IDCode, expected: %h, actual: %h", dm_idcode, idcode);
    $display(" IDCode = %h", idcode);

    $info(" Activating Debug Module");
    // Activate Debug Module
    riscv_dbg.write_dmi(dm::DMControl, 32'h0000_0001);

    $info(" SBA BUSY ");
    // Wait until SBA is free
    do riscv_dbg.read_dmi(dm::SBCS, sbcs);
    while (sbcs.sbbusy);
    $info(" SBA FREE");
  endtask // debug_module_init
   
   task jtag_data_preload;
    logic [127:0] rdata;

    automatic dm::sbcs_t sbcs = '{
      sbautoincrement: 1'b1,
      sbreadondata   : 1'b1,
      sbaccess       : 2'd2,
      default        : 1'b0
    };

    $display("======== Initializing the Debug Module ========");

    debug_module_init();
    riscv_dbg.write_dmi(dm::SBCS, sbcs);
    do riscv_dbg.read_dmi(dm::SBCS, sbcs);
    while (sbcs.sbbusy);

    $display("======== Preload data to SRAM ========");

    // Start writing to SRAM
    foreach (sections[addr]) begin
      $display("Writing %h with %0d words", addr << 3, sections[addr]); // word = 8 bytes here
       riscv_dbg.write_dmi(dm::SBAddress0, (addr << 3));
       do riscv_dbg.read_dmi(dm::SBCS, sbcs);
       while (sbcs.sbbusy);
      for (int i = 0; i < sections[addr]; i++) begin
        // $info(" Loading words to SRAM ");
        $display(" -- Word %0d/%0d", i, sections[addr]);
        riscv_dbg.write_dmi(dm::SBData1, memory[addr + i][63:32]);
        do riscv_dbg.read_dmi(dm::SBCS, sbcs);
        while (sbcs.sbbusy);           
        riscv_dbg.write_dmi(dm::SBData0, memory[addr + i][32:0]);
        // Wait until SBA is free to write next 32 bits
        do riscv_dbg.read_dmi(dm::SBCS, sbcs);
        while (sbcs.sbbusy);
      end
    end

    // Check loaded data
    if (CHECK_LOCAL_JTAG) begin
      $display("======== Checking loaded data ========");
      // Set SBCS register to read data
      sbcs.sbreadonaddr = 1;
      riscv_dbg.write_dmi(dm::SBCS, sbcs);
      foreach (sections[addr]) begin
        $display(" Checking %h", addr << 4);
        riscv_dbg.write_dmi(dm::SBAddress0, (addr << 4));
        for (int i = 0; i < sections[addr]; i++) begin
          if (i % 20 == 0) $display(" -- Word %0d/%0d", i, sections[addr]);
          for (int j = 0; j < 4; j++) begin
            riscv_dbg.read_dmi(dm::SBData0, rdata[j*32+:32]);
            // Wait until SBA is free to read another 32 bits
            do riscv_dbg.read_dmi(dm::SBCS, sbcs);
            while (sbcs.sbbusy);
          end
          if (rdata != memory[addr + i])
            $error("Mismatch detected at %h, expected %0d, actual %0d",
              (addr + i) << 4, memory[addr + 1], rdata);
        end
      end
    end

    $display("======== Preloading finished ========");

    // Preloading finished. Can now start executing
    sbcs.sbreadonaddr = 0;
    sbcs.sbreadondata = 0;
    riscv_dbg.write_dmi(dm::SBCS, sbcs);

  endtask // jtag_data_preload


  // Load ELF binary file
  task load_binary;
    input string binary;                   // File name
    addr_t       section_addr, section_len;
    byte         buffer[];
    // Read ELF
    void'(read_elf(binary));
    $display("Reading %s", binary);
    while (get_section(section_addr, section_len)) begin
      // Read Sections
      automatic int num_words = (section_len + AxiWideBeWidth - 1)/AxiWideBeWidth;
      $display("Reading section %x with %0d words", section_addr, num_words);

      sections[section_addr >> AxiWideByteOffset] = num_words;
      buffer                                      = new[num_words * AxiWideBeWidth];
      void'(read_section(section_addr, buffer));
      for (int i = 0; i < num_words; i++) begin
        automatic logic [AxiWideBeWidth-1:0][7:0] word = '0;
        for (int j = 0; j < AxiWideBeWidth; j++) begin
          word[j] = buffer[i * AxiWideBeWidth + j];
        end
        memory[section_addr/AxiWideBeWidth + i] = word;
      end
    end

    // Call the JTAG preload task
    jtag_data_preload();

  endtask // load_binary

  
  task jtag_ariane_wakeup;

    $info("======== Waking up Ariane using JTAG ========");
    // Generate the interrupt
    riscv_dbg.write_dmi(dm::DMControl, 32'h0000_0003);

    # 150ns; 
     
    riscv_dbg.write_dmi(dm::DMControl, 32'h0000_0001);
    // Wait till end of computation
    program_loaded = 1;

    // When task completed reading the return value using JTAG
    // Mainly used for post synthesis part
    $info("======== Wait for Completion ========");

  endtask // execute_application

  task jtag_read_eoc;

    automatic dm::sbcs_t sbcs = '{
      sbautoincrement: 1'b1,
      sbreadondata   : 1'b1,
      default        : 1'b0
    };

    // Initialize the dm module again, otherwise it will not work
    debug_module_init();
    sbcs.sbreadonaddr = 1;
    sbcs.sbautoincrement = 0;
    sbcs.sbaccess = 2;
    riscv_dbg.write_dmi(dm::SBCS, sbcs);
    do riscv_dbg.read_dmi(dm::SBCS, sbcs);
    while (sbcs.sbbusy);

    riscv_dbg.write_dmi(dm::SBAddress0, 32'h8000_1000);
    riscv_dbg.wait_idle(10);
    do riscv_dbg.read_dmi(dm::SBData0, retval);
    while (~retval[31]);
     

    if (retval[30:0]!=0) begin
        `uvm_error( "Core Test",  $sformatf("*** FAILED *** (tohost = %0d)",retval[30:0]))
    end else begin
        `uvm_info( "Core Test",  $sformatf("*** SUCCESS *** (tohost = %0d)", (retval[30:0])), UVM_LOW)
    end
     
  endtask // jtag_read_eoc

endmodule // ariane_tb


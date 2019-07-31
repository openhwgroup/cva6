/**
 * Avalon Wrapper for ariane core
 */

module ariane_core_avalon #(
    parameter int unsigned MHPMCounterNum   = 0,
    parameter int unsigned MHPMCounterWidth = 40,
    parameter bit RV32E                     = 0,
    parameter bit RV32M                     = 1,
    parameter int unsigned DmHaltAddr       = 32'h1A110800,
    parameter int unsigned DmExceptionAddr  = 32'h1A110808
) (
    // Clock and Reset
    input logic         clk_i,
    input logic         rst_i,

    input logic         test_en_i, // enable all clock gates for testing

    // Core ID, Cluster ID and boot address are considered more or less static
    input logic [ 3:0]  core_id_i,
    input logic [ 5:0]  cluster_id_i,
    input logic [31:0]  boot_addr_i,

    // Data memory interface (Avalon)
    output logic [31:0] avm_main_address,
    output logic [7:0]  avm_main_byteenable,
    output logic        avm_main_read,
    input logic [63:0]  avm_main_readdata,
    output logic        avm_main_write,
    output logic [63:0] avm_main_writedata,
    input logic         avm_main_waitrequest,
    input logic         avm_main_readdatavalid,
    input logic [1:0]   avm_main_response,

    // Interrupt inputs
    input logic         irq_i, // level sensitive IR lines
    input logic [4:0]   irq_id_i,
    output logic        irq_ack_o, // irq ack
    output logic [4:0]  irq_id_o,

    // RISC-V Formal Interface
    // Does not comply with the coding standards of _i/_o suffixes, but follows
    // the convention of RISC-V Formal Interface Specification.
`ifdef RVFI
    output logic [NR_COMMIT_PORTS-1:0]        rvfi_valid,
    output logic [NR_COMMIT_PORTS-1:0] [63:0] rvfi_order,
    output logic [NR_COMMIT_PORTS-1:0] [31:0] rvfi_insn,
    output logic [NR_COMMIT_PORTS-1:0] [31:0] rvfi_insn_uncompressed,
    output logic [NR_COMMIT_PORTS-1:0]        rvfi_trap,
    output logic [NR_COMMIT_PORTS-1:0]        rvfi_halt,
    output logic [NR_COMMIT_PORTS-1:0]        rvfi_intr,
    output logic [NR_COMMIT_PORTS-1:0] [ 1:0] rvfi_mode,
    output logic [NR_COMMIT_PORTS-1:0] [ 4:0] rvfi_rs1_addr,
    output logic [NR_COMMIT_PORTS-1:0] [ 4:0] rvfi_rs2_addr,
    output logic [NR_COMMIT_PORTS-1:0] [63:0] rvfi_rs1_rdata,
    output logic [NR_COMMIT_PORTS-1:0] [63:0] rvfi_rs2_rdata,
    output logic [NR_COMMIT_PORTS-1:0] [ 4:0] rvfi_rd_addr,
    output logic [NR_COMMIT_PORTS-1:0] [63:0] rvfi_rd_wdata,
    output logic [NR_COMMIT_PORTS-1:0] [63:0] rvfi_pc_rdata,
    output logic [NR_COMMIT_PORTS-1:0] [63:0] rvfi_pc_wdata,
    output logic [NR_COMMIT_PORTS-1:0] [63:0] rvfi_mem_addr,
    output logic [NR_COMMIT_PORTS-1:0] [ 3:0] rvfi_mem_rmask,
    output logic [NR_COMMIT_PORTS-1:0] [ 3:0] rvfi_mem_wmask,
    output logic [NR_COMMIT_PORTS-1:0] [63:0] rvfi_mem_rdata,
    output logic [NR_COMMIT_PORTS-1:0] [63:0] rvfi_mem_wdata,
`endif

    input logic [31:0]                       instr_dii,
    input logic                              instruction_valid_dii,
    output logic [INSTR_PER_FETCH-1:0][31:0] instr,
    output logic [INSTR_PER_FETCH-1:0][63:0] addr,
    output logic [INSTR_PER_FETCH-1:0]       instruction_valid,
    output logic                             flush_ctrl_if,
    output logic                      [63:0] virtual_request_address,
    output logic                             serving_unaligned_o,
    output logic [63:0]                      serving_unaligned_address_o,
    // branch-predict update
    output logic                             is_mispredict,

    output logic                                rom_req,
    output logic [ariane_axi::AddrWidth-1:0]    rom_addr,
    input logic  [ariane_axi::DataWidth-1:0]    rom_rdata,

    // Debug Interface
    input logic         debug_req_i
);

    // set up connections for ariane inputs
    logic         instr_rvalid_i;
    logic [31:0]  instr_rdata_i, prdata, prdata_0;
    logic         psel, pready, pready_0, penable, penable_0;
    logic         instr_gnt_i;

    logic         data_rvalid_i;
    logic [3:0]   data_be_o;
    logic [63:0]  data_addr_o;
    logic [63:0]  data_wdata_o;
    logic [63:0]  data_rdata_i;
    logic         data_err_i;
    logic         data_err_avalon;
    logic         data_we_o;
    logic         data_req_o;
    logic         data_gnt_i;

    localparam ariane_pkg::ariane_cfg_t ArianeRIGCfg = '{
      RASDepth: 2,
      BTBEntries: 32,
      BHTEntries: 128,
      GHRLength: 4,
      // idempotent region
      NrNonIdempotentRules:  0,
      NonIdempotentAddrBase: {0},
      NonIdempotentLength:   {0},
      NrExecuteRegionRules:  1,
      ExecuteRegionAddrBase: {64'h00000000},
      ExecuteRegionLength:   {64'hFFFFFFFFFFFFFFFF},
      // cached region
      NrCachedRegionRules:    1,
      CachedRegionAddrBase:  {64'h80000000},
      CachedRegionLength:    {64'h0},
      // physical region
      NrPhysicalRegionRules:    1,
      PhysicalRegionAddrBase:  {64'h80000000},
      PhysicalRegionLength:    {64'h0},
      //  cache config
      Axi64BitCompliant:      1'b1,
      SwapEndianess:          1'b0,
      // debug
      DmBaseAddress:          64'h0
    };
   
    avalon_ariane_translator_main translator_main (
        .clock(clk_i),
        .reset_n(~rst_i),

        // inputs to translator
        .data_req_i(data_req_o),
        .data_we_i(data_we_o),
        .data_be_i(data_be_o),
        // our main memory interface is word-addressed but the ariane core is byte-addressed
        .data_addr_i({2'b0, data_addr_o[63:2]}),
        .data_wdata_i(data_wdata_o),
        
        .avm_main_waitrequest(avm_main_waitrequest),
        .avm_main_readdatavalid(avm_main_readdatavalid),
        .avm_main_readdata(avm_main_readdata),
        .avm_main_response(avm_main_response),

        // outputs from translator
        .data_gnt_o(data_gnt_i),
        .data_rvalid_o(data_rvalid_i),
        .data_rdata_o(data_rdata_i),
        .data_err_o(data_err_avalon),

        .avm_main_address(avm_main_address),
        .avm_main_byteenable(avm_main_byteenable),
        .avm_main_read(avm_main_read),
        .avm_main_write(avm_main_write),
        .avm_main_writedata(avm_main_writedata)
    );

   ariane_axi::req_t    axi_req;
   ariane_axi::resp_t   axi_resp;

  AXI_BUS #(
    .AXI_ADDR_WIDTH ( ariane_axi::AddrWidth   ),
    .AXI_DATA_WIDTH ( ariane_axi::DataWidth   ),
    .AXI_ID_WIDTH   ( ariane_soc::IdWidth     ),
    .AXI_USER_WIDTH ( ariane_axi::UserWidth   )
  ) slave();

  // ---------------
  // ROM
  // ---------------
  axi2mem #(
    .AXI_ID_WIDTH   ( ariane_soc::IdWidth      ),
    .AXI_ADDR_WIDTH ( ariane_axi::AddrWidth    ),
    .AXI_DATA_WIDTH ( ariane_axi::DataWidth    ),
    .AXI_USER_WIDTH ( ariane_axi::UserWidth    )
  ) i_axi2rom (
    .clk_i  ( clk_i                   ),
    .rst_ni ( ~rst_i                  ),
    .slave  ( slave                   ),
    .req_o  ( rom_req                 ),
    .we_o   (                         ),
    .addr_o ( rom_addr                ),
    .be_o   (                         ),
    .data_o (                         ),
    .data_i ( rom_rdata               )
  );

   ariane #(
    .ArianeCfg  ( ArianeRIGCfg )
  ) u_core (
        // Clock and reset
        .clk_i          (clk_i),
        .rst_ni         (~rst_i),

        // Configuration
        .hart_id_i      (core_id_i),
        .boot_addr_i    (boot_addr_i),
              
        // Interrupt inputs
        .irq_i          (irq_i),
/*
        .irq_id_i       (irq_id_i),
        .irq_ack_o      (irq_ack_o),
        .irq_id_o       (irq_id_o),
*/
        // Debug interface
        .debug_req_i    (debug_req_i),
        
        // RISC-V Formal Interface
        // Does not comply with the coding standards of _i/_o suffixes, but follows
        // the convention of RISC-V Formal Interface Specification.
    `ifdef RVFI
        .rvfi_valid     (rvfi_valid),
        .rvfi_order     (rvfi_order),
        .rvfi_insn      (rvfi_insn),
        .rvfi_insn_uncompressed (rvfi_insn_uncompressed),
        .rvfi_trap      (rvfi_trap),
        .rvfi_halt      (rvfi_halt),
        .rvfi_intr      (rvfi_intr),
        .rvfi_mode      (rvfi_mode),
        .rvfi_rs1_addr  (rvfi_rs1_addr),
        .rvfi_rs2_addr  (rvfi_rs2_addr),
        .rvfi_rs1_rdata (rvfi_rs1_rdata),
        .rvfi_rs2_rdata (rvfi_rs2_rdata),
        .rvfi_rd_addr   (rvfi_rd_addr),
        .rvfi_rd_wdata  (rvfi_rd_wdata),
        .rvfi_pc_rdata  (rvfi_pc_rdata),
        .rvfi_pc_wdata  (rvfi_pc_wdata),
        .rvfi_mem_addr  (rvfi_mem_addr),
        .rvfi_mem_rmask (rvfi_mem_rmask),
        .rvfi_mem_wmask (rvfi_mem_wmask),
        .rvfi_mem_rdata (rvfi_mem_rdata),
        .rvfi_mem_wdata (rvfi_mem_wdata),
    `endif

    `ifdef DII
        .flush_ctrl_if,
        .instr,
        .addr,
        .instruction_valid,
        .virtual_request_address,
        .serving_unaligned_o,
        .serving_unaligned_address_o,
        .is_mispredict,
    `endif

        // Special control signal
        .ipi_i(0),
        .time_irq_i(0),
        .axi_req_o(axi_req),
        .axi_resp_i(axi_resp)
    );

  axi_master_connect i_axi_master_connect_ariane (
    .axi_req_i(axi_req),
    .axi_resp_o(axi_resp),
    .master(slave)
  );
   
endmodule

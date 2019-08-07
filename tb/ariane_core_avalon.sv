/**
 * Avalon Wrapper for ariane core
 */

module ariane_core_avalon #(
) (
    // Clock and Reset
    input logic         clk_i,
    input logic         rst_i,

    // Data memory interface (Avalon)
    output logic [31:0] avm_main_address,
    output logic [7:0]  avm_main_byteenable,
    output logic        avm_main_read,
    input logic [63:0]  avm_main_readdata,
    output logic        avm_main_write,
    output logic [63:0] avm_main_writedata,
    input logic         avm_main_readdatavalid,
    input logic [1:0]   avm_main_response,

    // Interrupt inputs
    input logic         irq_i, // level sensitive IR lines

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
    output logic [NR_COMMIT_PORTS-1:0] [ 7:0] rvfi_mem_rmask,
    output logic [NR_COMMIT_PORTS-1:0] [ 7:0] rvfi_mem_wmask,
    output logic [NR_COMMIT_PORTS-1:0] [63:0] rvfi_mem_rdata,
    output logic [NR_COMMIT_PORTS-1:0] [63:0] rvfi_mem_wdata,
    output logic [NR_COMMIT_PORTS-1:0]        rvfi_flush,
`endif

    output logic [INSTR_PER_FETCH-1:0] [31:0] instr,
    output logic [INSTR_PER_FETCH-1:0] [63:0] addr,
    output logic [INSTR_PER_FETCH-1:0]        instruction_valid,
    output logic                       [63:0] virtual_request_address,
    output logic                              serving_unaligned_o,
    output logic [63:0]                       serving_unaligned_address_o,
    // branch-predict update
    output logic                              is_mispredict, rvfi_mem_read, rvfi_mem_write,

    output logic                                mem_req,
    output logic [ariane_axi::AddrWidth-1:0]    mem_addr,
    input logic  [ariane_axi::DataWidth-1:0]    mem_rdata
);

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
      PhysicalRegionLength:    {64'h10000},
      //  cache config
      Axi64BitCompliant:      1'b1,
      SwapEndianess:          1'b0,
      // debug
      DmBaseAddress:          64'h0
    };
   
   ariane_axi::req_t    axi_req;
   ariane_axi::resp_t   axi_resp;

  AXI_BUS #(
    .AXI_ADDR_WIDTH ( ariane_axi::AddrWidth   ),
    .AXI_DATA_WIDTH ( ariane_axi::DataWidth   ),
    .AXI_ID_WIDTH   ( ariane_soc::IdWidth     ),
    .AXI_USER_WIDTH ( ariane_axi::UserWidth   )
  ) slave();

   logic [7:0]         dummy;
   assign mem_addr[63:56] = {8{mem_addr[55]}};
   
  // ---------------
  // MEM
  // ---------------
  axi2mem #(
    .AXI_ID_WIDTH   ( ariane_soc::IdWidth      ),
    .AXI_ADDR_WIDTH ( ariane_axi::AddrWidth    ),
    .AXI_DATA_WIDTH ( ariane_axi::DataWidth    ),
    .AXI_USER_WIDTH ( ariane_axi::UserWidth    )
  ) i_axi2rom (
    .clk_i  ( clk_i                       ),
    .rst_ni ( ~rst_i                      ),
    .slave  ( slave                       ),
    .req_o  ( mem_req                     ),
    .we_o   (                             ),
    .addr_o ( {dummy,mem_addr[55:0]}      ),
    .be_o   (                             ),
    .data_o (                             ),
    .data_i ( mem_rdata                   )
  );

   ariane #(
    .ArianeCfg  ( ArianeRIGCfg )
  ) u_core (
        // Clock and reset
        .clk_i          (clk_i),
        .rst_ni         (~rst_i),

        // Configuration
        .hart_id_i      ('0),
        .boot_addr_i    (64'H80000000),
              
        // Interrupt inputs
        .irq_i          (irq_i),
        // Debug interface
        .debug_req_i    (1'b0),
        
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
        .rvfi_flush     (rvfi_flush),
        .instr,
        .addr,
        .instruction_valid,
        .virtual_request_address,
        .serving_unaligned_o,
        .serving_unaligned_address_o,
        .is_mispredict,
        .rvfi_mem_read,
        .rvfi_mem_write,
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

/**
 * Avalon Wrapper for ariane core
 */

`define RVFI

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

`ifdef DII
    input logic [31:0]  instr_dii,
    input logic         instruction_valid_dii,
    input logic         enable_dii,
    output logic        flush_dii,
    output logic        instr_req_dii,
`endif

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
      // idempotent region
      NrNonIdempotentRules:  0,
      NonIdempotentAddrBase: {0},
      NonIdempotentLength:   {0},
      NrExecuteRegionRules:  1,
      ExecuteRegionAddrBase: {64'h80000000},
      ExecuteRegionLength:   {64'h10000},
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

   axi2apb #(
            .AXI4_ADDRESS_WIDTH ( ariane_axi::AddrWidth ),
            .AXI4_RDATA_WIDTH   ( ariane_axi::DataWidth ),
            .AXI4_WDATA_WIDTH   ( ariane_axi::DataWidth ),
            .AXI4_ID_WIDTH      ( ariane_soc::IdWidth   ),
            .AXI4_USER_WIDTH    ( ariane_axi::UserWidth ),

            .BUFF_DEPTH_SLAVE   ( 2              ),
            .APB_ADDR_WIDTH     ( ariane_axi::AddrWidth )
  ) i_axi2apb (
            .ACLK       ( clk_i                 ),
            .ARESETn    ( ~rst_i                ),
            .test_en_i  ( test_en_i             ),

            .AWID_i     ( axi_req.aw.id         ),
            .AWADDR_i   ( axi_req.aw.addr       ),
            .AWLEN_i    ( axi_req.aw.len        ),
            .AWSIZE_i   ( axi_req.aw.size       ),
            .AWBURST_i  ( axi_req.aw.burst      ),
            .AWLOCK_i   ( axi_req.aw.lock       ),
            .AWCACHE_i  ( axi_req.aw.cache      ),
            .AWPROT_i   ( axi_req.aw.prot       ),
            .AWREGION_i ( axi_req.aw.region     ),
            .AWUSER_i   ( '0                    ),
            .AWQOS_i    ( axi_req.aw.qos        ),
            .AWVALID_i  ( axi_req.aw_valid      ),
            .AWREADY_o  ( axi_resp.aw_ready     ),

            .WDATA_i    ( axi_req.w.data        ),
            .WSTRB_i    ( axi_req.w.strb        ),
            .WLAST_i    ( axi_req.w.last        ),
            .WUSER_i    ( '0                    ),
            .WVALID_i   ( axi_req.w_valid       ),
            .WREADY_o   ( axi_resp.w_ready      ),

            .BID_o      ( axi_resp.b.id         ),
            .BRESP_o    ( axi_resp.b.resp       ),
            .BVALID_o   ( axi_resp.b_valid      ),
            .BUSER_o    (                       ),
            .BREADY_i   ( axi_req.b_ready       ),

            .ARID_i     ( axi_req.ar.id         ),
            .ARADDR_i   ( axi_req.ar.addr       ),
            .ARLEN_i    ( axi_req.ar.len        ),
            .ARSIZE_i   ( axi_req.ar.size       ),
            .ARBURST_i  ( axi_req.ar.burst      ),
            .ARLOCK_i   ( axi_req.ar.lock       ),
            .ARCACHE_i  ( axi_req.ar.cache      ),
            .ARPROT_i   ( axi_req.ar.prot       ),
            .ARREGION_i ( axi_req.ar.region     ),
            .ARUSER_i   ( '0                    ),
            .ARQOS_i    ( axi_req.ar.qos        ),
            .ARVALID_i  ( axi_req.ar_valid      ),
            .ARREADY_o  ( axi_resp.ar_ready     ),

            .RID_o      ( axi_resp.r.id         ),
            .RDATA_o    ( axi_resp.r.data       ),
            .RRESP_o    ( axi_resp.r.resp       ),
            .RLAST_o    ( axi_resp.r.last       ),
            .RUSER_o    (                       ),
            .RVALID_o   ( axi_resp.r_valid      ),
            .RREADY_i   ( axi_req.r_ready       ),

            .PENABLE    ( penable               ),
            .PWRITE     ( data_we_o             ),
            .PADDR      ( data_addr_o           ),
            .PSEL       ( psel                  ),
            .PWDATA     ( data_wdata_o          ),
            .PRDATA     ( prdata                ),
            .PREADY     ( pready                ),
            .PSLVERR    ( data_err_i            )
  );

   always @(posedge clk_i)
     begin
        pready_0 <= pready;
        penable_0 <= penable;
        prdata_0 <= data_rdata_i;
        prdata <= prdata_0;
        data_err_i <= data_err_avalon | (penable && ((data_addr_o < 64'h80000000) || (data_addr_o >= 64'h80010000)));
     end
   
assign pready = data_rvalid_i;
   
/*              
 obsolete ??
        .data_rvalid_i  (data_rvalid_i),
        .data_be_o      (data_be_o),
        .data_addr_o    (data_addr_o),
        .data_rdata_i   (data_rdata_i),
        .data_req_o     (data_req_o),
        .data_gnt_i     (data_gnt_i),
*/
   
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
        .flush_dii,
        .instr_req_dii,
        .instr_dii,
        .instruction_valid_dii,
        .enable_dii,
    `endif

        // Special control signal
        .ipi_i(0),
        .time_irq_i(0),
        .axi_req_o(axi_req),
        .axi_resp_i(axi_resp)
    );

endmodule

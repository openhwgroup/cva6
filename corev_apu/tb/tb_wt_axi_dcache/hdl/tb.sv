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
// Author: Michael Schaffner <schaffner@iis.ee.ethz.ch>, ETH Zurich
//         Nils Wistoff <nwistoff@iis.ee.ethz.ch>, ETH Zurich
// Date: 04.09.2020
// Description: testbench for nonblocking write-back L1 dcache.

`include "tb.svh"
`include "assign.svh"
`include "axi/typedef.svh"

module tb import ariane_pkg::*; import wt_cache_pkg::*; import tb_pkg::*; #()();

  // leave this
  timeunit 1ps;
  timeprecision 1ps;

  // memory configuration (64bit words)
  parameter MemBytes          = 2**DCACHE_INDEX_WIDTH * 4 * 32;
  parameter MemWords          = MemBytes>>3;

  // noncacheable portion
  parameter logic [63:0] CachedAddrBeg = MemBytes>>3;//1/8th of the memory is NC
  parameter logic [63:0] CachedAddrEnd = 64'hFFFF_FFFF_FFFF_FFFF;

  // contention and invalidation rates (in %)
  parameter MemRandHitRate   = 75;
  parameter MemRandInvRate   = 10;
  parameter TlbHitRate       = 95;

  // parameters for random read sequences (in %)
  parameter FlushRate         = 10;
  parameter KillRate          = 5;

  parameter Verbose           = 0;

  // number of vectors per test
  parameter nReadVectors      = 20000;
  parameter nWriteVectors     = 20000;
  parameter nAMOs             = 20000;

  /// ID width of the Full AXI slave port, master port has ID `AxiIdWidthFull + 32'd1`
  parameter int unsigned  TbAxiIdWidthFull   = 32'd6;
  /// Address width of the full AXI bus
  parameter int unsigned  TbAxiAddrWidthFull = 32'd64;
  /// Data width of the full AXI bus
  parameter int unsigned  TbAxiDataWidthFull = 32'd64;
  localparam int unsigned TbAxiUserWidthFull = AXI_USER_WIDTH;
  /// Application time to the DUT
  parameter time          TbApplTime         = 2ns;
  /// Test time of the DUT
  parameter time          TbTestTime         = 8ns;


///////////////////////////////////////////////////////////////////////////////
// MUT signal declarations
///////////////////////////////////////////////////////////////////////////////

  `AXI_TYPEDEF_ALL(axi_data,
                   logic [    TbAxiAddrWidthFull-1:0],
                   logic [      TbAxiIdWidthFull-1:0],
                   logic [    TbAxiDataWidthFull-1:0],
                   logic [(TbAxiDataWidthFull/8)-1:0],
                   logic [    TbAxiUserWidthFull-1:0])

  logic                enable_i;
  logic                flush_i;
  logic                flush_ack_o;
  logic                miss_o;
  amo_req_t            amo_req_i;
  amo_resp_t           amo_resp_o;
  dcache_req_i_t [2:0] req_ports_i;
  dcache_req_o_t [2:0] req_ports_o;
  axi_data_req_t       axi_data_o;
  axi_data_resp_t      axi_data_i;

///////////////////////////////////////////////////////////////////////////////
// TB signal declarations
///////////////////////////////////////////////////////////////////////////////

  string test_name;
  logic clk_i, rst_ni;
  logic [31:0] seq_num_resp, seq_num_write, seq_num_amo;
  seq_t [2:0] seq_type;
  logic [3:0] seq_done;
  logic [6:0] req_rate[2:0];
  logic seq_run, seq_last;
  logic end_of_sim;

  logic mem_rand_en;
  logic inv_rand_en;
  logic amo_rand_en;
  logic tlb_rand_en;

  logic write_en;
  logic [63:0] write_paddr, write_data;
  logic [7:0] write_be;

  typedef struct packed  {
    logic [1:0]  size;
    logic [63:0] paddr;
  } resp_fifo_t;

  typedef struct packed {
    logic        valid;
    logic [63:0] paddr;
  } reservation_t;

  logic [63:0] act_paddr[1:0];
  riscv::xlen_t exp_rdata[1:0];
  logic [63:0] exp_paddr[1:0];
  logic [63:0] amo_act_mem;
  logic [63:0] amo_shadow;
  logic [63:0] amo_exp_result;
  resp_fifo_t  fifo_data_in[1:0];
  resp_fifo_t  fifo_data[1:0];
  logic [1:0]  fifo_push, fifo_pop, fifo_flush;
  logic [2:0]  flush;
  logic        flush_rand_en;

  AXI_BUS_DV #(
    .AXI_ADDR_WIDTH ( TbAxiAddrWidthFull       ),
    .AXI_DATA_WIDTH ( TbAxiDataWidthFull       ),
    .AXI_ID_WIDTH   ( TbAxiIdWidthFull + 32'd1 ),
    .AXI_USER_WIDTH ( TbAxiUserWidthFull       )
  ) axi_data_dv (
    .clk_i ( clk_i )
  );

  `AXI_ASSIGN_FROM_REQ(axi_data_dv, axi_data_o)
  `AXI_ASSIGN_TO_RESP(axi_data_i, axi_data_dv)

  typedef tb_mem_port #(
    .AW                   ( TbAxiAddrWidthFull       ),
    .DW                   ( TbAxiDataWidthFull       ),
    .IW                   ( TbAxiIdWidthFull + 32'd1 ),
    .UW                   ( TbAxiUserWidthFull       ),
    .TA                   ( TbApplTime               ),
    .TT                   ( TbTestTime               ),
    .AX_MIN_WAIT_CYCLES   ( 0                        ),
    .AX_MAX_WAIT_CYCLES   ( 50                       ),
    .R_MIN_WAIT_CYCLES    ( 10                       ),
    .R_MAX_WAIT_CYCLES    ( 20                       ),
    .RESP_MIN_WAIT_CYCLES ( 10                       ),
    .RESP_MAX_WAIT_CYCLES ( 20                       ),
    .MEM_BYTES            ( MemBytes                 )
  ) tb_mem_port_t;

  tb_mem_port_t data_mem_port;

  AXI_BUS #(
    .AXI_ADDR_WIDTH ( TbAxiAddrWidthFull       ),
    .AXI_DATA_WIDTH ( TbAxiDataWidthFull       ),
    .AXI_ID_WIDTH   ( TbAxiIdWidthFull + 32'd1 ),
    .AXI_USER_WIDTH ( TbAxiUserWidthFull       )
  ) axi_data ();

  AXI_BUS #(
    .AXI_ADDR_WIDTH ( TbAxiAddrWidthFull       ),
    .AXI_DATA_WIDTH ( TbAxiDataWidthFull       ),
    .AXI_ID_WIDTH   ( TbAxiIdWidthFull + 32'd1 ),
    .AXI_USER_WIDTH ( TbAxiUserWidthFull       )
  ) axi_amo_adapter ();

  AXI_BUS_DV #(
    .AXI_ADDR_WIDTH ( TbAxiAddrWidthFull       ),
    .AXI_DATA_WIDTH ( TbAxiDataWidthFull       ),
    .AXI_ID_WIDTH   ( TbAxiIdWidthFull + 32'd1 ),
    .AXI_USER_WIDTH ( TbAxiUserWidthFull       )
  ) axi_amo_adapter_dv (
    .clk_i ( clk_i )
  );

  `AXI_ASSIGN(axi_data, axi_data_dv)
  `AXI_ASSIGN(axi_amo_adapter_dv, axi_amo_adapter)

///////////////////////////////////////////////////////////////////////////////
// Helper tasks
///////////////////////////////////////////////////////////////////////////////

  // Run a sequence of read (and write) vectors
  task automatic runSeq(input int nReadVectors, input int nWriteVectors = 0, input logic last =1'b0);
    seq_last      = last;
    seq_run       = 1'b1;
    seq_num_resp  = nReadVectors;
    seq_num_write = nWriteVectors;
    seq_num_amo   = 0;
    `APPL_WAIT_CYC(clk_i, 1)
    seq_run      = 1'b0;
    `APPL_WAIT_SIG(clk_i, &seq_done)
    `APPL_WAIT_CYC(clk_i, 1)
  endtask : runSeq

  // Run a sequence of AMOs
  task automatic runAMOs(input int nAMOs, input logic last =1'b0);
    seq_last      = last;
    seq_run       = 1'b1;
    seq_num_resp  = 0;
    seq_num_write = 0;
    seq_num_amo   = nAMOs;
    `APPL_WAIT_CYC(clk_i, 1)
    seq_run      = 1'b0;
    `APPL_WAIT_SIG(clk_i, &seq_done)
    `APPL_WAIT_CYC(clk_i, 1)
  endtask : runAMOs

  // Flush the cache
  task automatic flushCache();
    flush[2]      = 1'b1;
    `APPL_WAIT_SIG(clk_i, flush_ack_o);
    flush[2]      = 0'b0;
    `APPL_WAIT_CYC(clk_i, 1)
  endtask : flushCache

///////////////////////////////////////////////////////////////////////////////
// Clock Process
///////////////////////////////////////////////////////////////////////////////

  always @*
    begin
      do begin
        clk_i = 1; #(CLK_HI);
        clk_i = 0; #(CLK_LO);
      end while (end_of_sim == 1'b0);
      repeat (100) begin
        // generate a few extra cycle to allow
        // response acquisition to complete
        clk_i = 1; #(CLK_HI);
        clk_i = 0; #(CLK_LO);
      end
    end

///////////////////////////////////////////////////////////////////////////////
// memory emulation
///////////////////////////////////////////////////////////////////////////////

  // listen to the write/AMO ports and keep shadow memory up-to-date
  initial begin : p_mem
    automatic logic[63:0] amo_result, amo_op_a, amo_op_b, amo_op_a_u, amo_op_b_u;
    reservation_t reservation;

    // Initialize
    reservation = '0;
    amo_exp_result = 'x;
    `APPL_WAIT_SIG(clk_i, ~rst_ni)
    `APPL_WAIT_CYC(clk_i, 1)

    forever begin
      `ACQ_WAIT_CYC(clk_i, 1)
      amo_exp_result = 'x;

      // Regular stores. These are directly written to shadow memory.
      if(write_en) begin
        for(int k=0; k<8; k++) begin
          if(write_be[k]) begin
            tb_mem_port_t::shadow_q[write_paddr + k] <= write_data[k*8 +: 8];
          end
        end
      end

      // AMOs. Here, we perform the AMO on shadow memory to keep it consistent with the memory and
      // deliver to an expected response.
      if (amo_req_i.req) begin
        // 32-bit AMO
        if (amo_req_i.size == 2'h2) begin
          // Sign-extended operands
          amo_op_a   = $signed(amo_shadow[31:0]);
          amo_op_b   = $signed(amo_req_i.operand_b[31:0]);

          // Zero-extended operands
          amo_op_a_u = $unsigned(amo_shadow[31:0]);
          amo_op_b_u = $unsigned(amo_req_i.operand_b[31:0]);

          // The result that is expected to be returned by AMO and evantually to be stored in rd.
          // For most AMOs, this is the previous memory content.
          // RISC-V spec requires: "For RV64, 32-bit AMOs always sign-extend the value placed in rd."
          amo_exp_result = amo_op_a;

        // 64-bit AMO
        end else begin
          // Sign-extended operands
          amo_op_a   = $signed(amo_shadow);
          amo_op_b   = $signed(amo_req_i.operand_b);

          // Zero-extended operands
          amo_op_a_u = $unsigned(amo_shadow);
          amo_op_b_u = $unsigned(amo_req_i.operand_b);

          // The result that is expected to be returned by AMO and evantually to be stored in rd.
          // For most AMOs, this is the previous memory content.
          amo_exp_result = amo_shadow;
        end

        // Perform actual AMO.
        case (amo_req_i.amo_op)
          // LR instruction
          AMO_LR: begin
            // Mark a reservation for requested memory location.
            reservation.valid = 1'b1;
            reservation.paddr = amo_req_i.operand_a;

            // The memory contents remain unchanged (old contents == new contents)
            amo_result = amo_shadow;
          end

          // SC instruction
          AMO_SC: begin
            // Check whether we have a valid reservation. If so, do the store and return 0.
            if (reservation.valid && reservation.paddr == amo_req_i.operand_a) begin
              amo_result     = amo_op_b;
              amo_exp_result = 64'b0;

            // Else, leave the memory unchanged and return 1.
            end else begin
              amo_result     = amo_shadow;
              amo_exp_result = 64'b1;
            end

            // Either way, invalidate the reservation.
            reservation.valid = 1'b0;
          end

          // AMOs
          AMO_SWAP: amo_result = amo_op_b;
          AMO_ADD:  amo_result = amo_op_a + amo_op_b;
          AMO_AND:  amo_result = amo_op_a & amo_op_b;
          AMO_OR:   amo_result = amo_op_a | amo_op_b;
          AMO_XOR:  amo_result = amo_op_a ^ amo_op_b;
          AMO_MAX:  amo_result = ($signed(amo_op_a) > $signed(amo_op_b)) ? amo_op_a : amo_op_b;
          AMO_MIN:  amo_result = ($signed(amo_op_a) < $signed(amo_op_b)) ? amo_op_a : amo_op_b;
          AMO_MAXU: amo_result = (amo_op_a_u > amo_op_b_u) ? amo_op_a : amo_op_b;
          AMO_MINU: amo_result = (amo_op_a_u < amo_op_b_u) ? amo_op_a : amo_op_b;

          // Default: Leave memory unchanged.
          default: amo_result = amo_shadow;
        endcase

        `ACQ_WAIT_CYC(clk_i,1)

        // Write back arithmetic result of AMO to shadow memory.
        for (int k = 0; k < 2**amo_req_i.size; k++) begin
          tb_mem_port_t::shadow_q[amo_req_i.operand_a + k] <= amo_result[k*8 +: 8];
        end

        `ACQ_WAIT_SIG(clk_i,amo_resp_o.ack)
      end
    end
  end

  // Instantiate memory and AXI ports
  initial begin : p_sim_mem
    // Create AXI ports
    data_mem_port   = new(axi_amo_adapter_dv, CACHED);

    // Initialize AXI ports and memory
    data_mem_port.reset();
    tb_mem_port_t::init_mem();

    @(posedge rst_ni);

    // Start AXI port emulation
    fork
      data_mem_port.run();
    join
  end

///////////////////////////////////////////////////////////////////////////////
// MUT
///////////////////////////////////////////////////////////////////////////////

  localparam ariane_cfg_t ArianeDefaultConfig = '{
    RASDepth: 2,
    BTBEntries: 32,
    BHTEntries: 128,
    // idempotent region
    NrNonIdempotentRules:  0,
    NonIdempotentAddrBase: {64'b0},
    NonIdempotentLength:   {64'b0},
    // executable region
    NrExecuteRegionRules:  0,
    ExecuteRegionAddrBase: {64'h0},
    ExecuteRegionLength:   {64'h0},
    // cached region
    NrCachedRegionRules:   1,
    CachedRegionAddrBase:  {CachedAddrBeg},//1/8th of the memory is NC
    CachedRegionLength:    {CachedAddrEnd-CachedAddrBeg+64'b1},
    // cache config
    AxiCompliant:          1'b1,
    SwapEndianess:         1'b0,
    // debug
    DmBaseAddress:         64'h0,
    NrPMPEntries:          0
  };

  wt_cache_subsystem  #(
    .ArianeCfg    ( ArianeDefaultConfig ),
    .AxiAddrWidth ( TbAxiAddrWidthFull  ),
    .AxiDataWidth ( TbAxiDataWidthFull  ),
    .AxiIdWidth   ( TbAxiIdWidthFull    ),
    .axi_req_t    ( axi_data_req_t      ),
    .axi_rsp_t    ( axi_data_resp_t     )
  ) i_dut (
    .clk_i              (clk_i        ),
    .rst_ni             (rst_ni       ),
    .icache_en_i        ( '0          ),
    .icache_flush_i     ( '0          ),
    .icache_miss_o      (             ),
    .icache_areq_i      ( '0          ),
    .icache_areq_o      (             ),
    .icache_dreq_i      ( '0          ),
    .icache_dreq_o      (             ),
    .dcache_enable_i    ( 1'b1        ),
    .dcache_flush_i     ( flush_i     ),
    .dcache_flush_ack_o ( flush_ack_o ),
    .dcache_amo_req_i   ( amo_req_i   ),
    .dcache_amo_resp_o  ( amo_resp_o  ),
    .dcache_miss_o      (             ),
    .dcache_req_ports_i ( req_ports_i ),
    .dcache_req_ports_o ( req_ports_o ),
    .wbuffer_empty_o    (             ),
    .wbuffer_not_ni_o   (             ),
    .axi_req_o          ( axi_data_o  ),
    .axi_resp_i         ( axi_data_i  )
  );

///////////////////////////////////////////////////////////////////////////////
// AXI Atomics Adapter
///////////////////////////////////////////////////////////////////////////////

axi_riscv_atomics_wrap #(
    .AXI_ADDR_WIDTH     ( TbAxiAddrWidthFull       ),
    .AXI_DATA_WIDTH     ( TbAxiDataWidthFull       ),
    .AXI_ID_WIDTH       ( TbAxiIdWidthFull + 32'd1 ),
    .AXI_USER_WIDTH     ( TbAxiUserWidthFull       ),
    .AXI_MAX_WRITE_TXNS ( 1                        ),
    .RISCV_WORD_WIDTH   ( riscv::XLEN              )
) i_amo_adapter (
    .clk_i  ( clk_i                         ),
    .rst_ni ( rst_ni                        ),
    .mst    ( axi_amo_adapter.Master ),
    .slv    ( axi_data.Slave )
);

///////////////////////////////////////////////////////////////////////////////
// port emulation programs
///////////////////////////////////////////////////////////////////////////////

  // get actual paddr from read controllers
  assign act_paddr[0] = {i_dut.i_wt_dcache.gen_rd_ports[0].i_wt_dcache_ctrl.address_tag_d,
                         i_dut.i_wt_dcache.gen_rd_ports[0].i_wt_dcache_ctrl.address_idx_q,
                         i_dut.i_wt_dcache.gen_rd_ports[0].i_wt_dcache_ctrl.address_off_q};
  assign act_paddr[1] = {i_dut.i_wt_dcache.gen_rd_ports[1].i_wt_dcache_ctrl.address_tag_d,
                         i_dut.i_wt_dcache.gen_rd_ports[1].i_wt_dcache_ctrl.address_idx_q,
                         i_dut.i_wt_dcache.gen_rd_ports[1].i_wt_dcache_ctrl.address_off_q};

  // generate fifo queues for expected responses
  generate
    for(genvar k=0; k<2;k++) begin
      assign fifo_data_in[k] =  {req_ports_i[k].data_size,
                                 exp_paddr[k]};

      for (genvar l=0; l<riscv::XLEN/8; l++)
        assign exp_rdata[k][l*8 +: 8] = tb_mem_port_t::shadow_q[{fifo_data[k].paddr[63:3], 3'b0} + l];

      assign fifo_push[k]  = req_ports_i[k].data_req & req_ports_o[k].data_gnt;
      assign fifo_flush[k] = req_ports_i[k].kill_req;
      assign fifo_pop[k]   = req_ports_o[k].data_rvalid & ~req_ports_i[k].kill_req;

      fifo_v3 #(
        .dtype(resp_fifo_t)
      ) i_resp_fifo (
        .clk_i       ( clk_i            ),
        .rst_ni      ( rst_ni           ),
        .flush_i     ( fifo_flush[k]    ),
        .testmode_i  ( '0               ),
        .full_o      (                  ),
        .empty_o     (                  ),
        .usage_o     (                  ),
        .data_i      ( fifo_data_in[k]  ),
        .push_i      ( fifo_push[k]     ),
        .data_o      ( fifo_data[k]     ),
        .pop_i       ( fifo_pop[k]      )
      );
    end
  endgenerate

  // memory and shadow memory region that are addressed by current AMO
  for (genvar k=0; k<8; k++) begin
    assign amo_act_mem[k*8 +: 8] = tb_mem_port_t::memory_q[amo_req_i.operand_a + k];
    assign amo_shadow[k*8 +: 8] = tb_mem_port_t::shadow_q[amo_req_i.operand_a + k];
  end

  tb_readport #(
    .PortName      ( "RD0"         ),
    .FlushRate     ( FlushRate     ),
    .KillRate      ( KillRate      ),
    .TlbHitRate    ( TlbHitRate    ),
    .MemWords      ( MemWords      ),
    .CachedAddrBeg ( CachedAddrBeg ),
    .CachedAddrEnd ( CachedAddrEnd ),
    .RndSeed       ( 5555555       ),
    .Verbose       ( Verbose       )
  ) i_tb_readport0 (
    .clk_i           ( clk_i               ),
    .rst_ni          ( rst_ni              ),
    .test_name_i     ( test_name           ),
    .req_rate_i      ( req_rate[0]         ),
    .seq_type_i      ( seq_type[0]         ),
    .tlb_rand_en_i   ( tlb_rand_en         ),
    .flush_rand_en_i ( flush_rand_en       ),
    .seq_run_i       ( seq_run             ),
    .seq_num_resp_i  ( seq_num_resp        ),
    .seq_last_i      ( seq_last            ),
    .seq_done_o      ( seq_done[0]         ),
    .exp_paddr_o     ( exp_paddr[0]        ),
    .exp_size_i      ( fifo_data[0].size   ),
    .exp_paddr_i     ( fifo_data[0].paddr  ),
    .exp_rdata_i     ( exp_rdata[0]        ),
    .act_paddr_i     ( act_paddr[0]        ),
    .flush_o         ( flush[0]            ),
    .flush_ack_i     ( flush_ack_o         ),
    .dut_req_port_o  ( req_ports_i[0]      ),
    .dut_req_port_i  ( req_ports_o[0]      )
    );

  tb_readport #(
    .PortName      ( "RD1"         ),
    .FlushRate     ( FlushRate     ),
    .KillRate      ( KillRate      ),
    .TlbHitRate    ( TlbHitRate    ),
    .MemWords      ( MemWords      ),
    .CachedAddrBeg ( CachedAddrBeg ),
    .CachedAddrEnd ( CachedAddrEnd ),
    .RndSeed       ( 3333333       ),
    .Verbose       ( Verbose       )
  ) i_tb_readport1 (
    .clk_i           ( clk_i               ),
    .rst_ni          ( rst_ni              ),
    .test_name_i     ( test_name           ),
    .req_rate_i      ( req_rate[1]         ),
    .seq_type_i      ( seq_type[1]         ),
    .tlb_rand_en_i   ( tlb_rand_en         ),
    .flush_rand_en_i ( flush_rand_en       ),
    .seq_run_i       ( seq_run             ),
    .seq_num_resp_i  ( seq_num_resp        ),
    .seq_last_i      ( seq_last            ),
    .exp_paddr_o     ( exp_paddr[1]        ),
    .exp_size_i      ( fifo_data[1].size   ),
    .exp_paddr_i     ( fifo_data[1].paddr  ),
    .exp_rdata_i     ( exp_rdata[1]        ),
    .act_paddr_i     ( act_paddr[1]        ),
    .seq_done_o      ( seq_done[1]         ),
    .flush_o         ( flush[1]            ),
    .flush_ack_i     ( flush_ack_o         ),
    .dut_req_port_o  ( req_ports_i[1]      ),
    .dut_req_port_i  ( req_ports_o[1]      )
  );

  tb_writeport #(
    .PortName      ( "WR0"         ),
    .MemWords      ( MemWords      ),
    .CachedAddrBeg ( CachedAddrBeg ),
    .CachedAddrEnd ( CachedAddrEnd ),
    .RndSeed       ( 7777777       ),
    .Verbose       ( Verbose       )
  ) i_tb_writeport (
    .clk_i          ( clk_i               ),
    .rst_ni         ( rst_ni              ),
    .test_name_i    ( test_name           ),
    .req_rate_i     ( req_rate[2]         ),
    .seq_type_i     ( seq_type[2]         ),
    .seq_run_i      ( seq_run             ),
    .seq_num_vect_i ( seq_num_write       ),
    .seq_last_i     ( seq_last            ),
    .seq_done_o     ( seq_done[2]         ),
    .dut_req_port_o ( req_ports_i[2]      ),
    .dut_req_port_i ( req_ports_o[2]      )
  );

  tb_amoport  #(
    .PortName      ("AMO0"),
    .MemWords      ( MemWords      ),
    .CachedAddrBeg ( CachedAddrBeg ),
    .CachedAddrEnd ( CachedAddrEnd ),
    .RndSeed       ( 1111111       ),
    .Verbose       ( Verbose       )
  ) i_tb_amoport (
    .clk_i               ( clk_i          ),
    .rst_ni              ( rst_ni         ),
    .test_name_i         ( test_name      ),
    .seq_run_i           ( seq_run        ),
    .seq_num_amo_i       ( seq_num_amo    ),
    .seq_last_i          ( seq_last       ),
    .seq_done_o          ( seq_done[3]    ),
    .act_mem_i           ( amo_act_mem    ),
    .exp_mem_i           ( amo_shadow     ),
    .exp_result_i        ( amo_exp_result ),
    .dut_amo_req_port_o  ( amo_req_i      ),
    .dut_amo_resp_port_i ( amo_resp_o     )
  );

  // Translate write requests for shadow memory.
  initial begin
    forever begin
      `WAIT_CYC(clk_i,1)

      write_en    = req_ports_i[2].data_req & req_ports_o[2].data_gnt & req_ports_i[2].data_we;
      write_paddr = {req_ports_i[2].address_tag,  req_ports_i[2].address_index};
      write_data  = req_ports_i[2].data_wdata;
      write_be    = req_ports_i[2].data_be;
    end
  end

  assign flush_i = |flush;

///////////////////////////////////////////////////////////////////////////////
// simulation coordinator process
///////////////////////////////////////////////////////////////////////////////

// TODO: implement CSR / controller
// flush_i, flush_ack_o, enable_i, miss_o, wbuffer_empty_o


  initial begin : p_stim
    test_name        = "";
    seq_type         = '{default: RANDOM_SEQ};
    req_rate         = '{default: 7'd75};
    seq_run          = 1'b0;
    seq_last         = 1'b0;
    seq_num_resp     = '0;
    seq_num_write    = '0;
    // seq_done
    end_of_sim       = 0;
    rst_ni           = 0;
    // randomization settings
    mem_rand_en      = 0;
    tlb_rand_en      = 0;
    inv_rand_en      = 0;
    amo_rand_en      = 0;
    flush_rand_en    = 0;
    // cache ctrl
    flush[2]         = 0;
    // flush_ack_o
    enable_i         = 0;
    // miss_o

    // Print some info
    $display("TB> current configuration:");
    $display("TB> MemWords        %d",   MemWords);
    $display("TB> CachedAddrBeg   %16X", CachedAddrBeg);
    $display("TB> CachedAddrEnd   %16X", CachedAddrEnd);
    $display("TB> MemRandHitRate  %d",   MemRandHitRate);
    $display("TB> MemRandInvRate  %d",   MemRandInvRate);

    // Reset cycles
    `APPL_WAIT_CYC(clk_i,100)
    rst_ni        = 1'b1;
    `APPL_WAIT_CYC(clk_i,100)

    $display("TB> start with test sequences");

    // Apply each test until seq_num_resp memory requests have successfully completed
    ///////////////////////////////////////////////
    test_name    = "TEST 0 -- random read -- disabled cache";

    // Config
    enable_i     = 0;
    seq_type     = '{default: RANDOM_SEQ};
    req_rate     = '{default: 7'd50};

    // Cache disabled ~> all requests should use bypass port
    data_mem_port.set_region(0, MemBytes - 1);

    runSeq(nReadVectors);
    flushCache();
    tb_mem_port_t::check_mem();

    ///////////////////////////////////////////////
    test_name    = "TEST 1 -- linear read -- disabled cache";

    // Config
    enable_i     = 0;
    seq_type     = '{default: LINEAR_SEQ};
    req_rate     = '{default: 7'd50};

    runSeq(nReadVectors);
    flushCache();
    tb_mem_port_t::check_mem();

    ///////////////////////////////////////////////
    test_name    = "TEST 2 -- random read -- enabled cache";

    // Config
    enable_i     = 1;
    seq_type     = '{default: RANDOM_SEQ};
    req_rate     = '{default: 7'd50};

    runSeq(nReadVectors);
    flushCache();
    tb_mem_port_t::check_mem();

    ///////////////////////////////////////////////
    test_name    = "TEST 3 -- linear read -- enabled cache";

    // Config
    enable_i     = 1;
    seq_type     = '{default: LINEAR_SEQ};
    req_rate     = '{default: 7'd50};

    runSeq(nReadVectors);
    flushCache();
    tb_mem_port_t::check_mem();

    ///////////////////////////////////////////////
    test_name    = "TEST 4 -- random read -- enabled cache + tlb, mem contentions";

    // Config
    enable_i     = 1;
    tlb_rand_en  = 1;
    mem_rand_en  = 1;
    seq_type     = '{default: RANDOM_SEQ};
    req_rate     = '{default: 7'd50};

    runSeq(nReadVectors);
    flushCache();
    tb_mem_port_t::check_mem();

    ///////////////////////////////////////////////
    test_name    = "TEST 5 -- linear read -- enabled cache + tlb, mem contentions";

    // Config
    enable_i     = 1;
    tlb_rand_en  = 1;
    mem_rand_en  = 1;
    seq_type     = '{default: LINEAR_SEQ};
    req_rate     = '{default: 7'd50};

    runSeq(nReadVectors);
    flushCache();
    tb_mem_port_t::check_mem();

    ///////////////////////////////////////////////
    test_name    = "TEST 6 -- random read -- enabled cache + tlb, mem contentions + invalidations";

    // Config
    enable_i     = 1;
    tlb_rand_en  = 1;
    mem_rand_en  = 1;
    inv_rand_en  = 1;
    seq_type     = '{default: RANDOM_SEQ};
    req_rate     = '{default: 7'd50};

    runSeq(nReadVectors);
    flushCache();
    tb_mem_port_t::check_mem();

    ///////////////////////////////////////////////
    test_name    = "TEST 7 -- random read/write -- disabled cache";

    // Config
    enable_i     = 0;
    tlb_rand_en  = 0;
    mem_rand_en  = 0;
    inv_rand_en  = 0;
    seq_type     = '{default: RANDOM_SEQ};
    req_rate     = '{default: 7'd25};

    runSeq(nReadVectors,nWriteVectors);
    flushCache();
    tb_mem_port_t::check_mem();

    ///////////////////////////////////////////////
    test_name    = "TEST 8 -- random read/write -- enabled cache";

    // Config
    enable_i     = 1;
    tlb_rand_en  = 0;
    mem_rand_en  = 0;
    inv_rand_en  = 0;
    seq_type     = '{default: RANDOM_SEQ};
    req_rate     = '{default: 7'd25};

    runSeq(nReadVectors,2*nWriteVectors);
    flushCache();
    tb_mem_port_t::check_mem();

    ///////////////////////////////////////////////
    test_name    = "TEST 9 -- random read/write -- enabled cache + tlb, mem contentions + invalidations";

    // Config
    enable_i     = 1;
    tlb_rand_en  = 1;
    mem_rand_en  = 1;
    inv_rand_en  = 1;
    seq_type     = '{default: RANDOM_SEQ};
    req_rate     = '{default: 7'd25};

    runSeq(nReadVectors,2*nWriteVectors);
    flushCache();
    tb_mem_port_t::check_mem();

    ///////////////////////////////////////////////
    test_name    = "TEST 10 -- linear burst write -- enabled cache";

    // Config
    enable_i     = 1;
    tlb_rand_en  = 0;
    mem_rand_en  = 0;
    inv_rand_en  = 0;
    seq_type     = '{LINEAR_SEQ, IDLE_SEQ, IDLE_SEQ};
    req_rate     = '{100, 0, 0};

    runSeq(0,nWriteVectors);
    flushCache();
    tb_mem_port_t::check_mem();

    ///////////////////////////////////////////////
    test_name    = "TEST 11 -- linear burst write with hot cache";

    // Config
    enable_i     = 1;
    tlb_rand_en  = 0;
    mem_rand_en  = 0;
    inv_rand_en  = 0;
    seq_type     = '{IDLE_SEQ, IDLE_SEQ, LINEAR_SEQ};
    req_rate     = '{default:100};

    runSeq((CachedAddrBeg>>3)+(2**(DCACHE_INDEX_WIDTH-3))*DCACHE_SET_ASSOC);
    seq_type     = '{LINEAR_SEQ, IDLE_SEQ, IDLE_SEQ};
    runSeq(0,(CachedAddrBeg>>3)+(2**(DCACHE_INDEX_WIDTH-3))*DCACHE_SET_ASSOC);
    flushCache();
    tb_mem_port_t::check_mem();

    ///////////////////////////////////////////////
    test_name    = "TEST 12 -- random write bursts -- enabled cache";

    // Config
    enable_i     = 1;
    tlb_rand_en  = 0;
    mem_rand_en  = 0;
    inv_rand_en  = 0;
    seq_type     = '{BURST_SEQ, RANDOM_SEQ, RANDOM_SEQ};
    req_rate     = '{75, 0, 0};

    runSeq(0,nWriteVectors);
    flushCache();
    tb_mem_port_t::check_mem();

    ///////////////////////////////////////////////
    test_name    = "TEST 13 -- random write bursts -- enabled cache + tlb, mem contentions + invalidations";

    // Config
    enable_i     = 1;
    tlb_rand_en  = 1;
    mem_rand_en  = 1;
    inv_rand_en  = 1;
    seq_type     = '{BURST_SEQ, IDLE_SEQ, IDLE_SEQ};
    req_rate     = '{75, 0, 0};

    runSeq(0,nWriteVectors);
    flushCache();
    tb_mem_port_t::check_mem();

    ///////////////////////////////////////////////
    test_name    = "TEST 14 -- random write/read-- enabled cache + tlb, mem contentions + invalidations";

    // Config
    enable_i     = 1;
    tlb_rand_en  = 1;
    mem_rand_en  = 1;
    inv_rand_en  = 1;
    seq_type     = '{RANDOM_SEQ, RANDOM_SEQ, RANDOM_SEQ};
    req_rate     = '{default:25};

    runSeq(nReadVectors,nWriteVectors);
    flushCache();
    tb_mem_port_t::check_mem();

    ///////////////////////////////////////////////
    test_name    = "TEST 15 -- short wrapping sequences to provoke writebuffer hits";

    // Config
    enable_i     = 1;
    tlb_rand_en  = 0;
    mem_rand_en  = 0;
    inv_rand_en  = 0;
    seq_type     = '{WRAP_SEQ, IDLE_SEQ, WRAP_SEQ};
    req_rate     = '{100,0,20};

    runSeq(nReadVectors,nWriteVectors);
    flushCache();
    tb_mem_port_t::check_mem();

    ///////////////////////////////////////////////
    test_name    = "TEST 16 -- random write/read-- enabled cache + tlb, mem contentions + invalidations + random flushes";

    // Config
    enable_i      = 1;
    tlb_rand_en   = 1;
    mem_rand_en   = 1;
    inv_rand_en   = 1;
    flush_rand_en = 1;
    seq_type      = '{RANDOM_SEQ, RANDOM_SEQ, RANDOM_SEQ};
    req_rate      = '{default:25};

    runSeq(nReadVectors,nWriteVectors);
    flushCache();
    tb_mem_port_t::check_mem();

    ///////////////////////////////////////////////
    test_name    = "TEST 17 -- set contention -- enabled cache";

    // Config
    enable_i     = 1;
    tlb_rand_en  = 1;
    mem_rand_en  = 0;
    inv_rand_en  = 0;
    seq_type     = '{CONST_SEQ, IDLE_SEQ, SET_SEQ};
    req_rate     = '{50,0,2};

    runSeq(0.2*nReadVectors,2*nWriteVectors);
    flushCache();
    tb_mem_port_t::check_mem();

    ///////////////////////////////////////////////
    test_name    = "TEST 18 -- AMOs";

    // Config
    enable_i     = 1;
    tlb_rand_en  = 1;
    mem_rand_en  = 0;
    inv_rand_en  = 0;
    seq_type     = '{CONST_SEQ, IDLE_SEQ, SET_SEQ};
    req_rate     = '{50,0,2};

    runAMOs(nAMOs,1); // Last sequence flag, terminates agents
    flushCache();
    tb_mem_port_t::check_mem();

    /////////////////////////////////////////////
    end_of_sim = 1;
    $display("TB> end test sequences");
    tb_mem_port_t::report_mem();
  end

endmodule

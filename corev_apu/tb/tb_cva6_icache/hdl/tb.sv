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
// Date: 15.08.2018
// Description: testbench for icache. includes the following tests:
//
// 0) random accesses with disabled cache
// 1) random accesses with enabled cache to cacheable and noncacheable memory
// 2) linear, wrapping sweep with enabled cache
// 3) 1) with random stalls on the memory side and TLB side
// 4) nr 3) with random invalidations
//
// note that we use a simplified address translation scheme to emulate the TLB.
// (random offsets).



`include "tb.svh"

module tb import tb_pkg::*; import ariane_pkg::*; import wt_cache_pkg::*; #()();

  // leave this
  timeunit 1ps;
  timeprecision 1ps;

  // number of 32bit words
  parameter MemBytes                   = 2**ICACHE_INDEX_WIDTH * 4 * 32;
  parameter MemWords                   = MemBytes>>2;
  parameter logic [63:0] CachedAddrBeg = MemBytes/4;
  parameter logic [63:0] CachedAddrEnd = MemBytes;

  localparam ariane_cfg_t Cfg = '{
    RASDepth:              2,
    BTBEntries:            32,
    BHTEntries:            128,
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
    CachedRegionAddrBase: {CachedAddrBeg},
    CachedRegionLength:   {CachedAddrEnd-CachedAddrBeg+64'b1},
    // cache config
    Axi64BitCompliant:     1'b0,
    SwapEndianess:         1'b0,
    // debug
    DmBaseAddress:         64'h0,
    NrPMPEntries:          0
  };

  // rates are in percent
  parameter TlbRandHitRate   = 50;
  parameter MemRandHitRate   = 50;
  parameter MemRandInvRate   = 10;

  parameter SeqRate          = 90;
  parameter S1KillRate       = 5;
  parameter S2KillRate       = 5;
  parameter FlushRate        = 1;

  parameter logic [63:0] TlbOffset = 4*1024;//use multiples of 4kB pages!


///////////////////////////////////////////////////////////////////////////////
// MUT signal declarations
///////////////////////////////////////////////////////////////////////////////

  logic           clk_i;
  logic           rst_ni;
  logic           flush_i;
  logic           en_i;
  logic           miss_o;
  icache_areq_i_t areq_i;
  icache_areq_o_t areq_o;
  icache_dreq_i_t dreq_i;
  icache_dreq_o_t dreq_o;
  logic           mem_rtrn_vld_i;
  icache_rtrn_t   mem_rtrn_i;
  logic           mem_data_req_o;
  logic           mem_data_ack_i;
  icache_req_t    mem_data_o;


///////////////////////////////////////////////////////////////////////////////
// TB signal declarations
///////////////////////////////////////////////////////////////////////////////

  logic stim_start, stim_end, end_of_sim, acq_done;
  logic [63:0] num_vectors;
  string test_name;

  logic mem_rand_en;
  logic inv_rand_en;
  logic io_rand_en;
  logic tlb_rand_en;
  logic exception_en;

  logic [63:0] stim_vaddr;
  logic [63:0] exp_data;
  logic [63:0] exp_vaddr;
  logic stim_push, stim_flush, stim_full;
  logic exp_empty, exp_pop;

  logic dut_out_vld, dut_in_rdy;

///////////////////////////////////////////////////////////////////////////////
// Clock Process
///////////////////////////////////////////////////////////////////////////////

  always @*
  begin
    do begin
      clk_i = 1;#(CLK_HI);
      clk_i = 0;#(CLK_LO);
    end while (end_of_sim == 1'b0);
      repeat (100) begin
        // generate a few extra cycle to allow response acquisition to complete
        clk_i = 1;#(CLK_HI);
        clk_i = 0;#(CLK_LO);
      end
  end

///////////////////////////////////////////////////////////////////////////////
// Helper tasks
///////////////////////////////////////////////////////////////////////////////

  // prepare tasks...

  task automatic genRandReq();
    automatic bit ok;
    automatic logic [63:0] val;
    dreq_i.req     = 0;
    dreq_i.kill_s1 = 0;
    dreq_i.kill_s2 = 0;
    num_vectors    = 100000;
    stim_end       = 0;

    stim_start     = 1;
    `APPL_WAIT_CYC(clk_i,10)
    stim_start     = 0;

    // start with clean cache
    flush_i        = 1;
    `APPL_WAIT_CYC(clk_i,1)
    flush_i        = 0;

     while(~acq_done) begin
      // randomize request
      dreq_i.req = 0;
      ok = randomize(val) with {val > 0; val <= 100;};
      if (val < SeqRate) begin
        dreq_i.req = 1;
        // generate random address
        ok = randomize(val) with {val >= 0; val < (MemBytes-TlbOffset)>>2;};
        dreq_i.vaddr = val<<2;// align to 4Byte
        // generate random control events
        ok = randomize(val) with {val > 0; val <= 100;};
        dreq_i.kill_s1 = (val < S1KillRate);
        ok = randomize(val) with {val > 0; val <= 100;};
        dreq_i.kill_s2 = (val < S2KillRate);
        ok = randomize(val) with {val > 0; val <= 100;};
        flush_i = (val < FlushRate);
        `APPL_WAIT_SIG(clk_i, dut_in_rdy)
      end else begin
        `APPL_WAIT_CYC(clk_i,1)
      end
    end
    stim_end       = 1;
  endtask : genRandReq


  task automatic genSeqRead();
    automatic bit ok;
    automatic logic [63:0] val;
    automatic logic [63:0] addr;
    dreq_i.req     = 0;
    dreq_i.kill_s1 = 0;
    dreq_i.kill_s2 = 0;
    num_vectors    = 32*4*1024;
    addr           = 0;
    stim_end       = 0;

    stim_start     = 1;
    `APPL_WAIT_CYC(clk_i,10)
    stim_start     = 0;

    // start with clean cache
    flush_i        = 1;
    `APPL_WAIT_CYC(clk_i,1)
    flush_i        = 0;

    while(~acq_done) begin
      dreq_i.req = 1;
      dreq_i.vaddr = addr;
      // generate linear read
      addr = (addr + 4) % (MemBytes - TlbOffset);
      `APPL_WAIT_SIG(clk_i, dut_in_rdy)
    end
    stim_end       = 1;
  endtask : genSeqRead


///////////////////////////////////////////////////////////////////////////////
// TLB and memory emulation
///////////////////////////////////////////////////////////////////////////////

  tlb_emul #(
    .TlbRandHitRate(TlbRandHitRate)
  ) i_tlb_emul (
    .clk_i          ( clk_i        ),
    .rst_ni         ( rst_ni       ),
    .tlb_rand_en_i  ( tlb_rand_en  ),
    .exception_en_i ( exception_en ),
    .tlb_offset_i   ( TlbOffset    ),
    // icache interface
    .req_i          ( areq_o       ),
    .req_o          ( areq_i       )
  );

  mem_emul #(
    .MemRandHitRate ( MemRandHitRate ),
    .MemRandInvRate ( MemRandInvRate ),
    .MemWords       ( MemWords       ),
    .CachedAddrBeg  ( CachedAddrBeg  )
  ) i_mem_emul (
    .clk_i          ( clk_i          ),
    .rst_ni         ( rst_ni         ),
    .mem_rand_en_i  ( mem_rand_en    ),
    .io_rand_en_i   ( io_rand_en     ),
    .inv_rand_en_i  ( inv_rand_en    ),
    .tlb_offset_i   ( TlbOffset      ),
    .stim_vaddr_i   ( stim_vaddr     ),
    .stim_push_i    ( stim_push      ),
    .stim_flush_i   ( stim_flush     ),
    .stim_full_o    ( stim_full      ),
    .exp_data_o     ( exp_data       ),
    .exp_vaddr_o    ( exp_vaddr      ),
    .exp_empty_o    ( exp_empty      ),
    .exp_pop_i      ( exp_pop        ),
    .mem_data_req_i ( mem_data_req_o ),
    .mem_data_ack_o ( mem_data_ack_i ),
    .mem_data_i     ( mem_data_o     ),
    .mem_rtrn_vld_o ( mem_rtrn_vld_i ),
    .mem_rtrn_o     ( mem_rtrn_i     )
  );

///////////////////////////////////////////////////////////////////////////////
// MUT
///////////////////////////////////////////////////////////////////////////////

  cva6_icache  #(
    .ArianeCfg(Cfg)
    ) dut (
    .clk_i          ( clk_i          ),
    .rst_ni         ( rst_ni         ),
    .flush_i        ( flush_i        ),
    .en_i           ( en_i           ),
    .miss_o         ( miss_o         ),
    .areq_i         ( areq_i         ),
    .areq_o         ( areq_o         ),
    .dreq_i         ( dreq_i         ),
    .dreq_o         ( dreq_o         ),
    .mem_rtrn_vld_i ( mem_rtrn_vld_i ),
    .mem_rtrn_i     ( mem_rtrn_i     ),
    .mem_data_req_o ( mem_data_req_o ),
    .mem_data_ack_i ( mem_data_ack_i ),
    .mem_data_o     ( mem_data_o     )
  );

  // connect interface to expected response channel of memory emulation
  assign stim_vaddr = dreq_i.vaddr;
  assign stim_push  = dreq_i.req & dreq_o.ready & (~dreq_i.kill_s1) & (~flush_i);
  assign stim_flush = 0;
  assign exp_pop    = (dreq_o.valid | dreq_i.kill_s2) & (~exp_empty);

///////////////////////////////////////////////////////////////////////////////
// stimuli application process
///////////////////////////////////////////////////////////////////////////////

  assign dut_in_rdy = dreq_o.ready;

  initial   // process runs just once
  begin : p_stim
    end_of_sim       = 0;
    num_vectors      = 0;
    stim_start       = 0;
    stim_end         = 0;

    rst_ni           = 0;

    mem_rand_en      = 0;
    tlb_rand_en      = 0;
    inv_rand_en      = 0;
    exception_en     = 0;
    io_rand_en       = 0;

    dreq_i.req       = 0;
    dreq_i.kill_s1   = 0;
    dreq_i.kill_s2   = 0;
    dreq_i.vaddr     = 0;
    flush_i          = 0;
    en_i             = 0;

    // print some info
    $display("TB> current configuration:");
    $display("TB> MemWords       %d",   MemWords);
    $display("TB> CachedAddrBeg  %16X", CachedAddrBeg);
    $display("TB> TlbRandHitRate %d",   TlbRandHitRate);
    $display("TB> MemRandHitRate %d",   MemRandHitRate);
    $display("TB> MemRandInvRate %d",   MemRandInvRate);
    $display("TB> S1KillRate     %d",   S1KillRate);
    $display("TB> S2KillRate     %d",   S2KillRate);
    $display("TB> FlushRate      %d",   FlushRate);

    `APPL_WAIT_CYC(clk_i,100);
    $display("TB> choose TLB offset  %16X", TlbOffset);

    // reset cycles
    `APPL_WAIT_CYC(clk_i,100);
    rst_ni        = 1'b1;
    `APPL_WAIT_CYC(clk_i,100);

    $display("TB> stimuli application started");
    // apply each test until NUM_ACCESSES memory
    // requests have successfully completed
    ///////////////////////////////////////////////
    // TEST 0
    en_i = 0;
    genRandReq();
    `APPL_WAIT_CYC(clk_i,200);
    ///////////////////////////////////////////////
    // TEST 1
    test_name = "TEST1, enabled cache";
    en_i = 1;
    genRandReq();
    `APPL_WAIT_CYC(clk_i,200);
    ///////////////////////////////////////////////
    // TEST 2
    test_name = "TEST2, enabled cache, sequential reads";
    en_i        = 1;
    genSeqRead();
    `APPL_WAIT_CYC(clk_i,200);
    ///////////////////////////////////////////////
    // TEST 3
    test_name = "TEST3, enabled cache, random stalls in mem and TLB side";
    en_i        = 1;
    mem_rand_en = 1;
    tlb_rand_en = 1;
    genRandReq();
    `APPL_WAIT_CYC(clk_i,200);
    ///////////////////////////////////////////////
    // TEST 4
    test_name = "TEST4, +random invalidations";
    en_i        = 1;
    mem_rand_en = 1;
    tlb_rand_en = 1;
    inv_rand_en = 1;
    genRandReq();
    `APPL_WAIT_CYC(clk_i,200);
    ///////////////////////////////////////////////
    end_of_sim = 1;
    $display("TB> stimuli application ended");
  end

///////////////////////////////////////////////////////////////////////////////
// stimuli acquisition process
///////////////////////////////////////////////////////////////////////////////

  assign dut_out_vld = dreq_o.valid;

  initial   // process runs just once
  begin : p_acq

    bit ok;
    progress status;
    string failingTests, tmpstr;
    int    n;

    status       = new();
    failingTests = "";
    acq_done     = 0;

    ///////////////////////////////////////////////
    // loop over tests
    n=0;
    while (~end_of_sim) begin
      // wait for stimuli application
      `ACQ_WAIT_SIG(clk_i, stim_start);
      $display("TB: ----------------------------------------------------------------------\n");
      $display("TB> %s", test_name);

      status.reset(num_vectors);
      acq_done = 0;
      for (int k=0;k<num_vectors;k++) begin

        // wait for response
        `ACQ_WAIT_SIG(clk_i, dut_out_vld);

        ok=(dreq_o.data == exp_data[FETCH_WIDTH-1:0]) && (dreq_o.vaddr == exp_vaddr);

        if(!ok) begin
          tmpstr =
          $psprintf("vector: %02d - %06d -- exp_vaddr: %16X -- act_vaddr : %16X -- exp_data: %08X -- act_data: %08X",
            n, k, exp_vaddr, dreq_o.vaddr, exp_data[FETCH_WIDTH-1:0], dreq_o.data);
          failingTests = $psprintf("%sTB: %s\n", failingTests, tmpstr);
          $display("TB> %s", tmpstr);
        end
        status.addRes(!ok);
        status.print();
      end
      acq_done = 1;
      n++;
      // wait for stimuli application end
      `ACQ_WAIT_SIG(clk_i, stim_end);
      `ACQ_WAIT_CYC(clk_i,100);
    end
    ///////////////////////////////////////////////

    status.printToFile("summary.rep", 1);

    if(status.totErrCnt == 0) begin
      $display("TB: ----------------------------------------------------------------------\n");
      $display("TB: PASSED %0d VECTORS", status.totAcqCnt);
      $display("TB: ----------------------------------------------------------------------\n");
    end else begin
      $display("TB: ----------------------------------------------------------------------\n");
      $display("TB: FAILED %0d OF %0d VECTORS\n", status.totErrCnt, status.totAcqCnt);
      $display("TB: failing tests:");
      $display("%s", failingTests);
      $display("TB: ----------------------------------------------------------------------\n");
    end
  end

endmodule













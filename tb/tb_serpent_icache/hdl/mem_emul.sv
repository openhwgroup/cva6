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
// Description: simple emulation layer for the memory subsystem.
//

import ariane_pkg::*;
import serpent_cache_pkg::*;

module mem_emul #(
  parameter              MemRandHitRate = 10, //in percent
  parameter              MemRandInvRate = 5,  //in percent
  parameter              MemWords       = 1024*1024,// in 32bit words
  parameter logic [63:0] CachedAddrBeg  = MemWords/2
) (
  input logic            clk_i,
  input logic            rst_ni,
  // some tb signals to enable randomization, etc
  input logic            mem_rand_en_i,
  input logic            io_rand_en_i,
  input logic            inv_rand_en_i,
  input logic [63:0]     tlb_offset_i,
  // stimuli interface to get expected responses
  input  logic [63:0]    stim_vaddr_i,
  input  logic           stim_push_i,
  input  logic           stim_flush_i,
  output logic           stim_full_o,
  output logic [63:0]    exp_data_o,
  output logic [63:0]    exp_vaddr_o,
  output logic           exp_empty_o,
  input  logic           exp_pop_i,
  // icache interface
  output logic           mem_rtrn_vld_o,
  output icache_rtrn_t   mem_rtrn_o,
  input  logic           mem_data_req_i,
  output logic           mem_data_ack_o,
  input  icache_req_t    mem_data_i
);

  logic        mem_ready_q, mem_inv_q;
  logic [63:0] rand_addr_q;

  icache_req_t outfifo_data;
  logic outfifo_pop, outfifo_push, outfifo_full, outfifo_empty;
  icache_rtrn_t infifo_data;
  logic infifo_pop, infifo_push, infifo_full, infifo_empty;

  logic [63:0] stim_addr;
  logic exp_empty;

  logic [31:0] mem_array [MemWords-1:0];
  logic [31:0] mem_array_shadow [MemWords-1:0];
  logic initialized_q;

  logic [31:0] inval_addr_queue[$];
  logic [31:0] inval_data_queue[$];

  // sequential process holding the state of the memory readout process
  always_ff @(posedge clk_i or negedge rst_ni) begin : p_tlb_rand
    automatic bit ok  = 0;
    automatic int rnd = 0;
    automatic logic [31:0] val;
    automatic logic [63:0] lval;

    if(~rst_ni) begin
      mem_ready_q   <= '0;
      mem_inv_q     <= '0;
      rand_addr_q   <= '0;
      initialized_q <= '0;
    end else begin

      // fill the memory once with random data
      if (~initialized_q) begin
        for (int k=0; k<MemWords; k++) begin
          ok=randomize(val);
          mem_array[k]        <= val;
          mem_array_shadow[k] <= val;
        end
          initialized_q       <= 1;
      end

      // re-randomize noncacheable I/O space if requested
      if (io_rand_en_i) begin
        for (int k=0; k<CachedAddrBeg; k++) begin
          ok = randomize(val);
          mem_array[k]        <= val;
        end
      end

      // generate random contentions
      if (mem_rand_en_i) begin
        ok = randomize(rnd) with {rnd > 0; rnd <= 100;};
        if(rnd < MemRandHitRate) begin
          mem_ready_q <= '1;
        end else
          mem_ready_q <= '0;
      end else begin
        mem_ready_q <= '1;
      end

      // generate random invalidations

      if (inv_rand_en_i) begin
        if (infifo_push) begin
          // update coherent memory view for expected responses
          while(inval_addr_queue.size()>0)begin
            lval = inval_addr_queue.pop_back();
            val  = inval_data_queue.pop_back();
            mem_array_shadow[lval] <= val;
          end
        end

        ok = randomize(rnd) with {rnd > 0; rnd <= 100;};
        if(rnd < MemRandInvRate) begin
          mem_inv_q = '1;
          ok = randomize(lval) with {lval>=0; lval<MemWords;};
          ok = randomize(val);
          // save for coherent view above
          inval_addr_queue.push_front(lval);
          inval_data_queue.push_front(val);
          // overwrite the memory with new random data value
          rand_addr_q     <= lval<<2;
          mem_array[lval] <= val;
        end else begin
          mem_inv_q <= '0;
        end
      end
    end
  end




  // readout process
  always_comb begin : proc_mem
    infifo_push       = 0;
    infifo_data       = '0;
    outfifo_pop       = 0;
    infifo_data.rtype = ICACHE_IFILL_ACK;

    // generate random invalidation
    if (mem_inv_q) begin

      infifo_data.rtype = ICACHE_INV_REQ;

      // since we do not keep a mirror tag table here,
      // we allways invalidate all ways of the aliased index.
      // this is not entirely correct and will produce
      // too many invalidations
      infifo_data.inv.idx = rand_addr_q[ICACHE_INDEX_WIDTH-1:0];
      infifo_data.inv.all = '1;
      infifo_push         = 1'b1;

    end else if ((~outfifo_empty) && (~infifo_full) && mem_ready_q) begin
      outfifo_pop     = 1'b1;
      infifo_push     = 1'b1;

      // address goes to I/O space
      if (outfifo_data.nc) begin
        infifo_data.nc  = 1'b1;
        infifo_data.f4b = 1'b1;
        // replicate words (this is done in openpiton, too)
        // note: openpiton replicates the words here.
        for (int k=0; k<ICACHE_LINE_WIDTH/32; k++) begin
          infifo_data.data[k*32 +:32] = mem_array[outfifo_data.paddr>>2];
        end
        infifo_data.data[0 +:32] = mem_array[outfifo_data.paddr>>2];
      end else begin
        infifo_data.nc  = outfifo_data.nc;
        // replicate words (this is done in openpiton, too)
        for (int k=0; k<ICACHE_LINE_WIDTH/32; k++) begin
          infifo_data.data[k*32 +:32] = mem_array[(outfifo_data.paddr>>2) + k];
        end
      end
    end
  end

  fifo_v2 #(
    .dtype(icache_req_t),
    .DEPTH(2)
  ) i_outfifo (
    .clk_i       ( clk_i         ),
    .rst_ni      ( rst_ni        ),
    .flush_i     ( 1'b0          ),
    .testmode_i  ( 1'b0          ),
    .full_o      ( outfifo_full  ),
    .empty_o     ( outfifo_empty ),
    .alm_full_o  (               ),
    .alm_empty_o (               ),
    .data_i      ( mem_data_i    ),
    .push_i      ( outfifo_push  ),
    .data_o      ( outfifo_data  ),
    .pop_i       ( outfifo_pop   )
  );

  assign outfifo_push   = mem_data_req_i & (~outfifo_full);
  assign mem_data_ack_o = outfifo_push;

  fifo_v2 #(
    .dtype(icache_rtrn_t),
    .DEPTH(2)
  ) i_infifo (
    .clk_i       ( clk_i         ),
    .rst_ni      ( rst_ni        ),
    .flush_i     ( 1'b0          ),
    .testmode_i  ( 1'b0          ),
    .full_o      ( infifo_full   ),
    .empty_o     ( infifo_empty  ),
    .alm_full_o  (               ),
    .alm_empty_o (               ),
    .data_i      ( infifo_data   ),
    .push_i      ( infifo_push   ),
    .data_o      ( mem_rtrn_o    ),
    .pop_i       ( infifo_pop    )
  );

  assign infifo_pop     = ~infifo_empty;
  assign mem_rtrn_vld_o = infifo_pop;

  // this is to readout the expected responses
  fifo_v2 #(
    .DATA_WIDTH(64),
    .DEPTH(3)
  ) i_stimuli_fifo (
    .clk_i       ( clk_i         ),
    .rst_ni      ( rst_ni        ),
    .flush_i     ( stim_flush_i  ),
    .testmode_i  ( 1'b0          ),
    .full_o      ( stim_full_o   ),
    .empty_o     ( exp_empty     ),
    .alm_full_o  (               ),
    .alm_empty_o (               ),
    .data_i      ( stim_vaddr_i  ),
    .push_i      ( stim_push_i   ),
    .data_o      ( stim_addr     ),
    .pop_i       ( exp_pop_i     )
  );

  assign exp_empty_o = exp_empty | stim_flush_i;
  // use last seen memory state in case random invalidations are present
  assign exp_data_o  = (inv_rand_en_i) ? mem_array_shadow[(stim_addr>>2) + (tlb_offset_i>>2)] :
                                         mem_array       [(stim_addr>>2) + (tlb_offset_i>>2)];
  assign exp_vaddr_o = stim_addr;

  align0: assert property (
    @(posedge clk_i) disable iff (~rst_ni) ~exp_empty |-> stim_addr[1:0] == 0)
       else $fatal(1,"stim_addr is not 32bit word aligned");

  align1: assert property (
    @(posedge clk_i) disable iff (~rst_ni) ~outfifo_empty |-> outfifo_data.paddr[1:0] == 0)
       else $fatal(1,"paddr is not 32bit word aligned");


endmodule // mem_emul

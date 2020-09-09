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


`include "tb.svh"



module tb_mem import tb_pkg::*; import ariane_pkg::*; import wt_cache_pkg::*;#(
  parameter string MemName             = "TB_MEM",
  parameter MemRandHitRate             = 10, //in percent
  parameter MemRandInvRate             = 5,  //in percent
  parameter MemWords                   = 1024*1024,// in 64bit words
  parameter logic [63:0] CachedAddrBeg = MemWords/2,
  parameter logic [63:0] CachedAddrEnd = 64'hFFFF_FFFF_FFFF_FFFF
) (
  input logic            clk_i,
  input logic            rst_ni,
  // randomization settings
  input logic            mem_rand_en_i,
  input logic            inv_rand_en_i,
  input logic            amo_rand_en_i,
  // dcache interface
  output logic           mem_rtrn_vld_o,
  output dcache_rtrn_t   mem_rtrn_o,
  input  logic           mem_data_req_i,
  output logic           mem_data_ack_o,
  input  dcache_req_t    mem_data_i,
  // expected response interface
  input  logic           seq_last_i,
  input  logic           check_en_i,
  input  logic           commit_en_i,
  input  logic [7:0]     commit_be_i,
  input  logic [63:0]    commit_paddr_i,
  input  logic           write_en_i,
  input  logic [7:0]     write_be_i,
  input  logic [63:0]    write_data_i,
  input  logic [63:0]    write_paddr_i,
  output logic [63:0]    mem_array_o[MemWords-1:0]
);

    // leave this
    timeunit 1ps;
    timeprecision 1ps;

    logic        mem_ready_q, mem_inv_q;
    logic [63:0] rand_addr_q;

    dcache_req_t outfifo_data;
    logic outfifo_pop, outfifo_push, outfifo_full, outfifo_empty;
    dcache_rtrn_t infifo_data;
    logic infifo_pop, infifo_push, infifo_full, infifo_empty;

    logic initialized_q;
    logic write_en;

    logic [63:0] mem_array_q[MemWords-1:0];

    // this shadow memory  provides a view that is consistent with the one from the core
    // i.e., pending writes are present in this view, and invalidations will not overwrite
    // the corresponding bytes until they have been commited to the normal memory.
    logic [63:0] mem_array_shadow_q[MemWords-1:0];
    logic [7:0]  mem_array_dirty_q[MemWords-1:0];

    assign mem_array_o = mem_array_shadow_q;

    // sequential process holding the state of the memory readout process
    always_ff @(posedge clk_i or negedge rst_ni) begin : p_tlb_rand
        automatic int rnd = 0;
        automatic logic [63:0] val;
        automatic logic [63:0] lval;

        if(~rst_ni) begin
            mem_ready_q   <= '0;
            mem_inv_q     <= '0;
            rand_addr_q   <= '0;
            initialized_q <= '0;
        end else begin

            // fill the memory once with random data
            if (initialized_q) begin
                // commit "virtual" writes (i.e., clear the dirty flags)
                if(commit_en_i) begin
                    for(int k=0; k<8; k++) begin
                        if(commit_be_i[k]) begin
                            mem_array_dirty_q[commit_paddr_i>>3][k] <= 1'b0;
                        end
                    end
                end

                // "virtual" writes coming from TB agent, used to generate expected responses
                if(write_en_i) begin
                    for(int k=0; k<8; k++) begin
                        if(write_be_i[k]) begin
                            mem_array_shadow_q[write_paddr_i>>3][k*8 +: 8] <= write_data_i[k*8 +: 8];
                            mem_array_dirty_q[write_paddr_i>>3][k]         <= 1'b1;
                        end
                    end
                end

                // "real" writes coming via the miss controller
                if(write_en) begin
                    unique case(outfifo_data.size)
                        3'b000: mem_array_q[outfifo_data.paddr>>3][outfifo_data.paddr[2:0]*8  +: 8]  = outfifo_data.data[outfifo_data.paddr[2:0]*8  +: 8];
                        3'b001: mem_array_q[outfifo_data.paddr>>3][outfifo_data.paddr[2:1]*16 +: 16] = outfifo_data.data[outfifo_data.paddr[2:1]*16 +: 16];
                        3'b010: mem_array_q[outfifo_data.paddr>>3][outfifo_data.paddr[2:2]*32 +: 32] = outfifo_data.data[outfifo_data.paddr[2:2]*32 +: 32];
                        3'b011: mem_array_q[outfifo_data.paddr>>3] = outfifo_data.data[0 +: 64];
                        default: begin
                            $fatal(1,"unsupported transfer size for write");
                        end
                    endcase // infifo_data.size
                end
            // initialization with random data
            end else begin
                mem_array_dirty_q      <= '{default:'0};

                for (int k=0; k<MemWords; k++) begin
                    void'(randomize(val));
                    mem_array_q[k]        <= val;
                    mem_array_shadow_q[k] <= val;
                end
                initialized_q <= 1;
            end


            // generate random contentions
            if (mem_rand_en_i) begin
                void'(randomize(rnd) with {rnd > 0; rnd <= 100;});
                if(rnd < MemRandHitRate) begin
                    mem_ready_q <= '1;
                end else begin
                    mem_ready_q <= '0;
                end
            end else begin
                mem_ready_q <= '1;
            end

            // generate random invalidations
            if (inv_rand_en_i) begin
                void'(randomize(rnd) with {rnd > 0; rnd <= 100;});
                // only invalidate if there are no replies in flight to the cache. Otherwise, we
                // might send data that has just been invalidated.
                if(rnd < MemRandInvRate && ~infifo_empty) begin
                    mem_inv_q <= '1;
                    void'(randomize(lval) with {lval>=0; lval<(MemWords>>3);});
                    void'(randomize(val));
                    rand_addr_q              <= lval<<3;

                    // with the current TB setup, we cannot invalidate a memory location if a write response to the same address is
                    // in flight, since this could lead to an incosistent state between the real memory and the shadow memory view.
                    // the workaround is not to overwrite shadow memory regions that are still pending in the write buffer
                    // this can be improved.
                    for(int k=0; k<8; k++) begin
                        if(~mem_array_dirty_q[lval][k]) begin
                            mem_array_q       [lval][k*8 +: 8] <= val[k*8 +: 8];
                            mem_array_shadow_q[lval][k*8 +: 8] <= val[k*8 +: 8];
                        end
                    end
                end else begin
                    mem_inv_q <= '0;
                end
            end else begin
                mem_inv_q <= '0;
            end
        end
    end


    // readout process
    always_comb begin : proc_mem
        infifo_push       = 0;
        infifo_data       = '0;
        outfifo_pop       = 0;
        infifo_data.rtype = DCACHE_LOAD_ACK;
        infifo_data.data  = 'x;
        write_en          = '0;

        // TODO: atomic request
        // DCACHE_ATOMIC_REQ
        // DCACHE_ATOMIC_ACK

        // TODO: stores
        // DCACHE_STORE_REQ
        // DCACHE_STORE_ACK

        // TODO: interrupts
        // DCACHE_INT_REQ
        // DCACHE_INT_ACK

        // generate random invalidation
        if (mem_inv_q) begin

            infifo_data.rtype = DCACHE_INV_REQ;

            // since we do not keep a mirror tag table here,
            // we allways invalidate all ways of the aliased index.
            // this is not entirely correct and will produce
            // too many invalidations
            infifo_data.inv.idx = rand_addr_q[DCACHE_INDEX_WIDTH-1:0];
            infifo_data.inv.all = '1;
            infifo_push         = 1'b1;

        end else if ((~outfifo_empty) && (~infifo_full) && mem_ready_q) begin

            outfifo_pop     = 1'b1;
            infifo_push     = 1'b1;

            unique case (outfifo_data.rtype)
                DCACHE_LOAD_REQ: begin
                    infifo_data.tid = outfifo_data.tid;
                    infifo_data.data = 'x;
                    unique case(outfifo_data.size)
                        3'b000: for(int k=0;k<64;k+=8)  infifo_data.data[outfifo_data.paddr[2:0]*8 +: 8] = mem_array_q[outfifo_data.paddr>>3][outfifo_data.paddr[2:0]*8 +: 8];
                        3'b001: for(int k=0;k<64;k+=16) infifo_data.data[outfifo_data.paddr[2:1]*16+:16] = mem_array_q[outfifo_data.paddr>>3][outfifo_data.paddr[2:1]*16+:16];
                        3'b010: for(int k=0;k<64;k+=32) infifo_data.data[outfifo_data.paddr[2]  *32+:32] = mem_array_q[outfifo_data.paddr>>3][outfifo_data.paddr[2]  *32+:32];
                        3'b011:                                                  infifo_data.data[0+:64] = mem_array_q[outfifo_data.paddr>>3];
                        3'b111: for(int k=0; k<DCACHE_LINE_WIDTH/64; k++) infifo_data.data[k*64 +:64]    = mem_array_q[(outfifo_data.paddr>>3) + k];
                        default: $fatal(1,"unsupported transfer size for read");
                    endcase // infifo_data.size
                end
                DCACHE_STORE_REQ:  begin
                    infifo_data.tid   = outfifo_data.tid;
                    infifo_data.rtype = DCACHE_STORE_ACK;
                    write_en          = 1'b1;
                end
                // DCACHE_ATOMIC_REQ: $fatal(1, "DCACHE_ATOMIC_REQ not implemented yet");
                // DCACHE_INT_REQ:    $fatal(1, "DCACHE_INT_REQ not implemented yet");
                default: begin
                    // $fatal(1, "unsupported request type");
                end
            endcase // outfifo_data.rtype
        end
    end

  fifo_v3 #(
    .dtype(dcache_req_t),
    .DEPTH(2)
  ) i_outfifo (
    .clk_i       ( clk_i         ),
    .rst_ni      ( rst_ni        ),
    .flush_i     ( 1'b0          ),
    .testmode_i  ( 1'b0          ),
    .full_o      ( outfifo_full  ),
    .empty_o     ( outfifo_empty ),
    .usage_o     (               ),
    .data_i      ( mem_data_i    ),
    .push_i      ( outfifo_push  ),
    .data_o      ( outfifo_data  ),
    .pop_i       ( outfifo_pop   )
  );

  assign outfifo_push   = mem_data_req_i & (~outfifo_full);
  assign mem_data_ack_o = outfifo_push;

  fifo_v3 #(
    .dtype(dcache_rtrn_t),
    .DEPTH(2)
  ) i_infifo (
    .clk_i       ( clk_i         ),
    .rst_ni      ( rst_ni        ),
    .flush_i     ( 1'b0          ),
    .testmode_i  ( 1'b0          ),
    .full_o      ( infifo_full   ),
    .empty_o     ( infifo_empty  ),
    .usage_o     (               ),
    .data_i      ( infifo_data   ),
    .push_i      ( infifo_push   ),
    .data_o      ( mem_rtrn_o    ),
    .pop_i       ( infifo_pop    )
  );

  assign infifo_pop     = ~infifo_empty;
  assign mem_rtrn_vld_o = infifo_pop;


///////////////////////////////////////////////////////
// checker process
///////////////////////////////////////////////////////

    initial begin
        bit ok;
        progress status;
        status = new(MemName);

        `ACQ_WAIT_CYC(clk_i,10)
        `ACQ_WAIT_SIG(clk_i,~rst_ni)

        while(~seq_last_i) begin
            `ACQ_WAIT_SIG(clk_i,check_en_i)
            status.reset(MemWords);
            // crosscheck whether shadow and real memory arrays still match
            for(int k=0; k<MemWords; k++) begin
                ok = (mem_array_q[k] == mem_array_shadow_q[k]) && !(|mem_array_dirty_q[k]);
                if(!ok) begin
                    $display("%s> dirty bytes at k=%016X: real[k>>3]=%016X, shadow[k>>3]=%016X, dirty[k>>3]=%02X",
                        MemName, k<<3, mem_array_q[k], mem_array_shadow_q[k], mem_array_dirty_q[k]);
                end
                status.addRes(!ok);
                status.print();
            end
        end
        status.printToFile({MemName, "_summary.rep"}, 1);

        if(status.totErrCnt == 0) begin
            $display("%s> ----------------------------------------------------------------------", MemName);
            $display("%s> PASSED %0d VECTORS", MemName, status.totAcqCnt);
            $display("%s> ----------------------------------------------------------------------\n", MemName);
        end else begin
            $display("%s> ----------------------------------------------------------------------\n", MemName);
            $display("%s> FAILED %0d OF %0d VECTORS\n", MemName , status.totErrCnt, status.totAcqCnt);
            $display("%s> ----------------------------------------------------------------------\n", MemName);
        end
    end




///////////////////////////////////////////////////////
// assertions
///////////////////////////////////////////////////////

//pragma translate_off
`ifndef verilator

    nc_region: assert property (
        @(posedge clk_i) disable iff (~rst_ni) mem_data_req_i |-> mem_data_i.paddr >= CachedAddrEnd || mem_data_i.paddr < CachedAddrBeg |-> mem_data_i.nc)
        else $fatal(1, "cached access into noncached region");

    cached_reads: assert property (
        @(posedge clk_i) disable iff (~rst_ni) mem_data_req_i |-> mem_data_i.rtype==DCACHE_LOAD_REQ |-> ~mem_data_i.nc |-> mem_data_i.size == 3'b111)
        else $fatal(1, "cached read accesses always have to be one CL wide");

    nc_reads: assert property (
        @(posedge clk_i) disable iff (~rst_ni) mem_data_req_i |-> mem_data_i.rtype==DCACHE_LOAD_REQ |-> mem_data_i.nc |-> mem_data_i.size inside {3'b000, 3'b001, 3'b010, 3'b011})
        else $fatal(1, "nc read size can only be one of the following: byte, halfword, word, dword");

    write_size: assert property (
        @(posedge clk_i) disable iff (~rst_ni) mem_data_req_i |-> mem_data_i.rtype==DCACHE_STORE_REQ |-> mem_data_i.size inside {3'b000, 3'b001, 3'b010, 3'b011})
        else $fatal(1, "write size can only be one of the following: byte, halfword, word, dword");

    addr_range: assert property (
        @(posedge clk_i) disable iff (~rst_ni) mem_data_req_i |-> mem_data_i.rtype inside {DCACHE_STORE_REQ, DCACHE_STORE_REQ} |-> mem_data_i.paddr < (MemWords<<3))
        else $fatal(1, "address is out of bounds");

`endif
//pragma translate_on

endmodule // mem_emul

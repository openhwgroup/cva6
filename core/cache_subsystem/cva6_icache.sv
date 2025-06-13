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
// Description: Instruction cache that is compatible with openpiton.
//
// Some notes:
//
// 1) refills always have the size of one cache line, except for accesses to the I/O region, which is mapped
//    to the top half of the physical address space (bit 39 = 1). the data width of the interface has the width
//    of one cache line, and hence the ifills can be transferred in a single cycle. note that the ifills must be
//    consumed unconditionally.
//
// 2) instruction fetches are always assumed to be aligned to 32bit (lower 2 bits are ignored)
//
// 3) NC accesses to I/O space are expected to return 32bit from memory.
//
// Additional contributions by:
// 06.06.2024 - Yannick Casamatta, Thales
//              OBI Protocol

module cva6_icache
  import ariane_pkg::*;
  import wt_cache_pkg::*;
#(
    parameter config_pkg::cva6_cfg_t CVA6Cfg = config_pkg::cva6_cfg_empty,
    parameter type ypb_fetch_req_t = logic,
    parameter type ypb_fetch_rsp_t = logic,
    parameter type icache_req_t = logic,
    parameter type icache_rtrn_t = logic,
    /// ID to be used for read transactions
    parameter logic [CVA6Cfg.MEM_TID_WIDTH-1:0] RdTxId = 0
) (
    input logic clk_i,
    input logic rst_ni,

    /// flush the icache, flush and kill have to be asserted together
    input  logic flush_i,
    /// enable icache
    input  logic en_i,
    /// to performance counter
    output logic miss_o,

    // Fetch Request channel - FRONTEND
    input  ypb_fetch_req_t ypb_fetch_req_i,
    // Fetch Response channel - FRONTEND
    output ypb_fetch_rsp_t ypb_fetch_rsp_o,

    // refill port
    input  logic         mem_rtrn_vld_i,
    input  icache_rtrn_t mem_rtrn_i,
    output logic         mem_data_req_o,
    input  logic         mem_data_ack_i,
    output icache_req_t  mem_data_o
);

  localparam ICACHE_OFFSET_WIDTH = $clog2(CVA6Cfg.ICACHE_LINE_WIDTH / 8);
  localparam ICACHE_NUM_WORDS = 2 ** (CVA6Cfg.ICACHE_INDEX_WIDTH - ICACHE_OFFSET_WIDTH);
  localparam ICACHE_CL_IDX_WIDTH = $clog2(ICACHE_NUM_WORDS);  // excluding byte offset

  // functions
  function automatic logic [CVA6Cfg.ICACHE_SET_ASSOC-1:0] icache_way_bin2oh(
      input logic [CVA6Cfg.ICACHE_SET_ASSOC_WIDTH-1:0] in);
    logic [CVA6Cfg.ICACHE_SET_ASSOC-1:0] out;
    out     = '0;
    out[in] = 1'b1;
    return out;
  endfunction

  // signals
  logic cache_en_d, cache_en_q;  // cache is enabled
  logic [CVA6Cfg.VLEN-1:0] vaddr_d, vaddr_q;
  logic paddr_is_nc_q, paddr_is_nc_d;  // asserted if physical address is non-cacheable
  logic [CVA6Cfg.ICACHE_SET_ASSOC-1:0] cl_hit, cl_hit2;  // hit from tag compare

  logic cache_rden;  // triggers cache lookup
  logic cache_wren;  // triggers write to cacheline
  logic
      cmp_en_d,
      cmp_en_q;  // enable tag comparison in next cycle. used to cut long path due to NC signal.
  logic flush_d, flush_q;  // used to register and signal pending flushes

  // replacement strategy
  logic                                      update_lfsr;  // shift the LFSR
  logic [CVA6Cfg.ICACHE_SET_ASSOC_WIDTH-1:0] inv_way;  // first non-valid encountered
  logic [CVA6Cfg.ICACHE_SET_ASSOC_WIDTH-1:0] rnd_way;  // random index for replacement
  logic [CVA6Cfg.ICACHE_SET_ASSOC_WIDTH-1:0] repl_way;  // way to replace
  logic [CVA6Cfg.ICACHE_SET_ASSOC-1:0] repl_way_oh_d, repl_way_oh_q;  // way to replace (onehot)
  logic all_ways_valid;  // we need to switch repl strategy since all are valid

  // invalidations / flushing
  logic inv_en;  // incoming invalidations
  logic inv_d, inv_q;  // invalidation in progress
  logic flush_en, flush_done;  // used to flush cache entries
  logic [ICACHE_CL_IDX_WIDTH-1:0] flush_cnt_d, flush_cnt_q;  // used to flush cache entries

  // mem arrays
  logic                                cl_we;  // write enable to memory array
  logic [CVA6Cfg.ICACHE_SET_ASSOC-1:0] cl_req;  // request to memory array
  logic [     ICACHE_CL_IDX_WIDTH-1:0] cl_index;  // this is a cache-line index, to memory array
  logic [ICACHE_OFFSET_WIDTH-1:0] cl_offset_d, cl_offset_q;  // offset in cache line
  logic [CVA6Cfg.ICACHE_TAG_WIDTH-1:0] cl_tag_d, cl_tag_q;  // this is the cache tag
  logic [CVA6Cfg.ICACHE_TAG_WIDTH-1:0]          cl_tag_rdata [CVA6Cfg.ICACHE_SET_ASSOC-1:0]; // these are the tags coming from the tagmem
  logic [CVA6Cfg.ICACHE_LINE_WIDTH-1:0]         cl_rdata     [CVA6Cfg.ICACHE_SET_ASSOC-1:0]; // these are the cachelines coming from the cache
  logic [CVA6Cfg.ICACHE_USER_LINE_WIDTH-1:0]    cl_ruser[CVA6Cfg.ICACHE_SET_ASSOC-1:0]; // these are the cachelines coming from the user cache
  logic [CVA6Cfg.ICACHE_SET_ASSOC-1:0][CVA6Cfg.FETCH_WIDTH-1:0] cl_sel;  // selected word from each cacheline
  logic [CVA6Cfg.ICACHE_SET_ASSOC-1:0][CVA6Cfg.FETCH_USER_WIDTH-1:0] cl_user;  // selected word from each cacheline
  logic [CVA6Cfg.ICACHE_SET_ASSOC-1:0] vld_req;  // bit enable for valid regs
  logic vld_we;  // valid bits write enable
  logic [CVA6Cfg.ICACHE_SET_ASSOC-1:0] vld_wdata;  // valid bits to write
  logic [CVA6Cfg.ICACHE_SET_ASSOC-1:0] vld_rdata;  // valid bits coming from valid regs
  logic [ICACHE_CL_IDX_WIDTH-1:0] vld_addr;  // valid bit

  // cpmtroller FSM
  typedef enum logic [2:0] {
    FLUSH,
    IDLE,
    READ,
    READ_BIS,
    MISS,
    KILL_MISS
  } state_e;
  state_e state_d, state_q;

  logic ypb_valid, ypb_grant;

  logic [CVA6Cfg.FETCH_WIDTH-1:0] data_d, data_q, ypb_rdata;
  logic [CVA6Cfg.FETCH_USER_WIDTH-1:0] userdata_d, userdata_q, ypb_ruser;
  logic data_valid_ypb, data_valid_ypb_d, data_valid_ypb_q;

  //YPB
  assign ypb_fetch_rsp_o.pgnt = ypb_grant;
  assign ypb_fetch_rsp_o.rvalid = ypb_valid;
  assign ypb_fetch_rsp_o.rid = '0;
  assign ypb_fetch_rsp_o.err = '0;
  assign ypb_fetch_rsp_o.rdata = ypb_rdata;
  assign ypb_fetch_rsp_o.ruser = ypb_ruser;


  ///////////////////////////////////////////////////////
  // address -> cl_index mapping, interface plumbing
  ///////////////////////////////////////////////////////

  // extract tag from physical address, check if NC
  assign cl_tag_d  = (ypb_fetch_req_i.req && ypb_grant) ? ypb_fetch_req_i.a.addr[CVA6Cfg.ICACHE_TAG_WIDTH+CVA6Cfg.ICACHE_INDEX_WIDTH-1:CVA6Cfg.ICACHE_INDEX_WIDTH] : cl_tag_q;
  // memtype[1] = 1 is cacheable, memtype[1] = 0 is non cacheable
  assign paddr_is_nc_d  = !cache_en_q || ((ypb_fetch_req_i.req && ypb_grant) ? ypb_fetch_req_i.cacheable : paddr_is_nc_q);

  // latch this in case we have to stall later on
  // make sure this is 32bit aligned
  assign vaddr_d = (ypb_fetch_rsp_o.vgnt & ypb_fetch_req_i.vreq) ? ypb_fetch_req_i.vaddr : vaddr_q;

  // split virtual address into index and offset to address cache arrays
  assign cl_index = vaddr_d[CVA6Cfg.ICACHE_INDEX_WIDTH-1:ICACHE_OFFSET_WIDTH];


  if (CVA6Cfg.NOCType == config_pkg::NOC_TYPE_AXI4_ATOP) begin : gen_axi_offset
    // if we generate a noncacheable access, the word will be at offset 0 or 4 in the cl coming from memory
    assign cl_offset_d = ( ypb_fetch_rsp_o.vgnt & ypb_fetch_req_i.vreq)      ? (ypb_fetch_req_i.vaddr >> CVA6Cfg.FETCH_ALIGN_BITS) << CVA6Cfg.FETCH_ALIGN_BITS :
                         ( paddr_is_nc_d  & mem_data_req_o ) ? {{ICACHE_OFFSET_WIDTH-1{1'b0}}, cl_offset_q[2]}<<2 : // needed since we transfer 32bit over a 64bit AXI bus in this case
        cl_offset_q;
    // request word address instead of cl address in case of NC access
    assign mem_data_o.paddr = (paddr_is_nc_d) ? {cl_tag_d, vaddr_q[CVA6Cfg.ICACHE_INDEX_WIDTH-1:3], 3'b0} :                                         // align to 64bit
        {cl_tag_d, vaddr_q[CVA6Cfg.ICACHE_INDEX_WIDTH-1:ICACHE_OFFSET_WIDTH], {ICACHE_OFFSET_WIDTH{1'b0}}}; // align to cl
  end else begin : gen_piton_offset
    // icache fills are either cachelines or 4byte fills, depending on whether they go to the Piton I/O space or not.
    // since the piton cache system replicates the data, we can always index the full CL
    assign cl_offset_d = (ypb_fetch_rsp_o.vgnt & ypb_fetch_req_i.vreq) ? {ypb_fetch_req_i.vaddr >> 2, 2'b0} : cl_offset_q;

    // request word address instead of cl address in case of NC access
    assign mem_data_o.paddr = (paddr_is_nc_d) ? {cl_tag_d, vaddr_q[CVA6Cfg.ICACHE_INDEX_WIDTH-1:2], 2'b0} :                                         // align to 32bit
        {cl_tag_d, vaddr_q[CVA6Cfg.ICACHE_INDEX_WIDTH-1:ICACHE_OFFSET_WIDTH], {ICACHE_OFFSET_WIDTH{1'b0}}}; // align to cl
  end


  assign mem_data_o.tid = RdTxId;

  assign mem_data_o.nc  = paddr_is_nc_d;
  // way that is being replaced
  assign mem_data_o.way = repl_way;

  // invalidations take two cycles
  assign inv_d          = inv_en;


  typedef enum logic [1:0] {
    YPB_R_IDLE,
    YPB_R_WAIT,
    YPB_R_VALID,
    YPB_R_KILLED
  } ypb_r_state_e;
  ypb_r_state_e ypb_r_state_d, ypb_r_state_q;


  // Common clocked process
  always_ff @(posedge clk_i or negedge rst_ni) begin : p_ypb
    if (!rst_ni) begin
      ypb_r_state_q <= YPB_R_IDLE;
      data_q <= '0;
      userdata_q <= '0;
      data_valid_ypb_q <= '0;
    end else begin
      ypb_r_state_q <= ypb_r_state_d;
      data_q <= data_d;
      userdata_q <= userdata_d;
      data_valid_ypb_q <= data_valid_ypb_d;
    end
  end

  // YPB CHANNEL R protocol FSM (combi)

  always_comb begin : p_fsm_ypb_r
    // default assignment
    ypb_valid = '0;
    //fetch_rsp_o.invalid_data = '0;
    ypb_rdata = data_q;
    ypb_ruser = userdata_q;
    ypb_r_state_d = ypb_r_state_q;

    unique case (ypb_r_state_q)
      YPB_R_IDLE: begin
        if (ypb_fetch_req_i.preq && ypb_grant) begin
          if (!(ypb_fetch_req_i.kill_req || flush_d)) begin
            ypb_r_state_d = YPB_R_WAIT;
          end else begin
            ypb_r_state_d = YPB_R_KILLED;
          end
        end
      end

      YPB_R_WAIT: begin
        if (ypb_fetch_req_i.kill_req || flush_d) begin
          ypb_valid = '1;
          //fetch_rsp_o.invalid_data = '1;
          ypb_r_state_d = YPB_R_IDLE;
        end else if (data_valid_ypb || data_valid_ypb_q) begin
          ypb_valid = '1;
          if (data_valid_ypb) begin
            ypb_rdata = data_d;
            ypb_ruser = userdata_d;
          end
          ypb_ruser = userdata_d;
          if (!(ypb_fetch_req_i.preq && ypb_grant)) begin
            ypb_r_state_d = YPB_R_IDLE;
          end
        end
      end

      YPB_R_KILLED: begin
        ypb_valid = '1;
        //fetch_rsp_o.invalid_data = '1;
        if (ypb_fetch_req_i.preq && ypb_grant) begin
          if (!(ypb_fetch_req_i.kill_req || flush_d)) begin
            ypb_r_state_d = YPB_R_WAIT;
          end
        end else begin
          ypb_r_state_d = YPB_R_IDLE;
        end
      end

      default: begin
        // we should never get here
        ypb_r_state_d = YPB_R_IDLE;
      end
    endcase
  end


  ///////////////////////////////////////////////////////
  // main control logic
  ///////////////////////////////////////////////////////

  always_comb begin : p_fsm
    // default assignment
    state_d = state_q;
    cache_en_d   = cache_en_q & en_i;// disabling the cache is always possible, enable needs to go via flush
    flush_en = 1'b0;
    cmp_en_d = 1'b0;
    cache_rden = 1'b0;
    cache_wren = 1'b0;
    inv_en = 1'b0;
    flush_d = flush_q | flush_i;  // register incoming flush
    // interfaces
    ypb_fetch_rsp_o.vgnt = 1'b0;
    mem_data_req_o = 1'b0;
    // performance counter
    miss_o = 1'b0;
    ypb_grant = 1'b0;
    data_valid_ypb = '0;
    data_valid_ypb_d = '0;

    // handle invalidations unconditionally
    // note: invald are mutually exclusive with
    // ifills, since both arrive over the same IF
    // however, we need to make sure below that we
    // do not trigger a cache readout at the same time...
    if (mem_rtrn_vld_i && mem_rtrn_i.rtype == ICACHE_INV_REQ) begin
      inv_en = 1'b1;
    end

    unique case (state_q)
      //////////////////////////////////
      // this clears all valid bits
      FLUSH: begin
        flush_en = 1'b1;
        if (flush_done) begin
          state_d = IDLE;
          flush_d = 1'b0;
          // if the cache was not enabled set this
          cache_en_d = en_i;
        end
      end
      //////////////////////////////////
      // wait for an incoming request
      IDLE: begin
        // only enable tag comparison if cache is enabled
        cmp_en_d = cache_en_q;

        // handle pending flushes, or perform cache clear upon enable
        if (flush_d || (en_i && !cache_en_q)) begin
          state_d = FLUSH;
          // wait for incoming requests
        end else begin
          // mem requests are for sure invals here
          if (!mem_rtrn_vld_i) begin
            ypb_fetch_rsp_o.vgnt = 1'b1;
            // we have a new request not killed
            if (ypb_fetch_req_i.preq && !ypb_fetch_req_i.kill_req) begin
              cache_rden = 1'b1;
              state_d = READ_BIS;
              ypb_grant = 1'b1;
            end else if (ypb_fetch_req_i.vreq && !ypb_fetch_req_i.kill_req) begin
              cache_rden = 1'b1;
              state_d = READ;
            end
          end
        end
      end
      //////////////////////////////////
      // check whether we have a hit
      // in case the cache is disabled,
      // or in case the address is NC, we
      // reuse the miss mechanism to handle
      // the request
      READ: begin
        // only enable tag comparison if cache is enabled
        cmp_en_d   = cache_en_q;
        // readout speculatively
        cache_rden = cache_en_q;

        if (ypb_fetch_req_i.preq) begin
          state_d   = READ_BIS;
          ypb_grant = 1'b1;

          // check if we have to flush
          if (flush_d) begin
            state_d = IDLE;
            // we have an exception
          end else if (ypb_fetch_req_i.kill_req) begin
            state_d = IDLE;
            if (!mem_rtrn_vld_i) begin
              ypb_fetch_rsp_o.vgnt = 1'b1;
              if (ypb_fetch_req_i.vreq) begin
                state_d = READ;
              end
            end
            // we have a hit 
          end else if (|cl_hit && cache_en_q && !inv_q) begin
            data_valid_ypb_d = '1;
            state_d = IDLE;
            if (!mem_rtrn_vld_i) begin
              ypb_fetch_rsp_o.vgnt = 1'b1;
              if (ypb_fetch_req_i.vreq) begin
                state_d = READ;
              end
            end
          end else if (!inv_q) begin
            cmp_en_d = 1'b0;
            // only count this as a miss if the cache is enabled, and
            // the address is cacheable
            // send out ifill request
            mem_data_req_o = 1'b1;
            if (mem_data_ack_i) begin
              miss_o  = ~paddr_is_nc_d;
              state_d = MISS;
            end
          end
          // bail out if this request is being killed (and we missed on the TLB)
        end else if (flush_d) begin
          state_d = IDLE;
        end else if (ypb_fetch_req_i.kill_req) begin
          state_d = IDLE;
          // we can accept another request
          // and stay here, but only if no inval is coming in
          // note: we are not expecting ifill return packets here...
          if (!mem_rtrn_vld_i) begin
            ypb_fetch_rsp_o.vgnt = 1'b1;
            if (ypb_fetch_req_i.vreq) begin
              state_d = READ;
            end
          end
        end else if (ypb_fetch_req_i.vreq) begin
          //abort previous index and launch new one
          state_d = IDLE;
          if (!mem_rtrn_vld_i) begin
            cache_rden = 1'b1;
            ypb_fetch_rsp_o.vgnt = 1'b1;
            state_d = READ;
          end
        end
      end

      READ_BIS: begin
        // only enable tag comparison if cache is enabled
        cmp_en_d   = cache_en_q;
        // readout speculatively
        cache_rden = cache_en_q;

        // check if we have to flush
        if (flush_d) begin
          state_d = IDLE;
        end else if (ypb_fetch_req_i.kill_req) begin
          state_d = IDLE;
          if (!mem_rtrn_vld_i) begin
            ypb_fetch_rsp_o.vgnt = 1'b1;
            if (ypb_fetch_req_i.vreq) begin
              state_d = READ;
            end
          end

          // we have a hit
        end else if ((|cl_hit2 && cache_en_q && !inv_q)) begin
          state_d = IDLE;
          data_valid_ypb = 1'b1;
          // we can accept another request
          // and stay here, but only if no inval is coming in
          // note: we are not expecting ifill return packets here...
          if (!mem_rtrn_vld_i) begin
            ypb_fetch_rsp_o.vgnt = 1'b1;
            if (ypb_fetch_req_i.vreq) begin
              state_d = READ;
            end
          end

        end else if (!inv_q) begin
          cmp_en_d = 1'b0;
          // only count this as a miss if the cache is enabled, and
          // the address is cacheable
          // send out ifill request
          mem_data_req_o = 1'b1;
          if (mem_data_ack_i) begin
            miss_o  = ~paddr_is_nc_d;
            state_d = MISS;
          end
        end
      end

      //////////////////////////////////
      // wait until the memory transaction
      // returns. do not write to memory
      // if the nc bit is set.
      MISS: begin
        // note: this is mutually exclusive with ICACHE_INV_REQ,
        // so we do not have to check for invals here
        if (mem_rtrn_vld_i && mem_rtrn_i.rtype == ICACHE_IFILL_ACK) begin
          state_d = IDLE;
          // only return data if request is not being killed
          if (!(ypb_fetch_req_i.kill_req || flush_d)) begin
            // only write to cache if this address is cacheable
            cache_wren = ~paddr_is_nc_d;
            data_valid_ypb = '1;
          end
          // bail out if this request is being killed
        end else if (ypb_fetch_req_i.kill_req || flush_d) begin
          state_d = KILL_MISS;
        end
      end
      //////////////////////////////////
      // killed miss,
      // wait until memory responds and
      // go back to idle
      KILL_MISS: begin
        if (mem_rtrn_vld_i && mem_rtrn_i.rtype == ICACHE_IFILL_ACK) begin
          state_d = IDLE;
        end
      end

      default: begin
        // we should never get here
        state_d = FLUSH;
      end
    endcase  // state_q
  end

  ///////////////////////////////////////////////////////
  // valid bit invalidation and replacement strategy
  ///////////////////////////////////////////////////////

  // note: it cannot happen that we get an invalidation + a cl replacement
  // in the same cycle as these requests arrive via the same interface
  // flushes take precedence over invalidations (it is ok if we ignore
  // the inval since the cache is cleared anyway)

  assign flush_cnt_d = (flush_done) ? '0 : (flush_en) ? flush_cnt_q + 1 : flush_cnt_q;

  assign flush_done = (flush_cnt_q == (ICACHE_NUM_WORDS - 1));

  // invalidation/clearing address
  // flushing takes precedence over invals
  assign vld_addr = (flush_en)       ? flush_cnt_q        :
                    (inv_en)         ? mem_rtrn_i.inv.idx[CVA6Cfg.ICACHE_INDEX_WIDTH-1:ICACHE_OFFSET_WIDTH] :
                                       cl_index;

  assign vld_req  = (flush_en || cache_rden)        ? '1                                    :
                    (mem_rtrn_i.inv.all && inv_en)  ? '1                                    :
                    (mem_rtrn_i.inv.vld && inv_en)  ? icache_way_bin2oh(
      mem_rtrn_i.inv.way
  ) : repl_way_oh_q;

  assign vld_wdata = (cache_wren) ? '1 : '0;

  assign vld_we = (cache_wren | inv_en | flush_en);
  // assign vld_req   = (vld_we | cache_rden);


  // chose random replacement if all are valid
  assign update_lfsr = cache_wren & all_ways_valid;
  assign repl_way = (all_ways_valid) ? rnd_way : inv_way;
  assign repl_way_oh_d = (cmp_en_q) ? icache_way_bin2oh(repl_way) : repl_way_oh_q;

  // enable signals for memory arrays
  assign cl_req = (cache_rden) ? '1 : (cache_wren) ? repl_way_oh_q : '0;
  assign cl_we = cache_wren;


  // find invalid cache line
  lzc #(
      .WIDTH(CVA6Cfg.ICACHE_SET_ASSOC)
  ) i_lzc (
      .in_i   (~vld_rdata),
      .cnt_o  (inv_way),
      .empty_o(all_ways_valid)
  );

  // generate random cacheline index
  lfsr #(
      .LfsrWidth(8),
      .OutWidth (CVA6Cfg.ICACHE_SET_ASSOC_WIDTH)
  ) i_lfsr (
      .clk_i (clk_i),
      .rst_ni(rst_ni),
      .en_i  (update_lfsr),
      .out_o (rnd_way)
  );


  ///////////////////////////////////////////////////////
  // tag comparison, hit generation
  ///////////////////////////////////////////////////////

  logic [CVA6Cfg.ICACHE_SET_ASSOC_WIDTH-1:0] hit_idx;

  for (genvar i = 0; i < CVA6Cfg.ICACHE_SET_ASSOC; i++) begin : gen_tag_cmpsel
    assign cl_hit[i]  = (cl_tag_rdata[i] == cl_tag_d) & vld_rdata[i];
    assign cl_hit2[i] = (cl_tag_rdata[i] == cl_tag_q) & vld_rdata[i];
    assign cl_sel[i]  = cl_rdata[i][{cl_offset_q, 3'b0}+:CVA6Cfg.FETCH_WIDTH];
    assign cl_user[i] = cl_ruser[i][{cl_offset_q, 3'b0}+:CVA6Cfg.FETCH_USER_WIDTH];
  end


  lzc #(
      .WIDTH(CVA6Cfg.ICACHE_SET_ASSOC)
  ) i_lzc_hit (
      .in_i   (cl_hit),
      .cnt_o  (hit_idx),
      .empty_o()
  );

  always_comb begin
    if (cmp_en_q) begin
      data_d = cl_sel[hit_idx];
      userdata_d = cl_user[hit_idx];
    end else begin
      data_d = mem_rtrn_i.data[{cl_offset_q, 3'b0}+:CVA6Cfg.FETCH_WIDTH];
      userdata_d = mem_rtrn_i.user[{cl_offset_q, 3'b0}+:CVA6Cfg.FETCH_USER_WIDTH];
    end
  end

  ///////////////////////////////////////////////////////
  // memory arrays and regs
  ///////////////////////////////////////////////////////


  logic [CVA6Cfg.ICACHE_TAG_WIDTH:0] cl_tag_valid_rdata[CVA6Cfg.ICACHE_SET_ASSOC-1:0];

  for (genvar i = 0; i < CVA6Cfg.ICACHE_SET_ASSOC; i++) begin : gen_sram
    // Tag RAM
    sram_cache #(
        // tag + valid bit
        .DATA_WIDTH (CVA6Cfg.ICACHE_TAG_WIDTH + 1),
        .BYTE_ACCESS(0),
        .TECHNO_CUT (CVA6Cfg.TechnoCut),
        .NUM_WORDS  (ICACHE_NUM_WORDS)
    ) tag_sram (
        .clk_i  (clk_i),
        .rst_ni (rst_ni),
        .req_i  (vld_req[i]),
        .we_i   (vld_we),
        .addr_i (vld_addr),
        // we can always use the saved tag here since it takes a
        // couple of cycle until we write to the cache upon a miss
        .wuser_i('0),
        .wdata_i({vld_wdata[i], cl_tag_q}),
        .be_i   ('1),
        .ruser_o(),
        .rdata_o(cl_tag_valid_rdata[i])
    );

    assign cl_tag_rdata[i] = cl_tag_valid_rdata[i][CVA6Cfg.ICACHE_TAG_WIDTH-1:0];
    assign vld_rdata[i]    = cl_tag_valid_rdata[i][CVA6Cfg.ICACHE_TAG_WIDTH];

    // Data RAM
    sram_cache #(
        .USER_WIDTH (CVA6Cfg.ICACHE_USER_LINE_WIDTH),
        .DATA_WIDTH (CVA6Cfg.ICACHE_LINE_WIDTH),
        .USER_EN    (CVA6Cfg.FETCH_USER_EN),
        .BYTE_ACCESS(0),
        .TECHNO_CUT (CVA6Cfg.TechnoCut),
        .NUM_WORDS  (ICACHE_NUM_WORDS)
    ) data_sram (
        .clk_i  (clk_i),
        .rst_ni (rst_ni),
        .req_i  (cl_req[i]),
        .we_i   (cl_we),
        .addr_i (cl_index),
        .wuser_i(mem_rtrn_i.user),
        .wdata_i(mem_rtrn_i.data),
        .be_i   ('1),
        .ruser_o(cl_ruser[i]),
        .rdata_o(cl_rdata[i])
    );
  end


  always_ff @(posedge clk_i or negedge rst_ni) begin : p_regs
    if (!rst_ni) begin
      cl_tag_q      <= '0;
      flush_cnt_q   <= '0;
      vaddr_q       <= '0;
      cmp_en_q      <= '0;
      cache_en_q    <= '0;
      flush_q       <= '0;
      state_q       <= FLUSH;
      cl_offset_q   <= '0;
      repl_way_oh_q <= '0;
      inv_q         <= '0;
      paddr_is_nc_q <= '0;
    end else begin
      cl_tag_q      <= cl_tag_d;
      flush_cnt_q   <= flush_cnt_d;
      vaddr_q       <= vaddr_d;
      cmp_en_q      <= cmp_en_d;
      cache_en_q    <= cache_en_d;
      flush_q       <= flush_d;
      state_q       <= state_d;
      cl_offset_q   <= cl_offset_d;
      repl_way_oh_q <= repl_way_oh_d;
      inv_q         <= inv_d;
      paddr_is_nc_q <= paddr_is_nc_d;
    end
  end

  ///////////////////////////////////////////////////////
  // assertions
  ///////////////////////////////////////////////////////

  //pragma translate_off
`ifndef VERILATOR
  repl_inval0 :
  assert property (
    @(posedge clk_i) disable iff (!rst_ni) cache_wren |-> !(mem_rtrn_i.inv.all | mem_rtrn_i.inv.vld))
  else $fatal(1, "[l1 icache] cannot replace cacheline and invalidate cacheline simultaneously");

  repl_inval1 :
  assert property (
    @(posedge clk_i) disable iff (!rst_ni) (mem_rtrn_i.inv.all | mem_rtrn_i.inv.vld) |-> !cache_wren)
  else $fatal(1, "[l1 icache] cannot replace cacheline and invalidate cacheline simultaneously");

  invalid_state :
  assert property (
    @(posedge clk_i) disable iff (!rst_ni) (state_q inside {FLUSH, IDLE, READ, READ_BIS, MISS, KILL_MISS}))
  else $fatal(1, "[l1 icache] fsm reached an invalid state");

  hot1 :
  assert property (
    @(posedge clk_i) disable iff (!rst_ni) (!inv_en) |-> cache_rden |=> cmp_en_q |-> $onehot0(
      cl_hit
  ))
  else $fatal(1, "[l1 icache] cl_hit signal must be hot1");

  // this is only used for verification!
  logic vld_mirror[ICACHE_NUM_WORDS-1:0][CVA6Cfg.ICACHE_SET_ASSOC-1:0];
  logic [CVA6Cfg.ICACHE_TAG_WIDTH-1:0] tag_mirror[ICACHE_NUM_WORDS-1:0][CVA6Cfg.ICACHE_SET_ASSOC-1:0];
  logic [CVA6Cfg.ICACHE_SET_ASSOC-1:0] tag_write_duplicate_test;

  always_ff @(posedge clk_i or negedge rst_ni) begin : p_mirror
    if (!rst_ni) begin
      vld_mirror <= '{default: '0};
      tag_mirror <= '{default: '0};
    end else begin
      for (int i = 0; i < CVA6Cfg.ICACHE_SET_ASSOC; i++) begin
        if (vld_req[i] & vld_we) begin
          vld_mirror[vld_addr][i] <= vld_wdata[i];
          tag_mirror[vld_addr][i] <= cl_tag_q;
        end
      end
    end
  end

  for (genvar i = 0; i < CVA6Cfg.ICACHE_SET_ASSOC; i++) begin : gen_tag_dupl
    assign tag_write_duplicate_test[i] = (tag_mirror[vld_addr][i] == cl_tag_q) & vld_mirror[vld_addr][i] & (|vld_wdata);
  end

  tag_write_duplicate :
  assert property (
    @(posedge clk_i) disable iff (!rst_ni) |vld_req |-> vld_we |-> !(|tag_write_duplicate_test))
  else $fatal(1, "[l1 icache] cannot allocate a CL that is already present in the cache");


  initial begin
    // assert wrong parameterizations
    assert (CVA6Cfg.ICACHE_INDEX_WIDTH <= 12)
    else $fatal(1, "[l1 icache] cache index width can be maximum 12bit since VM uses 4kB pages");
  end
`endif
  //pragma translate_on

endmodule  // cva6_icache

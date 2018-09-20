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
// Date: 13.09.2018
// Description: coalescing write buffer for serpent dcache
// 
// A couple of notes:
//
// 1) the write buffer behaves as a fully-associative cache, and is therefore coalescing.
//    this cache is used by the cache readout logic to forward data to the load unit.
//
//    each byte can be in 3 states (valid/dirty):
//
//    0/x:   invalid -> free entry in the buffer that can be written
//    1/1: written and not part of TX in-flight
//    1/0:    Byte is part of a TX in-flight
//    
//    this state is used to distinguish between bytes that have been written and not 
//    yet sent to the memory subsystem, and bytes that are part of a transaction.
// 
// 2) further, each word in the write buffer has a cache states (checked, hit_oh)
//
//    checked == 0: unknown cache state 
//    checked == 1: cache state has been looked up, valid way is stored in "hit_oh"
//
//    cache invalidations/refills affecting a particular word will clear its word state to 0,
//    so another lookup has to be done. note that these lookups are triggered as soon as there is
//    a valid word with checked == 0 in the write buffer.
//  
// 3) returning write ACKs trigger a cache update if the word is present in the cache, and evict that 
//    word from the write buffer. if the word is not allocated to the cache, it is just evicted from the write buffer.
//    if the word cache state is VOID, the pipeline is stalled until it is clear whether that word is in the cache or not.
//
// 4) we handle NC writes using the writebuffer circuitry. the only difference is that the NC write
//    is not acked and popped from the core fifo until the write response returns from memory. this
//    ensures that the data cannot be overwritten by subsequent writes. note that, although the NC word is written
//    into the write buffer and hence visible to the forwarding logic, this particular word will 
//    never be forwarded. the reason is that only addresses allocated in the data cache can be forwarded.

import ariane_pkg::*;
import serpent_cache_pkg::*;

module serpent_dcache_wbuffer #(
    parameter     NUM_WORDS              = 8,
    parameter     MAX_TX                 = 4,              // determines the number of unique TX IDs
    parameter     NC_ADDR_BEGIN          = 40'h8000000000, // start address of noncacheable I/O region
    parameter bit NC_ADDR_GE_LT          = 1'b1            // determines how the physical address is compared with NC_ADDR_BEGIN
)(
    input  logic                               clk_i,          // Clock
    input  logic                               rst_ni,         // Asynchronous reset active low
   
    input  logic                               cache_en_i,     // writes are treated as NC if disabled
    output logic                               empty_o,        // asserted if no data is present in write buffer
     // core request ports
    input  dcache_req_i_t                      req_port_i,  
    output dcache_req_o_t                      req_port_o,  
    // interface to miss handler
    input  logic                               miss_ack_i,      
    output logic                               miss_paddr_o,
    output logic                               miss_req_o,      
    output logic                               miss_we_o,       // always 1 here
    output logic [63:0]                        miss_wdata_o,
    output logic                               miss_vld_bits_o, // unused here (set to 0)
    output logic                               miss_nc_o,       // request to I/O space
    output logic [2:0]                         miss_size_o,     //
    output logic [$clog2(MAX_TX)-1:0]          miss_id_o,       // id of this transaction
    // write responses from memory
    input  logic                               miss_rtrn_i,
    input  logic [$clog2(MAX_TX)-1:0]          miss_rtrn_id_i,  // transaction id to clear   
    // cache read interface 
    output logic [DCACHE_TAG_WIDTH-1:0]        rd_tag_o,        // tag in - comes one cycle later
    output logic [DCACHE_CL_IDX_WIDTH-1:0]     rd_idx_o, 
    output logic [DCACHE_OFFSET_WIDTH-1:0]     rd_off_o, 
    output logic                               rd_req_o,        // read the word at offset off_i[:3] in all ways
    input  logic                               rd_ack_i,        
    input logic  [63:0]                        rd_data_i,       // unused
    input logic  [DCACHE_SET_ASSOC-1:0]        rd_vld_data_i,   // unused
    input logic  [DCACHE_SET_ASSOC-1:0]        rd_hit_oh_i,
    // incoming invalidations
    input logic                                inval_vld_i,
    input logic [DCACHE_CL_IDX_WIDTH-1:0]      inval_cl_idx_i,   
    // cache word write interface
    output logic [DCACHE_SET_ASSOC-1:0]        wr_req_o,
    logic                                      wr_ack_i,
    logic [DCACHE_CL_IDX_WIDTH-1:0]            wr_idx_o,
    logic [DCACHE_OFFSET_WIDTH-1:0]            wr_off_o,
    logic [63:0]                               wr_data_o,
    logic [7:0]                                wr_data_be, 
    // to forwarding logic
    output wbuffer_t  [DCACHE_WBUF_DEPTH-1:0]  wbuffer_data_o
);

// TX status registers are indexed with the transaction ID
// they basically store which bytes from which buffer entry are part
// of that transaction
typedef struct packed { 
    logic                         vld;
    logic [7:0]                   be;
    logic [$clog2(NUM_WORDS)-1:0] ptr;
} tx_stat_t;

tx_stat_t [MAX_TX-1:0]            tx_stat_d, tx_stat_q;
wbuffer_t [NUM_WORDS-1:0]         wbuffer_q, wbuffer_d;
logic     [NUM_WORDS-1:0]         valid;
logic     [NUM_WORDS-1:0]         dirty;
logic     [NUM_WORDS-1:0]         tx;
logic     [NUM_WORDS-1:0]         tocheck;
logic     [NUM_WORDS-1:0]         wbuffer_hit_oh, inval_hit;
logic     [NUM_WORDS-1:0][7:0]    bdirty; 

logic [$clog2(NUM_WORDS)-1:0] next_ptr, dirty_ptr, hit_ptr, wr_ptr, inval_ptr, check_ptr_d, check_ptr_q, rtrn_ptr;
logic [$clog2(MAX_TX)-1:0] tx_cnt_q, tx_cnt_d, tx_id_q, tx_id_d, rtrn_id;

logic [2:0] bdirty_off;
logic [7:0] tx_be;
logic [63:0] wr_paddr, rd_paddr;
logic check_en_d, check_en_q;
logic full, dirty_rd_en, rdy;
logic rtrn_empty, evict;
logic nc_pending_d, nc_pending_q, addr_is_nc;

///////////////////////////////////////////////////////
// misc
///////////////////////////////////////////////////////

generate 
    if (NC_ADDR_GE_LT) begin : g_nc_addr_high
        assign addr_is_nc = (req_port_i.address_tag >= (NC_ADDR_BEGIN>>DCACHE_INDEX_WIDTH)) | ~cache_en_i;
    end
    if (~NC_ADDR_GE_LT) begin : g_nc_addr_low
        assign addr_is_nc = (req_port_i.address_tag < (NC_ADDR_BEGIN>>DCACHE_INDEX_WIDTH))  | ~cache_en_i;
    end
endgenerate  

assign miss_we_o       = 1'b1;
assign miss_vld_bits_o = '0;
assign wbuffer_data_o  = wbuffer_q;

///////////////////////////////////////////////////////
// openpiton does not understand byte enable sigs
// need to convert to the four cases:
// 00: byte
// 01: halfword
// 10: word
// 11: dword
// non-contiguous writes need to be serialized!
///////////////////////////////////////////////////////

// get byte offset
lzc #(
    .WIDTH ( NUM_WORDS )
) i_vld_bdirty (
    .in_i    ( bdirty[dirty_ptr] ),
    .cnt_o   ( bdirty_off        ),
    .empty_o (                   )
);

// add the offset to the physical base address of this buffer entry
assign miss_paddr_o = {wbuffer_q[dirty_ptr].wtag, bdirty_off};
assign miss_id_o    = tx_id_q;
assign miss_req_o   = (|dirty) && (tx_cnt_q < MAX_TX);

always_comb begin : p_be_to_size
    unique case(bdirty[dirty_ptr])
        8'b1111_1111: begin // dword
            miss_size_o = 3'b011;
        end    
        8'b0000_1111, 8'b1111_0000: begin // word
            miss_size_o = 3'b010;
        end    
        8'b1100_0000, 8'b0011_0000, 8'b0000_1100, 8'b0000_0011: begin // hword
            miss_size_o = 3'b001;
        end
        default: begin // individual bytes
            miss_size_o = 3'b000;
        end    
    endcase // dbe_idx     
end

// openpiton requires the data to be replicated in case of smaller sizes than dwords
always_comb begin : p_offset_mux
    miss_wdata_o = '0;
    tx_be     = '0;
    unique case(miss_size_o)
        2'b00: begin // byte
            for(int k=0; k<8; k++) begin    
                miss_wdata_o[k*8 +: 8] = wbuffer_q[dirty_ptr][bdirty_off*8 +: 8];
            end
            tx_be[bdirty_off]      = '1;               
        end        
        2'b01: begin // hword
            for(int k=0; k<4; k++) begin    
                miss_wdata_o[k*16 +: 16] = wbuffer_q[dirty_ptr][bdirty_off*16 +: 16];
            end 
            tx_be[bdirty_off +:2 ]  = '1;               
        end       
        2'b10: begin // word
            for(int k=0; k<2; k++) begin    
                miss_wdata_o[k*32 +: 32] = wbuffer_q[dirty_ptr][bdirty_off*32 +: 32];
            end 
            tx_be[bdirty_off +:4 ]  = '1;   
        end       
        2'b11: begin // dword
            miss_wdata_o = wbuffer_q[dirty_ptr];
            tx_be     = '1;   
        end
     endcase // miss_size_o          
end

///////////////////////////////////////////////////////
// TX status registers and ID counters
///////////////////////////////////////////////////////

// TODO: todo: make this fall through!
fifo_v2 #(
    .FALL_THROUGH ( 1'b0           ), 
    .DATA_WIDTH   ( $clog2(MAX_TX) ), 
    .DEPTH        ( MAX_TX         )        
) i_rtrn_id_fifo (
    .clk_i      ( clk_i            ),
    .rst_ni     ( rst_ni           ),
    .flush_i    ( 1'b0             ),
    .testmode_i ( 1'b0             ),
    .full_o     (                  ),
    .empty_o    ( rtrn_empty       ),
    .alm_full_o (                  ),
    .alm_empty_o(                  ),
    .data_i     ( miss_rtrn_id_i   ),
    .push_i     ( miss_rtrn_i      ),
    .data_o     ( rtrn_id          ),
    .pop_i      ( evict            )
);

always_comb begin : p_tx_stat
    tx_stat_d = tx_stat_q;  
    evict     = 1'b0;
    wr_req_o  = '0;

    // allocate a new entry
    if(dirty_rd_en) begin
        tx_stat_d[tx_id_q].vld = 1'b1;
        tx_stat_d[tx_id_q].ptr = dirty_ptr;
        tx_stat_d[tx_id_q].be  = bdirty[dirty_ptr];
    end 
   
    // clear entry if it is clear whether it can be pushed to the cache or not
    if((~rtrn_empty) && wbuffer_q[rtrn_ptr].checked) begin
        wr_req_o = wbuffer_q[rtrn_ptr].hit_oh;
        if(|wbuffer_q[rtrn_ptr].hit_oh) begin
            if(wr_ack_i) begin
                evict    = 1'b1;
                tx_stat_d[rtrn_id].vld = 1'b0;
            end    
        end else begin
            evict = 1'b1;
            tx_stat_d[rtrn_id].vld = 1'b0;
        end    
    end 

    for(int k=0; k<NUM_WORDS;k++) begin
        // if we write into a word that is currently being transmitted, 
        // we have to clear the corresponding byte enable signals in these transactions
        // this ensures that the byte flags of the dirty bytes are not changed to CLEAN 
        // when the write response comes back from memory
        if(req_port_i.data_req & rdy & (wr_ptr==tx_stat_q[k].ptr) & tx_stat_q[k].vld) begin
            for(int j=0; j<8; j++) begin
                if(req_port_i.data_be[j]) begin
                    tx_stat_d[k].be[j] = 1'b0;
                end
            end
        end
    end
end

assign tx_cnt_d   = (dirty_rd_en & evict) ? tx_cnt_q     :
                    (dirty_rd_en)         ? tx_cnt_q + 1 : 
                    (evict)               ? tx_cnt_q - 1 :
                                            tx_cnt_q;
// wrapping counter
assign tx_id_d    =  (dirty_rd_en)        ? tx_id_q + 1  : 
                                            tx_id_q;

///////////////////////////////////////////////////////
// cache readout & update
///////////////////////////////////////////////////////

// trigger TAG readout in cache
assign rd_paddr   = wbuffer_q[check_ptr_d].wtag<<3;
assign rd_req_o   = |tocheck;
assign rd_tag_o   = rd_paddr[DCACHE_TAG_WIDTH+DCACHE_INDEX_WIDTH-1:DCACHE_INDEX_WIDTH];
assign rd_idx_o   = rd_paddr[DCACHE_INDEX_WIDTH-1:DCACHE_OFFSET_WIDTH];
assign rd_off_o   = rd_paddr[DCACHE_OFFSET_WIDTH-1:0];
assign check_en_d = rd_req_o & rd_ack_i;

// cache update port
assign rtrn_ptr   = tx_stat_q[rtrn_id].ptr;
assign wr_data_be = tx_stat_q[rtrn_id].be;
assign wr_paddr   = wbuffer_q[rtrn_ptr].wtag<<3;
assign wr_idx_o   = wr_paddr[DCACHE_INDEX_WIDTH-1:DCACHE_OFFSET_WIDTH];
assign wr_off_o   = wr_paddr[DCACHE_OFFSET_WIDTH-1:0];
assign wr_data_o  = wbuffer_q[rtrn_ptr].data;


///////////////////////////////////////////////////////
// readout of status bits, index calculation 
///////////////////////////////////////////////////////

generate 
    for(genvar k=0; k<NUM_WORDS-1; k++) begin
        for(genvar j=0; j<8; j++) begin
            assign bdirty[k][j] = wbuffer_q[k].dirty[j] & wbuffer_q[k].valid[j];    
        end
    
        assign dirty[k]          = |bdirty[k];
        assign valid[k]          = |wbuffer_q[k].valid;
        assign wbuffer_hit_oh[k] = valid[k] & (wbuffer_q[k].wtag == {req_port_i.address_tag, req_port_i.address_index[DCACHE_INDEX_WIDTH-1:3]});
        
        // checks if an invalidation/cache refill hits a particular word
        // note: an invalidation can hit multiple words!
        assign inval_hit[k]  = inval_vld_i & valid[k] & (wbuffer_q[k].wtag[DCACHE_INDEX_WIDTH-1:DCACHE_OFFSET_WIDTH-3] == inval_cl_idx_i);
        
        // these word have to be looked up in the cache
        assign tocheck[k]       = (~wbuffer_q[k].checked) & valid[k];
    end    
endgenerate

assign wr_ptr     = (|wbuffer_hit_oh) ? hit_ptr : next_ptr;
assign empty_o    = ~(|valid);
assign rdy        = (|wbuffer_hit_oh) | (~full);


// next free entry in the buffer
lzc #(
    .WIDTH ( NUM_WORDS )
) i_vld_lzc (
    .in_i    ( ~valid        ),
    .cnt_o   ( next_ptr      ),
    .empty_o ( full          )
);

// next free entry in the buffer
lzc #(
    .WIDTH ( NUM_WORDS )
) i_hit_lzc (
    .in_i    ( wbuffer_hit_oh ),
    .cnt_o   ( hit_ptr        ),
    .empty_o (                )
);

// convert invalidation to index
lzc #(
    .WIDTH ( NUM_WORDS )
) i_inval_lzc (
    .in_i    ( inval_hit     ),
    .cnt_o   ( inval_ptr     ),
    .empty_o (               )
);

// next dirty word to serve
rrarbiter #(
    .NUM_REQ ( NUM_WORDS )
) i_dirty_rr (
    .clk_i   ( clk_i         ),
    .rst_ni  ( rst_ni        ),
    .flush_i ( 1'b0          ),
    .en_i    ( dirty_rd_en   ),
    .req_i   ( dirty         ),
    .ack_o   (               ),
    .vld_o   (               ),
    .idx_o   ( dirty_ptr     )
);

// next word to lookup in the cache
rrarbiter #(
    .NUM_REQ ( NUM_WORDS )
) i_clean_rr (
    .clk_i   ( clk_i         ),
    .rst_ni  ( rst_ni        ),
    .flush_i ( 1'b0          ),
    .en_i    ( check_en_d    ),
    .req_i   ( tocheck       ),
    .ack_o   (               ),
    .vld_o   (               ),
    .idx_o   ( check_ptr_d   )
);    


///////////////////////////////////////////////////////
// update logic
///////////////////////////////////////////////////////

// TODO: rewrite and separate into MUXES and write strobe logic
always_comb begin : p_buffer
    wbuffer_d           = wbuffer_q;
    nc_pending_d        = nc_pending_q;
    dirty_rd_en         = 1'b0;
    req_port_o.data_gnt = 1'b0;
    miss_nc_o           = 1'b0;

    // TAG lookup returns, mark corresponding word
    if(check_en_q) begin
        wbuffer_d[check_ptr_q].checked = 1'b1;
        wbuffer_d[check_ptr_q].hit_oh = rd_hit_oh_i;
    end

    // if an invalidation or cache line refill comes in and hits on the write buffer,
    // we have to discard our knowledge of the corresponding cacheline state
    for(int k=0; k<NUM_WORDS; k++) begin
        if(inval_hit[k]) begin
            wbuffer_d[k].checked = 1'b0;
        end 
    end 

    // once TX write response came back and word is written to cache, change to INV
    if(evict) begin
        for(int k=0; k<8; k++) begin
            if(tx_stat_q[rtrn_id].be[k]) begin
                wbuffer_d[rtrn_ptr].dirty[k] = 1'b0;
                wbuffer_d[rtrn_ptr].valid[k] = 1'b0;
            end    
        end
    end

    // mark bytes sent out to the memory system
    if(miss_req_o & miss_ack_i) begin
        dirty_rd_en = 1'b1;
        for(int k=0; k<8; k++) begin
            if(tx_be[k]) begin
                wbuffer_d[dirty_ptr].dirty[k] = 1'b0;
            end    
        end
    end

    // if we are serving an NC write, we block until it is served
    if(nc_pending_q) begin 
        if(empty_o) begin
            nc_pending_d        = 1'b0;
            req_port_o.data_gnt = 1'b1;
            miss_nc_o           = 1'b1; 
        end
    end else begin
        // write new word into the buffer
        if(req_port_i.data_req & rdy) begin
            // in case we have an NC address, need to drain the buffer first
            if(empty_o | ~addr_is_nc) begin 
                // leave in the core fifo if NC
                req_port_o.data_gnt      = ~addr_is_nc;
                nc_pending_d             = addr_is_nc;

                wbuffer_d[wr_ptr].checked = 1'b0;
                
                wbuffer_d[wr_ptr].wtag    = {req_port_i.address_tag, req_port_i.address_index[DCACHE_INDEX_WIDTH-1:3]};
                            
                // mark bytes as dirty
                for(int k=0; k<8; k++) begin
                    if(req_port_i.data_be[k]) begin
                        wbuffer_d[wr_ptr].valid          = 1'b1;
                        wbuffer_d[wr_ptr].dirty[k]       = 1'b1;
                        wbuffer_d[wr_ptr].data[k*8 +: 8] = req_port_i.data_wdata[k*8 +: 8];
                    end
                end
            end    
        end
    end
end


///////////////////////////////////////////////////////
// ff's
///////////////////////////////////////////////////////

always_ff @(posedge clk_i or negedge rst_ni) begin : p_regs
    if(~rst_ni) begin
        wbuffer_q     <= '{default: '0};
        tx_stat_q     <= '{default: '0};  
        nc_pending_q  <= '0;
        tx_cnt_q      <= '0;
        tx_id_q       <= '0;
        check_ptr_q   <= '0;
        check_en_q    <= '0;
    end else begin
        wbuffer_q     <= wbuffer_d;
        tx_stat_q     <= tx_stat_d; 
        tx_cnt_q      <= tx_cnt_d;
        tx_id_q       <= tx_id_d;
        nc_pending_q  <= nc_pending_d;
        check_ptr_q   <= check_ptr_d;
        check_en_q    <= check_en_d;
    end
end

///////////////////////////////////////////////////////
// assertions
///////////////////////////////////////////////////////

//pragma translate_off
`ifndef VERILATOR

    hot1: assert property (
        @(posedge clk_i) disable iff (~rst_ni) req_port_i.data_req |-> $onehot0(wbuffer_hit_oh))     
            else $fatal(1,"[l1 dcache wbuffer] wbuffer_hit_oh signal must be hot1");

    tx_status: assert property (
        @(posedge clk_i) disable iff (~rst_ni) evict & miss_ack_i & miss_req_o |-> (tx_id_q != rtrn_id)) 
            else $fatal(1,"[l1 dcache wbuffer] cannot allocate and clear same tx slot id in the same cycle");

    write_full: assert property (
        @(posedge clk_i) disable iff (~rst_ni) req_port_i.data_req |-> req_port_o.data_gnt |-> ((~full) | (|wbuffer_hit_oh))) 
            else $fatal(1,"[l1 dcache wbuffer] cannot write if full or no hit");

    unused0: assert property (
        @(posedge clk_i) disable iff (~rst_ni) ~req_port_i.tag_valid)
            else $fatal(1,"[l1 dcache wbuffer] req_port_i.tag_valid should not be asserted");

    unused1: assert property (
        @(posedge clk_i) disable iff (~rst_ni) ~req_port_i.kill_req)
            else $fatal(1,"[l1 dcache wbuffer] req_port_i.kill_req should not be asserted");

    unused2: assert property (
        @(posedge clk_i) disable iff (~rst_ni) ~req_port_i.data_we)
            else $fatal(1,"[l1 dcache wbuffer] req_port_i.data_we should not be asserted");

  //  initial begin
  //     // assert wrong parameterizations
  //     assert (DCACHE_INDEX_WIDTH<=12) 
  //       else $fatal(1,"[l1 dcache ctrl] cache index width can be maximum 12bit since VM uses 4kB pages");    
  //  end
`endif
//pragma translate_on

endmodule // serpent_dcache_wbuffer
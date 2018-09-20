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
// Description: Memory arrays, arbiter and tag comparison for serpent dcache.
//
//
// Notes: 1) all ports can trigger a readout of all ways, and the way where the tag hits is selected
//  
//        2) only port0 can write full cache lines. higher ports are read only. also, port0 can only read the tag array,
//           and does not trigger a cache line readout.
//
//        3) the single word write port is a separate port without access to the tag memory.
//           these single word writes can interleave with read operations if they go to different 
//           cacheline offsets, since each word offset is placed into a different SRAM bank.
//
//        4) Access priority is port 0 > port 1 > port 2... > single word write port  

import ariane_pkg::*;
import serpent_cache_pkg::*;

module serpent_dcache_mem #(
        parameter int unsigned NUM_RD_PORTS     = 3
    )(
        input  logic                                              clk_i,
        input  logic                                              rst_ni,
        
        // ports
        input  logic  [NUM_RD_PORTS-1:0][DCACHE_TAG_WIDTH-1:0]    rd_tag_i,           // tag in - comes one cycle later
        input  logic  [NUM_RD_PORTS-1:0][DCACHE_CL_IDX_WIDTH-1:0] rd_idx_i,     
        input  logic  [NUM_RD_PORTS-1:0][DCACHE_OFFSET_WIDTH-1:0] rd_off_i,     
        input  logic  [NUM_RD_PORTS-1:0]                          rd_req_i,           // read the word at offset off_i[:3] in all ways
        output logic  [NUM_RD_PORTS-1:0]                          rd_ack_o,     
        output logic                [DCACHE_SET_ASSOC-1:0]        rd_vld_bits_o,
        output logic                [DCACHE_SET_ASSOC-1:0]        rd_hit_oh_o,
        output logic                [63:0]                        rd_data_o,
        
        // only available on port 0, uses address signals of port 0    
        input  logic                [DCACHE_SET_ASSOC-1:0]        wr_cl_vld_i,        // writes a full cacheline 
        input  logic                [DCACHE_TAG_WIDTH-1:0]        wr_cl_tag_i,
        input  logic                [DCACHE_CL_IDX_WIDTH-1:0]     wr_cl_idx_i,
        input  logic                [DCACHE_OFFSET_WIDTH-1:0]     wr_cl_off_i,
        input  logic                [DCACHE_LINE_WIDTH-1:0]       wr_cl_data_i, 
        input  logic                [DCACHE_LINE_WIDTH/8-1:0]     wr_cl_data_be_i, 
        input  logic                [DCACHE_SET_ASSOC-1:0]        wr_vld_bits_i,      
        input  logic                                              wr_cl_byp_en_i,
        
        // separate port for single word write, no tag access
        input  logic                [DCACHE_SET_ASSOC-1:0]        wr_req_i,           // write a single word to offset off_i[:3] 
        output logic                                              wr_ack_o,
        input  logic                [DCACHE_CL_IDX_WIDTH-1:0]     wr_idx_i,     
        input  logic                [DCACHE_OFFSET_WIDTH-1:0]     wr_off_i,     
        input  logic                [63:0]                        wr_data_i,      
        input  logic                [7:0]                         wr_data_be_i,

        // forwarded wbuffer
        input wbuffer_t             [DCACHE_WBUF_DEPTH-1:0]       wbuffer_data_i
    );


    logic [DCACHE_NUM_BANKS-1:0]                                  bank_req;
    logic [DCACHE_NUM_BANKS-1:0]                                  bank_we;
    logic [DCACHE_NUM_BANKS-1:0][DCACHE_SET_ASSOC-1:0][7:0]       bank_be;
    logic [DCACHE_NUM_BANKS-1:0][DCACHE_CL_IDX_WIDTH-1:0]         bank_idx;
    logic [DCACHE_CL_IDX_WIDTH-1:0]                               bank_idx_d, bank_idx_q;
    logic [DCACHE_OFFSET_WIDTH-1:0]                               bank_off_d, bank_off_q;
     
    logic [DCACHE_NUM_BANKS-1:0][DCACHE_SET_ASSOC-1:0][63:0]      bank_wdata;                   // 
    logic [DCACHE_NUM_BANKS-1:0][DCACHE_SET_ASSOC-1:0][63:0]      bank_rdata;                   // 
    logic [DCACHE_SET_ASSOC-1:0][63:0]                            rdata_cl;                     // selected word from each cacheline
 
    logic [DCACHE_TAG_WIDTH-1:0]                                  tag;
    logic [DCACHE_SET_ASSOC-1:0]                                  vld_req;                      // bit enable for valid regs
    logic                                                         vld_we;                       // valid bits write enable
    logic [DCACHE_SET_ASSOC-1:0]                                  vld_wdata;                    // valid bits to write
    logic [DCACHE_SET_ASSOC-1:0][DCACHE_TAG_WIDTH-1:0]            tag_rdata;                    // these are the tags coming from the tagmem
    logic                       [DCACHE_CL_IDX_WIDTH-1:0]         vld_addr;                     // valid bit 
    
    logic [NUM_RD_PORTS-1:0][$clog2(DCACHE_NUM_BANKS)-1:0]        vld_sel_d, vld_sel_q;
    
    logic [DCACHE_SET_ASSOC-1:0]                                  wr_idx_oh;
    logic [DCACHE_SET_ASSOC-1:0][63:0]                            rdata_sel;

    logic [DCACHE_WBUF_DEPTH-1:0]                                 wbuffer_hit_oh;
    logic [7:0]                                                   wbuffer_be;
    logic [63:0]                                                  wbuffer_rdata, rdata;
    logic [63:0]                                                  wbuffer_cmp_addr;

///////////////////////////////////////////////////////
// arbiter
///////////////////////////////////////////////////////

    // Priority is highest for lowest read port index
    //
    // SRAM bank mapping:
    //
    // Bank 0                   Bank 2  
    // [way0, w0] [way1, w0] .. [way0, w1] [way1, w1] .. 

    // byte enable mapping
    generate 
        for (genvar k=0;k<DCACHE_NUM_BANKS;k++) begin : g_bank
            for (genvar j=0;j<DCACHE_SET_ASSOC;j++) begin : g_bank_way
                assign bank_be[k][j]   = (wr_cl_vld_i[j]) ? wr_cl_data_be_i[k*8 +: 8] : 
                                         (wr_ack_o)       ? wr_data_be_i              : 
                                                            '0;
                
                assign bank_wdata[k][j] = (|wr_cl_vld_i) ?  wr_cl_data_i[k*64 +: 64] :
                                                            wr_data_i;    
            end
        end
    endgenerate

    assign vld_wdata  = wr_vld_bits_i;
    assign vld_addr   = (|wr_cl_vld_i) ? wr_cl_idx_i : rd_idx_i[vld_sel_d];
    assign tag        = (|wr_cl_vld_i) ? wr_cl_tag_i : rd_tag_i[vld_sel_q];// delayed by one cycle
    assign idx        = (|wr_cl_vld_i) ? wr_cl_tag_i : rd_tag_i[vld_sel_q];// delayed by one cycle
    assign bank_off_d = (|wr_cl_vld_i) ? wr_cl_off_i : rd_off_i[vld_sel_d];
          
    assign wr_idx_oh  = dcache_cl_bin2oh(wr_off_i[DCACHE_OFFSET_WIDTH-1:3]);
    
    // priority arbiting for each bank separately
    // full cl writes always block the cache
    // tag readouts / cl readouts may interleave with single word writes in case
    // there is no conflict between the indexes
    always_comb begin : p_prio_arb
        // interface
        wr_ack_o    = 1'b0;
        rd_ack_o    = '0;

        // mem arrays
        bank_req    = '0;
        bank_we     = '0;

        vld_req     = '0;
        vld_we      = 1'b0;

        vld_sel_d   = 0;

        bank_idx    = '{default:wr_cl_idx_i};
        bank_idx_d  = wr_cl_idx_i;

        if(|wr_cl_vld_i) begin
            bank_req    = '1;
            bank_we     = '1;
            vld_req     = wr_cl_vld_i;
            vld_we      = 1'b1;
        end else begin
            // loop over ports
            for (int k=0;k<NUM_RD_PORTS;k++) begin
                if(rd_req_i[k]) begin
                    rd_ack_o[k]    = 1'b1;
                    vld_req        = 1'b1;
                    vld_sel_d      = k;
                    bank_req       = dcache_cl_bin2oh(rd_off_i[k][DCACHE_OFFSET_WIDTH-1:3]);
                    bank_idx       = '{default:rd_idx_i[k]};
                    bank_idx_d     = rd_idx_i[k];
                    break;
                end
            end        

            // check whether we can interleave a single word write
            if(~(|(bank_req & wr_idx_oh))) begin
                if(|wr_req_i) begin
                    wr_ack_o  = 1'b1;
                    bank_req |= wr_idx_oh;
                    bank_we   = wr_idx_oh;    
                    bank_idx[wr_off_i[DCACHE_OFFSET_WIDTH-1:3]] = wr_idx_i;
                end
            end
        end
    end                         

///////////////////////////////////////////////////////
// tag comparison, hit generation
///////////////////////////////////////////////////////

    logic [DCACHE_WBUF_DEPTH-1:0][7:0]  wbuffer_bvalid;
    logic [DCACHE_WBUF_DEPTH-1:0][63:0] wbuffer_data;

    // word tag comparison in write buffer
    assign wbuffer_cmp_addr = (wr_cl_byp_en_i) ? {wr_cl_tag_i, wr_cl_idx_i, wr_cl_off_i} : 
                                                 {tag, bank_idx_q, bank_off_q};

    // tag comparison of way 0                                    
    assign rd_hit_oh_o[0] = (tag == tag_rdata[0]) & rd_vld_bits_o[0];

    // use way 0 to bypass read data in case we missed on the cache or in case the req is NC
    assign rdata_cl[0] = (wr_cl_byp_en_i) ? wr_cl_data_i[wr_cl_off_i[DCACHE_OFFSET_WIDTH-1:3]]  :
                         (rd_hit_oh_o[0]) ? bank_rdata[bank_off_q[DCACHE_OFFSET_WIDTH-1:3]][0] :
                                            '0 ;
    
    generate 
        for (genvar i=1;i<DCACHE_SET_ASSOC;i++) begin : g_tag_cmpsel
            // tag comparison of ways >0
            assign rd_hit_oh_o[i] = (tag == tag_rdata[i]) & rd_vld_bits_o[i];
            // byte offset mux of ways >0
            assign rdata_cl[i] = (rd_hit_oh_o[i] & ~wr_cl_byp_en_i) ? bank_rdata[bank_off_q[DCACHE_OFFSET_WIDTH-1:3]][i] : '0;
        end

        for(genvar k=0; k<DCACHE_WBUF_DEPTH; k++) begin
            for(genvar j=0; j<8; j++) begin
                assign wbuffer_bvalid[k][j] = wbuffer_data_i[k].valid[j];
            end
            assign wbuffer_data[k]   = wbuffer_data_i[k].data;
            assign wbuffer_hit_oh[k] = (|wbuffer_bvalid[k]) & (wbuffer_data_i[k].wtag == (wbuffer_cmp_addr >> 3));
        end    

        // overlay bytes that hit in the write buffer
        for(genvar k=0; k<8; k++) begin
            assign rd_data_o[8*k +: 8] = (wbuffer_be[k]) ? wbuffer_rdata[8*k +: 8] : rdata[8*k +: 8];
        end
    endgenerate

    // OR reduction of writebuffer byte enables
    always_comb begin : p_wbuf_be_red
        for(int j=0; j<8;j++) begin
            wbuffer_be[j]  = (wbuffer_hit_oh[0]) ? wbuffer_bvalid[0][j] : '0;
            for(int k=1; k<DCACHE_WBUF_DEPTH;k++) 
                wbuffer_be[j] |= (wbuffer_hit_oh[k]) ? wbuffer_bvalid[k][j] : '0;
        end
    end

    // OR reduction of writebuffer data
    always_comb begin : p_wbuf_data_red
        wbuffer_rdata = (wbuffer_hit_oh[0]) ? wbuffer_data[0] : '0;
        for(int k=1; k<DCACHE_WBUF_DEPTH;k++)
            wbuffer_rdata |= (wbuffer_hit_oh[k]) ? wbuffer_data[k] : '0;
    end

    // OR reduction of selected cachelines
    always_comb begin : p_data_red
        rdata = rdata_cl[0];
        for(int k=1; k<DCACHE_SET_ASSOC;k++)
            rdata |= rdata_cl[k];
    end

///////////////////////////////////////////////////////
// memory arrays and regs
///////////////////////////////////////////////////////

    logic [DCACHE_TAG_WIDTH:0] vld_tag_rdata [DCACHE_SET_ASSOC-1:0];

    generate
        for (genvar k = 0; k < DCACHE_NUM_BANKS; k++) begin : g_data_banks
            // Data RAM
            sram #(
                .DATA_WIDTH ( 64*DCACHE_SET_ASSOC ),
                .NUM_WORDS  ( DCACHE_NUM_WORDS    )
            ) data_sram (
                .clk_i      ( clk_i               ),
                .rst_ni     ( rst_ni              ),
                .req_i      ( bank_req   [k]      ),
                .we_i       ( bank_we    [k]      ),
                .addr_i     ( bank_idx   [k]      ),
                .wdata_i    ( bank_wdata [k]      ),
                .be_i       ( bank_be    [k]      ),
                .rdata_o    ( bank_rdata [k]      )
            );
        end

        for (genvar i = 0; i < DCACHE_SET_ASSOC; i++) begin : g_sram

            assign tag_rdata[i]     = vld_tag_rdata[i][DCACHE_TAG_WIDTH-1:0];
            assign rd_vld_bits_o[i] = vld_tag_rdata[i][DCACHE_TAG_WIDTH];    
        
            // Tag RAM
            sram #(
                // tag + valid bit
                .DATA_WIDTH ( DCACHE_TAG_WIDTH+1 ),
                .NUM_WORDS  ( DCACHE_NUM_WORDS   )
            ) tag_sram (
                .clk_i     ( clk_i               ),
                .rst_ni    ( rst_ni              ),
                .req_i     ( vld_req[i]          ),
                .we_i      ( vld_we              ),
                .addr_i    ( vld_addr            ),
                .wdata_i   ( {vld_wdata[i], tag} ),
                .be_i      ( '1                  ),
                .rdata_o   ( vld_tag_rdata[i]    )
            );
        end
    endgenerate    


    always_ff @(posedge clk_i or negedge rst_ni) begin : p_regs
        if(~rst_ni) begin
            bank_idx_q <= '0;
            bank_off_q <= '0;
            vld_sel_q  <= '0;
        end else begin
            bank_idx_q <= bank_idx_d;
            bank_off_q <= bank_off_d;
            vld_sel_q  <= vld_sel_d ;
        end
    end



///////////////////////////////////////////////////////
// assertions
///////////////////////////////////////////////////////

    //pragma translate_off
    `ifndef VERILATOR

      hit_hot1: assert property (
          @(posedge clk_i) disable iff (~rst_ni) &vld_req |-> ~vld_we |=> $onehot0(rd_hit_oh_o))     
             else $fatal(1,"[l1 dcache] rd_hit_oh_o signal must be hot1");

      word_write_hot1: assert property (
          @(posedge clk_i) disable iff (~rst_ni) wr_ack_o |-> $onehot0(wr_req_i))     
             else $fatal(1,"[l1 dcache] wr_req_i signal must be hot1");

      wbuffer_hit_hot1: assert property (
          @(posedge clk_i) disable iff (~rst_ni) &vld_req |-> ~vld_we |=> $onehot0(wbuffer_hit_oh))     
             else $fatal(1,"[l1 dcache] wbuffer_hit_oh signal must be hot1");



       // initial begin
       //    // assert wrong parameterizations
       //    assert (DCACHE_INDEX_WIDTH<=12) 
       //      else $fatal(1,"[l1 dcache] cache index width can be maximum 12bit since VM uses 4kB pages");    
       // end
    `endif
    //pragma translate_on

endmodule // serpent_dcache_mem

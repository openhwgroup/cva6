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
// Notes: 1) reads trigger a readout of all ways, and the way where the tag hits is selected
//           writes typically go to a single way, and can either be full cacheline access (refills), or single word accesses (writes)
//           the cache is multi-banked and hence writes and reads can occur simultaneously if they go to different offsets.
//
//        2) port 0 is special in the sense that it is the only port that has write access to the cache

import ariane_pkg::*;
import serpent_cache_pkg::*;

module serpent_dcache_mem #(
        parameter int unsigned NUM_PORTS     = 3,
        parameter     NC_ADDR_BEGIN          = 40'h8000000000, // start address of noncacheable I/O region
        parameter bit NC_ADDR_GE_LT          = 1'b1            // determines how the physical address is compared with NC_ADDR_BEGIN
    )(
        input  logic                                             clk_i,
        input  logic                                             rst_ni,
           
        input logic                                              cache_en_i,     // make sure this is registered
    
        input  logic  [NUM_PORTS-1:0][DCACHE_TAG_WIDTH-1:0]      tag_i,          // tag in - comes one cycle later
        input  logic  [NUM_PORTS-1:0][DCACHE_CL_IDX_WIDTH-1:0]   idx_i, 
        input  logic  [NUM_PORTS-1:0][DCACHE_OFFSET_WIDTH-1:0]   off_i, 
        
        input  logic  [NUM_PORTS-1:0]                            rd_req_i,       // read the word at offset off_i[:3] in all ways
        output logic  [NUM_PORTS-1:0]                            gnt_o, 
        
        // only available on port 0
        input  logic                [DCACHE_SET_ASSOC-1:0]       wr_req_i,       // write a single word to offset off_i[:3] 
        input  logic                [DCACHE_SET_ASSOC-1:0]       wr_cl_req_i,    // writes a full cacheline    
        input  logic                [DCACHE_LINE_WIDTH-1:0]      wr_cl_data_i, 
        input  logic                [DCACHE_LINE_WIDTH/8-1:0]    wr_cl_data_be_i, 
        input  logic                                             wr_cl_data_is_nc_i, // used to bypass data read from memory
        input  logic                [DCACHE_SET_ASSOC-1:0]       wr_vld_data_i,      // valid bits
        // single word write, no access to tags and valid bits
        input  logic                [63:0]                       wr_data_i,      
        input  logic                [7:0]                        wr_data_be_i, 
        
        // shared by all ports
        output logic                [63:0]                       rd_data_o,
        output logic                [DCACHE_SET_ASSOC-1:0]       rd_vld_data_o,
        output logic                [DCACHE_SET_ASSOC-1:0]       rd_hit_oh_o,
        output logic                                             rd_paddr_is_nc_o
    );


// ///////////////////////////////////////////////////////
// // arbiter
// ///////////////////////////////////////////////////////

//     // Priority is highest for lowest index in port array
   
//     // Bank mapping:
//     //
//     // Bank 0                   Bank 2  
//     // [way0, w0] [way1, w0] .. [way0, w1] [way1, w1] .. 

//     logic [NUM_PORTS-1:0][DCACHE_NUM_BANKS-1:0]        port_bank_req; 
//     logic [NUM_PORTS-1:0][DCACHE_NUM_BANKS-1:0]        port_bank_gnt; 
//     logic [DCACHE_NUM_BANKS-1:0]                       bank_gnt;

//     generate 
//         // first port has write access
//         // full cl write request will block read requests of lower prio ports
//         // only single word writes can interleave with single word reads
//         assign port_bank_req[0]    =  (wr_cl_req_i)                ? '1 :                                  
//                                       (rd_req_i[0] | |wr_req_i[0]) ?  dcache_cl_bin2oh(off_i[DCACHE_OFFSET_WIDTH-1:3]) : '0;
        
//         for (genvar k=1;k<NUM_PORTS;k++) begin : g_req
//             assign port_bank_req[k]    =  (rd_req_i[k]) ? dcache_cl_bin2oh(off_i[DCACHE_OFFSET_WIDTH-1:3]) : '0;
//         end

//         // check whether the request matches with the grant
//         for (genvar k=0;k<NUM_PORTS;k++) begin : g_gnt
//             assign gnt_o[k]   = (port_bank_gnt[k] ==  port_bank_req[k]);
//         end
//     endgenerate

//     // priority arbiting for each bank separately
//     always_comb begin : p_prio_arb
//         automatic logic tmp; 
//         port_bank_gnt = '0;
//         bank_gnt      = '0;
//         // loop over banks
//         for(int j=0;j<DCACHE_NUM_BANKS;j++) begin
//             tmp = 1'b0;
//             // loop over ports
//             for (int k=0;k<NUM_PORTS;k++) begin
//                 if(port_bank_req[k][j]) begin
//                     port_bank_gnt[k][j] = 1'b1;
//                     tmp                 = 1'b1; 
//                     break;
//                 end
//                 // can only have one read request at the moment 
//                 // due to contentions at the valid/tag memory
//                 // note: single word writes do NOT need access to the valid/tag memory
//                 // at the moment
//                 if(rd_req_i[k]) begin
//                     break;
//                 end
//             end
//             bank_gnt[j] = tmp;
//         end            
//     end

// ///////////////////////////////////////////////////////
// // address and data muxes
// ///////////////////////////////////////////////////////

//     logic [DCACHE_NUM_BANKS-1:0]                                 bank_req;
//     logic [DCACHE_NUM_BANKS-1:0]                                 bank_we;
//     logic [DCACHE_NUM_BANKS-1:0][DCACHE_SET_ASSOC-1:0][7:0]      bank_be;
//     logic [DCACHE_NUM_BANKS-1:0][DCACHE_CL_IDX_WIDTH-1:0]        bank_idx;
//     logic [DCACHE_NUM_BANKS-1:0][DCACHE_OFFSET_WIDTH-1:0]        bank_off_d, bank_off_q;
    
//     logic [DCACHE_NUM_BANKS-1:0][DCACHE_SET_ASSOC-1:0][63:0]     bank_wdata;                   // 
//     logic [DCACHE_NUM_BANKS-1:0][DCACHE_SET_ASSOC-1:0][63:0]     bank_rdata;                   // 
//     logic [DCACHE_SET_ASSOC-1:0][63:0]                           bank_sel;                     // selected word from each cacheline

//     logic [DCACHE_TAG_WIDTH-1:0]                                 tag;
//     logic [DCACHE_SET_ASSOC-1:0]                                 vld_req;                      // bit enable for valid regs
//     logic                                                        vld_we;                       // valid bits write enable
//     logic [DCACHE_SET_ASSOC-1:0]                                 vld_wdata;                    // valid bits to write
//     logic [DCACHE_SET_ASSOC-1:0][DCACHE_TAG_WIDTH-1:0]           tag_rdata;                    // these are the tags coming from the tagmem
//     logic                       [DCACHE_CL_IDX_WIDTH-1:0]        vld_addr;                     // valid bit 
    
//     logic [NUM_PORTS-1:0][$log2(DCACHE_NUM_BANKS)-1:0]           port_bank_sel, vld_sel_d, vld_sel_q;
//     logic                                                        byp_en_d, byp_en_q;


//     assign bank_req = bank_gnt;   
//     assign bank_we  = (((|wr_req_i) | (|wr_cl_req_i)) & ~wr_cl_data_is_nc_i) ? bank_gnt : '0;   

//     generate 
//         for (genvar k=0;k<DCACHE_NUM_BANKS;k++) begin : g_bank

//             for (genvar j=0;j<DCACHE_SET_ASSOC;j++) begin : g_bank_way
//                 assign bank_be[k][j]   = (wr_cl_req_i[j]) ? wr_cl_data_be_i[k*8 +: 8] : 
//                                          (wr_req_i   [j]) ? wr_data_be_i              :
//                                          '0;
                
//                 assign bank_wdata[k][j] = (|wr_cl_req_i) ?  wr_cl_data_i[k*64 +: 64] :
//                                                             wr_data_i;    
//             end

//             lzc #(
//                 .WIDTH   ( NUM_PORTS          )
//             ) i_lzc (
//                 .in_i    ( port_bank_req[k]   ),// use req signals here for better timing
//                 .cnt_o   ( port_bank_sel[k]   ),
//                 .empty_o (                    )
//             );

//             assign bank_idx[k]   = idx_i[port_bank_sel[k]];
//             assign bank_off_d[k] = off_i[port_bank_sel[k]];

//         end
//     endgenerate

//     // only reads and full cl writes access the tag array
//     lzc #(
//         .WIDTH   ( NUM_PORTS          )
//     ) i_lzc (
//         .in_i    ( wr_cl_req_i | rd_req_i ),
//         .cnt_o   ( vld_sel_d              ),
//         .empty_o (                        )
//     );

//     assign vld_addr  = idx_i[vld_sel_d];
//     assign tag       = tag_i[vld_sel_q];// delayed by one cycle
//     assign vld_req   = (|wr_cl_req_i) ? wr_cl_req_i :
//                        (|rd_req_i)    ? '1          : 
//                                         '0;                 
//     assign vld_we    = ((|bank_gnt) & ~wr_cl_data_is_nc_i) ? wr_cl_req_i : '0; 
//     assign vld_wdata = wr_vld_data_i;

//     assign byp_en_d  = |wr_cl_req_i;

//     always_ff @(posedge clk_i or negedge rst_ni) begin : p_regs
//         if(~rst_ni) begin
//             bank_off_q    <= '0;
//             vld_sel_q     <= '0;
//             byp_en_q      <= '0;
//         end else begin
//             bank_off_q    <= bank_off_d;
//             vld_sel_q     <= vld_sel_d;
//             byp_en_q      <= byp_en_d;
//         end
//     end


// ///////////////////////////////////////////////////////
// // tag comparison, hit generation
// ///////////////////////////////////////////////////////

//     // tag comparison of way 0                                    
//     assign rd_hit_oh_o[0] = (tag == tag_rdata[0]) & rd_vld_data_o[0];

//     // use way 0 to bypass read data in case we missed on the cache or in case the req is NC
//     assign bank_sel[0] = (byp_en_q)       ? wr_cl_data_i[bank_off_q[DCACHE_OFFSET_WIDTH-1:3]];
//                          (rd_hit_oh_o[0]) ? bank_rdata[0][bank_off_q[DCACHE_OFFSET_WIDTH-1:3]]:
//                                           ? '0 :
    
//     generate 
//         for (genvar i=1;i<DCACHE_SET_ASSOC;i++) begin : g_tag_cmpsel
//             // tag comparison of ways >0
//             assign rd_hit_oh_o[i] = (tag == tag_rdata[i]) & rd_vld_data_o[i];

//             // byte offset mux of ways >0
//             assign cl_sel[i] = (rd_hit_oh_o[i] & ~byp_en_q) ? bank_rdata[i][bank_off_q[DCACHE_OFFSET_WIDTH-1:3]] : '0;
//         end
//     endgenerate
    
//     // OR reduction of selected cachelines
//     always_comb begin : p_reduction
//         rd_data_o = cl_sel[0];
//         for(int i=1; i<DCACHE_SET_ASSOC;i++)
//             rd_data_o |= cl_sel[i];
//     end

//     generate 
//         if (NC_ADDR_GE_LT) begin : g_nc_addr_high
//             assign rd_paddr_is_nc_o = (tag >= (NC_ADDR_BEGIN>>ICACHE_INDEX_WIDTH)) | ~cache_en_i;
//         end
//         if (~NC_ADDR_GE_LT) begin : g_nc_addr_low
//             assign rd_paddr_is_nc_o = (tag < (NC_ADDR_BEGIN>>ICACHE_INDEX_WIDTH))  | ~cache_en_i;
//         end
//     endgenerate   

// ///////////////////////////////////////////////////////
// // memory arrays and regs
// ///////////////////////////////////////////////////////

//     logic [ICACHE_TAG_WIDTH:0] vld_tag_rdata [ICACHE_SET_ASSOC-1:0];

//     generate
//         for (genvar k = 0; k < DCACHE_NUM_BANKS; k++) begin : g_data_banks
//             // Data RAM
//             sram #(
//                 .DATA_WIDTH ( 64*DCACHE_SET_ASSOC ),
//                 .NUM_WORDS  ( DCACHE_NUM_WORDS    )
//             ) data_sram (
//                 .clk_i      ( clk_i               ),
//                 .rst_ni     ( rst_ni              ),
//                 .req_i      ( bank_req   [k]      ),
//                 .we_i       ( bank_we    [k]      ),
//                 .addr_i     ( bank_idx   [k]      ),
//                 .wdata_i    ( bank_wdata [k]      ),
//                 .be_i       ( bank_be    [k]      ),
//                 .rdata_o    ( bank_rdata [k]      )
//             );
//         end

//         for (genvar i = 0; i < ICACHE_SET_ASSOC; i++) begin : g_sram

//             assign tag_rdata[i] = vld_tag_rdata[i][ICACHE_TAG_WIDTH-1:0];
//             assign vld_rdata[i] = vld_tag_rdata[i][ICACHE_TAG_WIDTH];    
        
//             // Tag RAM
//             sram #(
//                 // tag + valid bit
//                 .DATA_WIDTH ( ICACHE_TAG_WIDTH+1 ),
//                 .NUM_WORDS  ( ICACHE_NUM_WORDS   )
//             ) tag_sram (
//                 .clk_i     ( clk_i               ),
//                 .rst_ni    ( rst_ni              ),
//                 .req_i     ( vld_req[i]          ),
//                 .we_i      ( vld_we              ),
//                 .addr_i    ( vld_addr            ),
//                 .wdata_i   ( {vld_wdata[i], tag} ),
//                 .be_i      ( '1                  ),
//                 .rdata_o   ( vld_tag_rdata[i]    )
//             );
//         end
//     endgenerate    


// ///////////////////////////////////////////////////////
// // assertions
// ///////////////////////////////////////////////////////

// //pragma translate_off
// `ifndef VERILATOR

//     // //needs to be hot one
//     // wr_req_i
//     // // hot one per bank
//     // port_bank_gnt[ports][banks]

//   // noncacheable0: assert property (
//   //     @(posedge clk_i) disable iff (~rst_ni) paddr_is_nc |-> mem_rtrn_vld_i && (mem_rtrn_i.rtype == ICACHE_IFILL_ACK) |-> mem_rtrn_i.nc)       
//   //        else $fatal("[l1 icache] NC paddr implies nc ifill");

//   // noncacheable1: assert property (
//   //     @(posedge clk_i) disable iff (~rst_ni) mem_rtrn_vld_i |-> mem_rtrn_i.f4b |-> mem_rtrn_i.nc)       
//   //        else $fatal(1,"[l1 icache] 4b ifill implies NC");

//   // noncacheable2: assert property (
//   //     @(posedge clk_i) disable iff (~rst_ni) mem_rtrn_vld_i |-> mem_rtrn_i.nc |-> mem_rtrn_i.f4b)       
//   //        else $fatal(1,"[l1 icache] NC implies 4b ifill");         

//   // repl_inval0: assert property (
//   //     @(posedge clk_i) disable iff (~rst_ni) cache_wren |-> ~(mem_rtrn_i.inv.all | mem_rtrn_i.inv.vld))       
//   //        else $fatal(1,"[l1 icache] cannot replace cacheline and invalidate cacheline simultaneously");

//   // repl_inval1: assert property (
//   //     @(posedge clk_i) disable iff (~rst_ni) (mem_rtrn_i.inv.all | mem_rtrn_i.inv.vld) |-> ~cache_wren)       
//   //        else $fatal(1,"[l1 icache] cannot replace cacheline and invalidate cacheline simultaneously");
  
//   // invalid_state: assert property (
//   //     @(posedge clk_i) disable iff (~rst_ni) (state_q inside {FLUSH, IDLE, READ, MISS, TLB_MISS, KILL_ATRANS, KILL_MISS}))     
//   //        else $fatal(1,"[l1 icache] fsm reached an invalid state");

//   // hot1: assert property (
//   //     @(posedge clk_i) disable iff (~rst_ni) (~inv_en) |=> cmp_en_q |-> $onehot0(cl_hit))     
//   //        else $fatal(1,"[l1 icache] cl_hit signal must be hot1");

//   //  initial begin
//   //     // assert wrong parameterizations
//   //     assert (ICACHE_INDEX_WIDTH<=12) 
//   //       else $fatal(1,"[l1 icache] cache index width can be maximum 12bit since VM uses 4kB pages");    
//   //  end
// `endif
// //pragma translate_on

endmodule // serpent_dcache_mem

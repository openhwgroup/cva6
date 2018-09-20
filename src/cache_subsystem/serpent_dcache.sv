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
// Description: Instruction cache that is compatible with openpiton.

import ariane_pkg::*;
import serpent_cache_pkg::*;

module serpent_dcache #(
    parameter     NC_ADDR_BEGIN          = 40'h8000000000, // start address of noncacheable I/O region
    parameter bit NC_ADDR_GE_LT          = 1'b1            // determines how the physical address is compared with NC_ADDR_BEGIN
)(
    input  logic                           clk_i,       // Clock
    input  logic                           rst_ni,      // Asynchronous reset active low
    
    // Cache management
    input  logic                           enable_i,    // from CSR
    input  logic                           flush_i,     // high until acknowledged
    output logic                           flush_ack_o, // send a single cycle acknowledge signal when the cache is flushed
    output logic                           miss_o,      // we missed on a ld/st
    output logic                           wbuffer_empty_o,

    // AMO interface
    input  amo_req_t                       amo_req_i,
    output amo_resp_t                      amo_ack_o,
   
    // Request ports
    input  dcache_req_i_t [2:0]            req_ports_i,  // request ports
    output dcache_req_o_t [2:0]            req_ports_o,  // request ports 

    input  logic                           mem_rtrn_vld_i,
    input  dcache_rtrn_t                   mem_rtrn_i,
    output logic                           mem_data_req_o,
    input  logic                           mem_data_ack_i,
    output dcache_req_t                    mem_data_o
);
    
    // LD unit and PTW    
    localparam NUM_RD_PORTS = 3;

    // miss unit <-> read controllers
    logic cache_en, flush_en;
    
    // miss unit <-> memory
    logic bypass_en;
    logic [DCACHE_SET_ASSOC-1:0]    wr_cl_vld;
    logic [DCACHE_TAG_WIDTH-1:0]    wr_cl_tag;
    logic [DCACHE_CL_IDX_WIDTH-1:0] wr_cl_idx;
    logic [DCACHE_OFFSET_WIDTH-1:0] wr_cl_off;
    logic [DCACHE_LINE_WIDTH-1:0]   wr_cl_data;
    logic [DCACHE_LINE_WIDTH/8-1:0] wr_cl_data_be;
    logic                           wr_cl_data_is_nc;
    logic                           wr_cl_byp_en;
    logic [DCACHE_SET_ASSOC-1:0]    wr_vld_bits;
    logic [DCACHE_SET_ASSOC-1:0]    wr_req;
    logic                           wr_ack;
    logic [DCACHE_CL_IDX_WIDTH-1:0] wr_idx;
    logic [DCACHE_OFFSET_WIDTH-1:0] wr_off;
    logic [63:0]                    wr_data;
    logic [7:0]                     wr_data_be;
    
    // miss unit <-> controllers/wbuffer
    logic [NUM_RD_PORTS-1:0]                          miss_req;
    logic [NUM_RD_PORTS-1:0]                          miss_ack;
    logic [NUM_RD_PORTS-1:0]                          miss_nc;
    logic [NUM_RD_PORTS-1:0]                          miss_we;
    logic [NUM_RD_PORTS-1:0][63:0]                    miss_wdata;
    logic [NUM_RD_PORTS-1:0][63:0]                    miss_paddr;
    logic [NUM_RD_PORTS-1:0][DCACHE_SET_ASSOC-1:0]    miss_vld_bits;
    logic [NUM_RD_PORTS-1:0][2:0]                     miss_size;
    logic [NUM_RD_PORTS-1:0][DCACHE_ID_WIDTH-1:0]     miss_id;
    logic                                             miss_rtrn;
    logic [DCACHE_ID_WIDTH-1:0]                       miss_rtrn_id;
 
    // memory <-> read controllers/miss unit
    logic [NUM_RD_PORTS:0]                            rd_req;
    logic [NUM_RD_PORTS:0]                            rd_ack;
    logic [NUM_RD_PORTS-1:0][DCACHE_TAG_WIDTH-1:0]    rd_tag;
    logic [NUM_RD_PORTS-1:0][DCACHE_CL_IDX_WIDTH-1:0] rd_idx;
    logic [NUM_RD_PORTS-1:0][DCACHE_OFFSET_WIDTH-1:0] rd_off;
    logic [63:0]                                      rd_data;
    logic [DCACHE_SET_ASSOC-1:0]                      rd_vld_bits;
    logic [DCACHE_SET_ASSOC-1:0]                      rd_hit_oh;

    // miss unit <-> wbuffer    
    logic                           inval_vld;
    logic [DCACHE_CL_IDX_WIDTH-1:0] inval_cl_idx;   

    // wbuffer <-> memory
    wbuffer_t [DCACHE_WBUF_DEPTH-1:0] wbuffer_data;
    

///////////////////////////////////////////////////////
// miss handling unit
///////////////////////////////////////////////////////

    serpent_dcache_missunit #(
        .NUM_PORTS(NUM_RD_PORTS)
    ) i_serpent_dcache_missunit (
        .clk_i              ( clk_i              ),
        .rst_ni             ( rst_ni             ),
        .enable_i           ( enable_i           ),
        .flush_i            ( flush_i            ),
        .flush_ack_o        ( flush_ack_o        ),
        .miss_o             ( miss_o             ),
        .wbuffer_empty_i    ( wbuffer_empty_o    ),
        .cache_en_o         ( cache_en           ),
        .flush_en_o         ( flush_en           ),
        // amo interface 
        .amo_req_i          ( amo_req_i          ),
        .amo_ack_o          ( amo_ack_o          ),
        // miss handling interface 
        .miss_req_i         ( miss_req           ),
        .miss_ack_o         ( miss_ack           ),
        .miss_nc_i          ( miss_nc            ),
        .miss_we_i          ( miss_we            ),
        .miss_wdata_i       ( miss_wdata         ),
        .miss_paddr_i       ( miss_paddr         ),
        .miss_vld_bits_i    ( miss_vld_bits      ),
        .miss_size_i        ( miss_size          ),
        .miss_id_i          ( miss_id            ),
        // to writebuffer
        .miss_rtrn_o        ( miss_rtrn          ),
        .miss_rtrn_id_o     ( miss_rtrn_id       ),
        .inval_vld_o        ( inval_vld          ),
        .inval_cl_idx_o     ( inval_cl_idx       ),
        // cache memory interface 
        .wr_cl_vld_o        ( wr_cl_vld          ),
        .wr_cl_tag_o        ( wr_cl_tag          ),
        .wr_cl_idx_o        ( wr_cl_idx          ),
        .wr_cl_off_o        ( wr_cl_off          ),
        .wr_cl_data_o       ( wr_cl_data         ),
        .wr_cl_data_be_o    ( wr_cl_data_be      ),
        .wr_vld_bits_o      ( wr_vld_bits        ),
        .wr_cl_byp_en_o     ( wr_cl_byp_en       ),
        // memory interface 
        .mem_rtrn_vld_i     ( mem_rtrn_vld_i     ),
        .mem_rtrn_i         ( mem_rtrn_i         ),
        .mem_data_req_o     ( mem_data_req_o     ),
        .mem_data_ack_i     ( mem_data_ack_i     ),
        .mem_data_o         ( mem_data_o         )
    );

///////////////////////////////////////////////////////
// read controllers (LD unit and PTW/MMU)
///////////////////////////////////////////////////////

    generate
        // note: last read port is used by the write buffer
        for(genvar k=0; k<NUM_RD_PORTS-1; k++) begin
        serpent_dcache_ctrl #(
                .NC_ADDR_BEGIN(NC_ADDR_BEGIN), 
                .NC_ADDR_GE_LT(NC_ADDR_GE_LT)) 
            i_serpent_dcache_ctrl (
                .clk_i           ( clk_i            ),
                .rst_ni          ( rst_ni           ),
                .flush_i         ( flush_en         ),
                .cache_en_i      ( cache_en         ),
                // reqs from core
                .req_port_i      ( req_ports_i  [k] ),
                .req_port_o      ( req_ports_o  [k] ),
                // miss interface
                .miss_req_o      ( miss_req     [k] ),
                .miss_ack_i      ( miss_ack     [k] ),
                .miss_we_o       ( miss_we      [k] ),
                .miss_wdata_o    ( miss_wdata   [k] ),
                .miss_vld_bits_o ( miss_vld_bits[k] ),
                .miss_paddr_o    ( miss_paddr   [k] ),
                .miss_nc_o       ( miss_nc      [k] ),
                .miss_size_o     ( miss_size    [k] ),
                .miss_id_o       ( miss_id      [k] ),
                // cache mem interface
                .rd_tag_o        ( rd_tag       [k] ),
                .rd_idx_o        ( rd_idx       [k] ),
                .rd_off_o        ( rd_off       [k] ),
                .rd_req_o        ( rd_req       [k] ),
                .rd_ack_i        ( rd_ack       [k] ),
                .rd_data_i       ( rd_data          ),
                .rd_vld_data_i   ( rd_vld_data      ),
                .rd_hit_oh_i     ( rd_hit_oh        )
            );
        end
    endgenerate

///////////////////////////////////////////////////////
// store unit controller
///////////////////////////////////////////////////////

serpent_dcache_wbuffer #(
        .NUM_WORDS     ( DCACHE_WBUF_DEPTH     ),
        .MAX_TX        ( DCACHE_MAX_TX         ),
        .NC_ADDR_BEGIN ( NC_ADDR_BEGIN         ), 
        .NC_ADDR_GE_LT ( NC_ADDR_GE_LT         )) 
    i_serpent_dcache_wbuffer (
        .clk_i           ( clk_i               ),
        .rst_ni          ( rst_ni              ),
        .empty_o         ( wbuffer_empty_o     ),
        .cache_en_i      ( cache_en            ),
        // request ports from core (store unit)
        .req_port_i      ( req_ports_i  [2]    ),
        .req_port_o      ( req_ports_o  [2]    ),
        // miss unit interface
        .miss_req_o      ( miss_req     [2]    ),
        .miss_ack_i      ( miss_ack     [2]    ),
        .miss_we_o       ( miss_we      [2]    ),
        .miss_wdata_o    ( miss_wdata   [2]    ),
        .miss_vld_bits_o ( miss_vld_bits[2]    ),
        .miss_paddr_o    ( miss_paddr   [2]    ),
        .miss_nc_o       ( miss_nc      [2]    ),
        .miss_size_o     ( miss_size    [2]    ),
        .miss_id_o       ( miss_id      [2]    ),
        .miss_rtrn_i     ( miss_rtrn           ),
        .miss_rtrn_id_i  ( miss_rtrn_id        ),
        // cache read interface
        .rd_tag_o        ( rd_tag       [2]    ),
        .rd_idx_o        ( rd_idx       [2]    ),
        .rd_off_o        ( rd_off       [2]    ),
        .rd_req_o        ( rd_req       [2]    ),
        .rd_ack_i        ( rd_ack       [2]    ),
        .rd_data_i       ( rd_data             ),
        .rd_vld_data_i   ( rd_vld_bits         ),
        .rd_hit_oh_i     ( rd_hit_oh           ),
         // incoming invalidations
        .inval_vld_i     ( inval_vld           ),
        .inval_cl_idx_i  ( inval_cl_idx        ),
        // single word write interface
        .wr_req_o        ( wr_req              ),
        .wr_ack_i        ( wr_ack              ),
        .wr_idx_o        ( wr_idx              ),
        .wr_off_o        ( wr_off              ),
        .wr_data_o       ( wr_data             ),
        .wr_data_be      ( wr_data_be          ),
        // write buffer forwarding
        .wbuffer_data_o  ( wbuffer_data        )
    );

///////////////////////////////////////////////////////
// memory arrays, arbitration and tag comparison
///////////////////////////////////////////////////////

   serpent_dcache_mem #(
        .NUM_RD_PORTS(NUM_RD_PORTS)
        ) i_serpent_dcache_mem (
        .clk_i             ( clk_i              ),
        .rst_ni            ( rst_ni             ),
        // read ports
        .rd_tag_i          ( rd_tag             ),
        .rd_idx_i          ( rd_idx             ),
        .rd_off_i          ( rd_off             ),
        .rd_req_i          ( rd_req             ),
        .rd_ack_o          ( rd_ack             ),
        .rd_vld_bits_o     ( rd_vld_bits        ),
        .rd_hit_oh_o       ( rd_hit_oh          ),
        .rd_data_o         ( rd_data            ),
        // cacheline write port
        .wr_cl_vld_i       ( wr_cl_vld           ),
        .wr_cl_tag_i       ( wr_cl_tag          ),
        .wr_cl_idx_i       ( wr_cl_idx          ),
        .wr_cl_off_i       ( wr_cl_off          ),
        .wr_cl_data_i      ( wr_cl_data         ),
        .wr_cl_data_be_i   ( wr_cl_data_be      ),
        .wr_vld_bits_i     ( wr_vld_bits        ),
        .wr_cl_byp_en_i    ( wr_cl_byp_en       ),
        // single word write port
        .wr_req_i          ( wr_req             ),
        .wr_ack_o          ( wr_ack             ),
        .wr_idx_i          ( wr_idx             ),
        .wr_off_i          ( wr_off             ),
        .wr_data_i         ( wr_data            ),
        .wr_data_be_i      ( wr_data_be         ),
        // write buffer forwarding
        .wbuffer_data_i    ( wbuffer_data       )
    );

///////////////////////////////////////////////////////
// assertions
///////////////////////////////////////////////////////

// check for concurrency issues


//pragma translate_off
`ifndef VERILATOR

    // //needs to be hot one
    // wr_req_i
    // // hot one per bank
    // port_bank_gnt[ports][banks]

  // hot1: assert property (
  //     @(posedge clk_i) disable iff (~rst_ni) &vld_req |-> ~vld_we |=> $onehot0(rd_hit_oh_o))     
  //        else $fatal(1,"[l1 dcache] rd_hit_oh_o signal must be hot1");

  // noncacheable0: assert property (
  //     @(posedge clk_i) disable iff (~rst_ni) paddr_is_nc |-> mem_rtrn_vld_i && (mem_rtrn_i.rtype == DCACHE_IFILL_ACK) |-> mem_rtrn_i.nc)       
  //        else $fatal("[l1 icache] NC paddr implies nc ifill");

  // noncacheable1: assert property (
  //     @(posedge clk_i) disable iff (~rst_ni) mem_rtrn_vld_i |-> mem_rtrn_i.f4b |-> mem_rtrn_i.nc)       
  //        else $fatal(1,"[l1 icache] 4b ifill implies NC");

  // noncacheable2: assert property (
  //     @(posedge clk_i) disable iff (~rst_ni) mem_rtrn_vld_i |-> mem_rtrn_i.nc |-> mem_rtrn_i.f4b)       
  //        else $fatal(1,"[l1 icache] NC implies 4b ifill");         

  // repl_inval0: assert property (
  //     @(posedge clk_i) disable iff (~rst_ni) cache_wren |-> ~(mem_rtrn_i.inv.all | mem_rtrn_i.inv.vld))       
  //        else $fatal(1,"[l1 icache] cannot replace cacheline and invalidate cacheline simultaneously");

  // repl_inval1: assert property (
  //     @(posedge clk_i) disable iff (~rst_ni) (mem_rtrn_i.inv.all | mem_rtrn_i.inv.vld) |-> ~cache_wren)       
  //        else $fatal(1,"[l1 icache] cannot replace cacheline and invalidate cacheline simultaneously");
  
  // invalid_state: assert property (
  //     @(posedge clk_i) disable iff (~rst_ni) (state_q inside {FLUSH, IDLE, READ, MISS, TLB_MISS, KILL_ATRANS, KILL_MISS}))     
  //        else $fatal(1,"[l1 icache] fsm reached an invalid state");

  // hot1: assert property (
  //     @(posedge clk_i) disable iff (~rst_ni) (~inv_en) |=> cmp_en_q |-> $onehot0(cl_hit))     
  //        else $fatal(1,"[l1 icache] cl_hit signal must be hot1");

   // initial begin
   //    // assert wrong parameterizations
   //    assert (DCACHE_INDEX_WIDTH<=12) 
   //      else $fatal(1,"[l1 dcache] cache index width can be maximum 12bit since VM uses 4kB pages");    
   // end
`endif
//pragma translate_on


// `ifndef SYNTHESIS
//     initial begin
//         assert ($bits(data_if.aw_addr) == 64) else $fatal(1, "Ariane needs a 64-bit bus");
//         assert (DCACHE_LINE_WIDTH/64 inside {2, 4, 8, 16}) else $fatal(1, "Cache line size needs to be a power of two multiple of 64");
//     end
// `endif
endmodule // serpent_dcache

// Copyright (c) 2023 Thales.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// Author: Sebastien Jacq - Thales Research & Technology
// Date: 08/03/2023
//
// Description: N-way associative shared TLB, it allows to reduce the number 
//              of ITLB and DTLB entries.
//

/* verilator lint_off WIDTH */

module cva6_shared_tlb_sv32 import ariane_pkg::*; #(
        parameter int SHARED_TLB_DEPTH = 64,
        parameter int SHARED_TLB_WAYS = 2,
        parameter int ASID_WIDTH = 1,
        parameter ariane_pkg::ariane_cfg_t ArianeCfg = ariane_pkg::ArianeDefaultConfig
) (
    input  logic                    clk_i,                  // Clock
    input  logic                    rst_ni,                 // Asynchronous reset active low
    input  logic                    flush_i,               

    input  logic                    enable_translation_i,   // CSRs indicate to enable SV32
    input  logic                    en_ld_st_translation_i, // enable virtual memory translation for load/stores

    input  logic [ASID_WIDTH-1:0]   asid_i,

    // from TLBs
    // did we miss?
    input  logic                    itlb_access_i,
    input  logic                    itlb_hit_i,
    input  logic [riscv::VLEN-1:0]  itlb_vaddr_i,

    input  logic                    dtlb_access_i,
    input  logic                    dtlb_hit_i,
    input  logic [riscv::VLEN-1:0]  dtlb_vaddr_i,

    // to TLBs, update logic
    output tlb_update_sv32_t        itlb_update_o,
    output tlb_update_sv32_t        dtlb_update_o,

    // Performance counters
    output logic                    itlb_miss_o,
    output logic                    dtlb_miss_o,
    
    output logic                    shared_tlb_access_o,
    output logic                    shared_tlb_hit_o,
    output logic [riscv::VLEN-1:0]  shared_tlb_vaddr_o,
    
    output logic                    itlb_req_o,
    
    // Update shared TLB in case of miss
    input  tlb_update_sv32_t        shared_tlb_update_i

);

    function logic [SHARED_TLB_WAYS-1:0] shared_tlb_way_bin2oh ( input logic [$clog2(SHARED_TLB_WAYS)-1:0] in);
      logic [SHARED_TLB_WAYS-1:0] out;
      out     = '0;
      out[in] = 1'b1;
      return out;
    endfunction

    typedef struct packed {
      logic [8:0]            asid; //9 bits wide
      logic [9:0]            vpn1; //10 bits wide
      logic [9:0]            vpn0; //10 bits wide
      logic                  is_4M;
    } shared_tag_t;

    shared_tag_t shared_tag_wr;
    shared_tag_t [SHARED_TLB_WAYS-1:0] shared_tag_rd;

    logic [SHARED_TLB_DEPTH-1:0][SHARED_TLB_WAYS-1:0] shared_tag_valid_q, shared_tag_valid_d ;

    logic [SHARED_TLB_WAYS-1:0]          shared_tag_valid;

    logic [SHARED_TLB_WAYS-1:0]          tag_wr_en;
    logic [$clog2(SHARED_TLB_DEPTH)-1:0] tag_wr_addr;
    logic [$bits(shared_tag_t)-1:0]      tag_wr_data;

    logic [SHARED_TLB_WAYS-1:0]          tag_rd_en;
    logic [$clog2(SHARED_TLB_DEPTH)-1:0] tag_rd_addr;
    logic [$bits(shared_tag_t)-1:0]      tag_rd_data [SHARED_TLB_WAYS-1:0];

    logic [SHARED_TLB_WAYS-1:0]          tag_req;
    logic [SHARED_TLB_WAYS-1:0]          tag_we;
    logic [$clog2(SHARED_TLB_DEPTH)-1:0] tag_addr;

    logic [SHARED_TLB_WAYS-1:0]          pte_wr_en;
    logic [$clog2(SHARED_TLB_DEPTH)-1:0] pte_wr_addr;
    logic [$bits(riscv::pte_sv32_t)-1:0] pte_wr_data;
     
    logic [SHARED_TLB_WAYS-1:0]          pte_rd_en;
    logic [$clog2(SHARED_TLB_DEPTH)-1:0] pte_rd_addr;
    logic [$bits(riscv::pte_sv32_t)-1:0] pte_rd_data [SHARED_TLB_WAYS-1:0];

    logic [SHARED_TLB_WAYS-1:0]          pte_req;
    logic [SHARED_TLB_WAYS-1:0]          pte_we;
    logic [$clog2(SHARED_TLB_DEPTH)-1:0] pte_addr;
    
    logic [9:0] vpn0_d, vpn1_d, vpn0_q, vpn1_q;

    riscv::pte_sv32_t [SHARED_TLB_WAYS-1:0] pte;

    logic [riscv::VLEN-1-12:0]  itlb_vpn_q;
    logic [riscv::VLEN-1-12:0]  dtlb_vpn_q;
    
    logic [ASID_WIDTH-1:0] tlb_update_asid_q, tlb_update_asid_d;
    
    logic                   shared_tlb_access_q, shared_tlb_access_d;
    logic                   shared_tlb_hit_d;
    logic [riscv::VLEN-1:0] shared_tlb_vaddr_q, shared_tlb_vaddr_d;
    
    logic itlb_req_d, itlb_req_q;
    logic dtlb_req_d, dtlb_req_q;

    // replacement strategy
    logic [SHARED_TLB_WAYS-1:0]          way_valid;
    logic                                update_lfsr;       // shift the LFSR
    logic [$clog2(SHARED_TLB_WAYS)-1:0]  inv_way;           // first non-valid encountered
    logic [$clog2(SHARED_TLB_WAYS)-1:0]  rnd_way;           // random index for replacement
    logic [$clog2(SHARED_TLB_WAYS)-1:0]  repl_way;          // way to replace
    logic [SHARED_TLB_WAYS-1:0]          repl_way_oh_d;     // way to replace (onehot)
    logic                                all_ways_valid;    // we need to switch repl strategy since all are valid

    assign shared_tlb_access_o = shared_tlb_access_q;
    assign shared_tlb_hit_o = shared_tlb_hit_d;
    assign shared_tlb_vaddr_o = shared_tlb_vaddr_q;
    
    assign itlb_req_o = itlb_req_q;
    
    ///////////////////////////////////////////////////////
    // tag comparison, hit generation
    ///////////////////////////////////////////////////////   
    always_comb begin : itlb_dtlb_miss
        itlb_miss_o     = 1'b0;
        dtlb_miss_o     = 1'b0;
        vpn0_d          = vpn0_q;
        vpn1_d          = vpn1_q;

        tag_rd_en       = '0;
        pte_rd_en       = '0;

        itlb_req_d      = 1'b0;
        dtlb_req_d      = 1'b0;

        tlb_update_asid_d    = tlb_update_asid_q;

        shared_tlb_access_d  = '0;
        shared_tlb_vaddr_d   = shared_tlb_vaddr_q;

        tag_rd_addr    = '0;
        pte_rd_addr    = '0;

        // if we got an ITLB miss
        if (enable_translation_i & itlb_access_i & ~itlb_hit_i & ~dtlb_access_i) begin
            tag_rd_en        = '1;
            tag_rd_addr      = itlb_vaddr_i[12+:$clog2(SHARED_TLB_DEPTH)];
            pte_rd_en        = '1;
            pte_rd_addr      = itlb_vaddr_i[12+:$clog2(SHARED_TLB_DEPTH)];
        
            vpn0_d           = itlb_vaddr_i[21:12];
            vpn1_d           = itlb_vaddr_i[31:22];
        
            itlb_miss_o      = 1'b1;
            itlb_req_d       = 1'b1;
         
            tlb_update_asid_d   = asid_i;
            
            shared_tlb_access_d = 1'b1;
            shared_tlb_vaddr_d  = itlb_vaddr_i;
              
        // we got an DTLB miss
        end else if (en_ld_st_translation_i & dtlb_access_i & ~dtlb_hit_i) begin
            tag_rd_en        = '1;
            tag_rd_addr      = dtlb_vaddr_i[12+:$clog2(SHARED_TLB_DEPTH)];
            pte_rd_en        = '1;
            pte_rd_addr      = dtlb_vaddr_i[12+:$clog2(SHARED_TLB_DEPTH)];

            vpn0_d           = dtlb_vaddr_i[21:12];
            vpn1_d           = dtlb_vaddr_i[31:22];
        
            dtlb_miss_o      = 1'b1;
            dtlb_req_d       = 1'b1;
            
            tlb_update_asid_d   = asid_i;
            
            shared_tlb_access_d = 1'b1;
            shared_tlb_vaddr_d  = dtlb_vaddr_i;      
        end
    end //itlb_dtlb_miss

    always_comb begin : tag_comparison
        shared_tlb_hit_d = 1'b0;
        dtlb_update_o = '0;
        itlb_update_o = '0;
        //number of ways
        for (int unsigned i = 0; i < SHARED_TLB_WAYS; i++) begin
            if (shared_tag_valid[i] && ((tlb_update_asid_q == shared_tag_rd[i].asid) || pte[i].g)  && vpn1_q == shared_tag_rd[i].vpn1) begin
                if (shared_tag_rd[i].is_4M || vpn0_q == shared_tag_rd[i].vpn0) begin
                    shared_tlb_hit_d    = 1'b1;
                    if (itlb_req_q) begin
                        itlb_update_o.valid = 1'b1;
                        itlb_update_o.vpn = itlb_vpn_q;
                        itlb_update_o.is_4M = shared_tag_rd[i].is_4M;
                        itlb_update_o.asid = tlb_update_asid_q;
                        itlb_update_o.content = pte[i];
                    end else if (dtlb_req_q) begin
                        dtlb_update_o.valid = 1'b1;
                        dtlb_update_o.vpn = dtlb_vpn_q;
                        dtlb_update_o.is_4M = shared_tag_rd[i].is_4M;
                        dtlb_update_o.asid = tlb_update_asid_q;
                        dtlb_update_o.content = pte[i];
                    end
                end
            end
        end
    end //tag_comparison
 
    // sequential process
    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (~rst_ni) begin
        itlb_vpn_q   <= '0;
        dtlb_vpn_q   <= '0;
        tlb_update_asid_q  <= '0;
        shared_tlb_access_q <= '0;
        shared_tlb_vaddr_q <= '0;
        shared_tag_valid_q <= '0;
        vpn0_q <= '0;
        vpn1_q <= '0;
        itlb_req_q <= '0;
        dtlb_req_q <= '0;
        shared_tag_valid <= '0;
      end else begin
        itlb_vpn_q   <= itlb_vaddr_i[riscv::SV-1:12];
        dtlb_vpn_q   <= dtlb_vaddr_i[riscv::SV-1:12];
        tlb_update_asid_q  <= tlb_update_asid_d;
        shared_tlb_access_q <= shared_tlb_access_d;
        shared_tlb_vaddr_q <= shared_tlb_vaddr_d;
        shared_tag_valid_q <= shared_tag_valid_d;
        vpn0_q <= vpn0_d;
        vpn1_q <= vpn1_d;
        itlb_req_q <= itlb_req_d;
        dtlb_req_q <= dtlb_req_d;
        shared_tag_valid <= shared_tag_valid_q[tag_rd_addr];
      end
    end

    // ------------------
    // Update and Flush
    // ------------------
    always_comb begin : update_flush
        shared_tag_valid_d = shared_tag_valid_q;
        tag_wr_en = '0;
        pte_wr_en = '0;
        
        if (flush_i) begin
	    shared_tag_valid_d = '0;
        end else if (shared_tlb_update_i.valid) begin
            for (int unsigned i = 0; i < SHARED_TLB_WAYS; i++) begin
                if (repl_way_oh_d[i]) begin
                    shared_tag_valid_d[shared_tlb_update_i.vpn[$clog2(SHARED_TLB_DEPTH)-1:0]][i] = 1'b1;
                    tag_wr_en[i] = 1'b1;
                    pte_wr_en[i] = 1'b1;
                end
            end
        end
    end //update_flush

    assign shared_tag_wr.asid  = shared_tlb_update_i.asid;
    assign shared_tag_wr.vpn1  = shared_tlb_update_i.vpn[19:10];
    assign shared_tag_wr.vpn0  = shared_tlb_update_i.vpn[9:0];
    assign shared_tag_wr.is_4M = shared_tlb_update_i.is_4M;

    assign tag_wr_addr = shared_tlb_update_i.vpn[$clog2(SHARED_TLB_DEPTH)-1:0];
    assign tag_wr_data = shared_tag_wr;  

    assign pte_wr_addr = shared_tlb_update_i.vpn[$clog2(SHARED_TLB_DEPTH)-1:0];
    assign pte_wr_data = shared_tlb_update_i.content;

    assign way_valid     = shared_tag_valid_q[shared_tlb_update_i.vpn[$clog2(SHARED_TLB_DEPTH)-1:0]];
    assign repl_way      = (all_ways_valid) ? rnd_way : inv_way;
    assign update_lfsr   = shared_tlb_update_i.valid & all_ways_valid;
    assign repl_way_oh_d = (shared_tlb_update_i.valid) ? shared_tlb_way_bin2oh(repl_way) : '0;

    lzc #(
        .WIDTH ( SHARED_TLB_WAYS )
    ) i_lzc (
        .in_i    ( ~way_valid     ),
        .cnt_o   ( inv_way        ),
        .empty_o ( all_ways_valid )
    );

    lfsr #(
        .LfsrWidth  ( 8       ),
        .OutWidth   ( $clog2(SHARED_TLB_WAYS))
    ) i_lfsr (
        .clk_i          ( clk_i       ),
        .rst_ni         ( rst_ni      ),
        .en_i           ( update_lfsr ),
        .out_o          ( rnd_way     )
    );

    ///////////////////////////////////////////////////////
    // memory arrays and regs
    ///////////////////////////////////////////////////////

    assign tag_req = tag_wr_en | tag_rd_en;
    assign tag_we = tag_wr_en;
    assign tag_addr = tag_wr_en ? tag_wr_addr : tag_rd_addr;

    assign pte_req = pte_wr_en | pte_rd_en;
    assign pte_we = pte_wr_en;
    assign pte_addr = pte_wr_en ? pte_wr_addr : pte_rd_addr;

    for (genvar i = 0; i < SHARED_TLB_WAYS; i++) begin : gen_sram
        // Tag RAM
        sram #(
            .DATA_WIDTH ( $bits(shared_tag_t) ),
            .NUM_WORDS  ( SHARED_TLB_DEPTH   )
        ) tag_sram (
            .clk_i      ( clk_i           ),
            .rst_ni     ( rst_ni          ),
            .req_i      ( tag_req[i]      ),
            .we_i       ( tag_we[i]       ),
            .addr_i     ( tag_addr        ),
            .wuser_i    ( '0              ),
            .wdata_i    ( tag_wr_data     ),
            .be_i       ( '1              ),
            .ruser_o    (                 ),
            .rdata_o    ( tag_rd_data[i]  )
        );

        assign shared_tag_rd[i] = shared_tag_t'(tag_rd_data[i]);
    
        // PTE RAM
        sram #(
            .DATA_WIDTH ( $bits(riscv::pte_sv32_t) ),
            .NUM_WORDS  ( SHARED_TLB_DEPTH   )
        ) pte_sram (
            .clk_i      ( clk_i           ),
            .rst_ni     ( rst_ni          ),
            .req_i      ( pte_req[i]      ),
            .we_i       ( pte_we[i]       ),
            .addr_i     ( pte_addr        ),
            .wuser_i    ( '0              ),
            .wdata_i    ( pte_wr_data     ),
            .be_i       ( '1              ),
            .ruser_o    (                 ),
            .rdata_o    ( pte_rd_data[i]  )
        );
        assign pte[i] = riscv::pte_sv32_t'(pte_rd_data[i]);
    end
endmodule

/* verilator lint_on WIDTH */

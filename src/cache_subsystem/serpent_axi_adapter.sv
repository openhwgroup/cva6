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
// Date: 08.08.2018
// Description: adapter module to connect the L1D$ and L1I$ to a 64bit AXI bus.
//

import ariane_pkg::*;
import serpent_cache_pkg::*;

module serpent_axi_adapter #(
  parameter int unsigned AxiIdWidth = 10
) (
   input logic                  clk_i,
   input logic                  rst_ni,

   // icache
   input  logic                 icache_data_req_i,
   output logic                 icache_data_ack_o,
   input  icache_req_t          icache_data_i,
   // returning packets must be consumed immediately
   output logic                 icache_rtrn_vld_o,
   output icache_rtrn_t         icache_rtrn_o,

   // dcache
   input  logic                 dcache_data_req_i,
   output logic                 dcache_data_ack_o,
   input  dcache_req_t          dcache_data_i,
   // returning packets must be consumed immediately
   output logic                 dcache_rtrn_vld_o,
   output dcache_rtrn_t         dcache_rtrn_o,

    // AXI port
    output ariane_axi::req_t    axi_req_o,
    input  ariane_axi::resp_t   axi_resp_i
);

// support up to 512bit cache lines
localparam AxiNumWords = ariane_pkg::ICACHE_LINE_WIDTH/64;

///////////////////////////////////////////////////////
// request path 
///////////////////////////////////////////////////////

icache_req_t icache_data;
logic icache_data_full, icache_data_empty;
dcache_req_t dcache_data;
logic dcache_data_full, dcache_data_empty;

logic [1:0] arb_req, arb_ack;
logic       arb_idx;

typedef enum logic [1:0] {IFILL, LRSC, ATOP, STD} tx_t;
tx_t tmp_type;

logic rd_pending_d, rd_pending_q;
logic axi_rd_req, axi_rd_gnt;
logic axi_wr_req, axi_wr_gnt;
logic axi_wr_valid, axi_rd_valid, axi_rd_rdy, axi_wr_rdy;
logic axi_rd_lock, axi_wr_lock, axi_rd_exokay, axi_wr_exokay;
logic [63:0]                    axi_rd_addr, axi_wr_addr;
logic [$clog2(AxiNumWords)-1:0] axi_rd_blen, axi_wr_blen;
logic [1:0] axi_rd_size, axi_wr_size;
logic [AxiIdWidth-1:0] axi_rd_id_in, axi_wr_id_in, axi_rd_id_out, axi_wr_id_out;
logic [AxiNumWords-1:0][63:0] axi_rd_data, axi_wr_data;
logic [AxiNumWords-1:0][7:0]  axi_wr_be;
logic [5:0] axi_wr_atop;


assign icache_data_ack_o  = icache_data_req_i & ~icache_data_full;
assign dcache_data_ack_o  = dcache_data_req_i & ~dcache_data_full;

// arbiter
assign arb_req           = {~dcache_data_empty, ~icache_data_empty};

rrarbiter #(
  .NUM_REQ(2),
  .LOCK_IN(1)
) i_rrarbiter (
  .clk_i  ( clk_i                   ),
  .rst_ni ( rst_ni                  ),
  .flush_i( '0                      ),
  .en_i   ( axi_rd_gnt | axi_wr_gnt ),
  .req_i  ( arb_req                 ),
  .ack_o  ( arb_ack                 ),
  .vld_o  (                         ),
  .idx_o  ( arb_idx                 )
);

// the axi interconnect does not correctly handle the ordering of read responses.
// workaround: only allow for one outstanding TX. need to improve this.
assign rd_pending_d = (axi_rd_valid) ? '0 : rd_pending_q | axi_rd_gnt;

always_ff @(posedge clk_i or negedge rst_ni) begin : p_regs
  if(~rst_ni) begin
    rd_pending_q <= '0;
  end else begin
    rd_pending_q <= rd_pending_d;
  end
end

// request side
always_comb begin : p_axi_req
  axi_wr_data  = dcache_data.data;
  axi_wr_addr  = dcache_data.paddr;
  axi_wr_size  = dcache_data.size[1:0];
  axi_wr_req   = 1'b0;
  axi_wr_blen  = '0;// single word writes
  axi_wr_be    = '0;
  axi_wr_lock  = '0;
  axi_wr_atop  = '0;

  axi_rd_req   = 1'b0;
  axi_rd_blen  = '0;
  axi_rd_lock  = '0;
  
  tmp_type     = STD;

  // decode message type
  if (|arb_req) begin
    if (arb_idx == 0) begin
      //////////////////////////////////////
      // IMISS  
      axi_rd_req   = !rd_pending_q;
      tmp_type     = IFILL;
      if (~icache_data.nc) begin
        axi_rd_blen = ariane_pkg::ICACHE_LINE_WIDTH/64-1;
      end  
      //////////////////////////////////////
    end else begin  
      unique case (dcache_data.rtype)
        //////////////////////////////////////
        serpent_cache_pkg::DCACHE_LOAD_REQ: begin
          axi_rd_req   = !rd_pending_q;
          if (dcache_data.size[2]) axi_rd_blen = ariane_pkg::DCACHE_LINE_WIDTH/64-1;
        end
        //////////////////////////////////////
        serpent_cache_pkg::DCACHE_STORE_REQ: begin
          axi_wr_req   = 1'b1;
          axi_wr_be    = serpent_cache_pkg::toByteEnable8(dcache_data.paddr[2:0], dcache_data.size[1:0]);
        end
        //////////////////////////////////////
        serpent_cache_pkg::DCACHE_ATOMIC_REQ: begin
          // default  
          axi_wr_req   = 1'b1;
          tmp_type     = ATOP; 
          axi_wr_be    = serpent_cache_pkg::toByteEnable8(dcache_data.paddr[2:0], dcache_data.size[1:0]);
          unique case (dcache_data.amo_op)
            AMO_LR: begin
              axi_rd_lock  = 1'b1;
              axi_rd_req   = !rd_pending_q;
              tmp_type     = LRSC; 
              // tie to zero in this special case
              axi_wr_req   = 1'b0;
              axi_wr_be    = '0;
            end
            AMO_SC: begin
              axi_wr_lock  = 1'b1;
              tmp_type     = LRSC;
            end  
            // RISC-V atops have a load semantic
            AMO_SWAP: axi_wr_atop  = {axi_pkg::ATOP_ATOMICLOAD, axi_pkg::ATOP_ATOMICSWAP};
            AMO_ADD:  axi_wr_atop  = {axi_pkg::ATOP_ATOMICLOAD, axi_pkg::ATOP_ADD};
            AMO_AND:  begin 
              // in this case we need to invert the data to get a "CLR" 
              axi_wr_data  = ~dcache_data.data;
              axi_wr_atop  = {axi_pkg::ATOP_ATOMICLOAD, axi_pkg::ATOP_CLR};
            end  
            AMO_OR:   axi_wr_atop  = {axi_pkg::ATOP_ATOMICLOAD, axi_pkg::ATOP_SET};
            AMO_XOR:  axi_wr_atop  = {axi_pkg::ATOP_ATOMICLOAD, axi_pkg::ATOP_EOR};
            AMO_MAX:  axi_wr_atop  = {axi_pkg::ATOP_ATOMICLOAD, axi_pkg::ATOP_SMAX};
            AMO_MAXU: axi_wr_atop  = {axi_pkg::ATOP_ATOMICLOAD, axi_pkg::ATOP_UMAX};
            AMO_MIN:  axi_wr_atop  = {axi_pkg::ATOP_ATOMICLOAD, axi_pkg::ATOP_SMIN}; 
            AMO_MINU: axi_wr_atop  = {axi_pkg::ATOP_ATOMICLOAD, axi_pkg::ATOP_UMIN}; 
          endcase  
        end
      //////////////////////////////////////
      endcase
    end 
    

    axi_wr_id_in = {dcache_data.tid, tmp_type, dcache_data.nc};

    // arbiter mux
    if (arb_idx) begin
      axi_rd_addr  = dcache_data.paddr;
      axi_rd_size  = dcache_data.size[1:0];
      axi_rd_id_in = {dcache_data.tid, tmp_type, dcache_data.nc};
    end else begin
      axi_rd_addr  = icache_data.paddr;
      axi_rd_size  = 2'b11;// always request 64bit words in case of ifill
      axi_rd_id_in = {icache_data.tid, tmp_type, icache_data.nc};
    end 
  end  
end  

fifo_v2 #(
     .dtype       (  icache_req_t            ),
     .DEPTH       (  ADAPTER_REQ_FIFO_DEPTH  )
) i_icache_data_fifo (
     .clk_i       (  clk_i                   ),
     .rst_ni      (  rst_ni                  ),
     .flush_i     (  1'b0                    ),
     .testmode_i  (  1'b0                    ),
     .full_o      (  icache_data_full        ),
     .empty_o     (  icache_data_empty       ),
     .alm_full_o  (                          ),
     .alm_empty_o (                          ),
     .data_i      (  icache_data_i           ),
     .push_i      (  icache_data_ack_o       ),
     .data_o      (  icache_data             ),
     .pop_i       (  arb_ack[0]              )
);

fifo_v2 #(
     .dtype       (  dcache_req_t            ),
     .DEPTH       (  ADAPTER_REQ_FIFO_DEPTH  )
) i_dcache_data_fifo (
     .clk_i       (  clk_i                   ),
     .rst_ni      (  rst_ni                  ),
     .flush_i     (  1'b0                    ),
     .testmode_i  (  1'b0                    ),
     .full_o      (  dcache_data_full        ),
     .empty_o     (  dcache_data_empty       ),
     .alm_full_o  (                          ),
     .alm_empty_o (                          ),
     .data_i      (  dcache_data_i           ),
     .push_i      (  dcache_data_ack_o       ),
     .data_o      (  dcache_data             ),
     .pop_i       (  arb_ack[1]              )
);

///////////////////////////////////////////////////////
// return path from L15
///////////////////////////////////////////////////////

always_comb begin : p_axi_rtrn
  dcache_rtrn_o              = '0;
  icache_rtrn_o              = '0;  
  icache_rtrn_vld_o          = 1'b0;
  dcache_rtrn_vld_o          = 1'b0;
  icache_rtrn_o.data         = axi_rd_data;
  dcache_rtrn_o.data         = axi_rd_data;
  
  // we are always ready to consume packets unconditionally,
  // but we give prio to read responses below
  axi_rd_rdy                 = 1'b1;
  axi_wr_rdy                 = 1'b1;
  
  //////////////////////////////////////
  if (axi_rd_valid) begin
    // we give prio to read responses
    axi_wr_rdy                 = 1'b0;
    unique case(tx_t'(axi_rd_id_out[2:1]))
      STD:   begin
        dcache_rtrn_vld_o      = 1'b1;
        dcache_rtrn_o.rtype    = serpent_cache_pkg::DCACHE_LOAD_ACK;
        dcache_rtrn_o.tid      = axi_rd_id_out>>3;
        dcache_rtrn_o.nc       = axi_rd_id_out[0];
      end  
      LRSC:  begin
        dcache_rtrn_vld_o      = 1'b1;
        dcache_rtrn_o.rtype    = serpent_cache_pkg::DCACHE_ATOMIC_ACK;
        dcache_rtrn_o.tid      = axi_rd_id_out>>3;
        dcache_rtrn_o.nc       = axi_rd_id_out[0];
      end  
      ATOP:  begin
        dcache_rtrn_vld_o      = 1'b1;
        dcache_rtrn_o.rtype    = serpent_cache_pkg::DCACHE_ATOMIC_ACK;
        dcache_rtrn_o.tid      = axi_rd_id_out>>3;
        dcache_rtrn_o.nc       = axi_rd_id_out[0];
      end  
      IFILL: begin 
        icache_rtrn_vld_o      = 1'b1;
        icache_rtrn_o.rtype    = serpent_cache_pkg::ICACHE_IFILL_ACK;
        icache_rtrn_o.tid      = axi_rd_id_out>>3;
        icache_rtrn_o.nc       = axi_rd_id_out[0];
        icache_rtrn_o.f4b      = axi_rd_id_out[0];
      end  
    endcase
  //////////////////////////////////////  
  end else if (axi_wr_valid) begin
    dcache_rtrn_vld_o  = 1'b1; 
    dcache_rtrn_o.tid  = axi_wr_id_out>>3;
    dcache_rtrn_o.nc   = axi_wr_id_out[0];
    unique case(tx_t'(axi_wr_id_out[2:1]))
      STD:   dcache_rtrn_o.rtype = serpent_cache_pkg::DCACHE_STORE_ACK;
      ATOP:  dcache_rtrn_vld_o   = 1'b0; // silently drop atop write response, as we only rely on the read response here
      LRSC:  begin 
        dcache_rtrn_o.rtype = serpent_cache_pkg::DCACHE_ATOMIC_ACK;
        // encode success 
        dcache_rtrn_o.data[63:0] = (axi_wr_exokay) ? '0 : '1;
      end
      default: dcache_rtrn_vld_o   = 1'b0;
    endcase
  end
  //////////////////////////////////////
end


// invalidations are not supported at the moment as this would require a snoop filter (AXI ACE...)
// note that the atomic transactions would also need a master exclusive monitor in that case
// assign icache_rtrn_o.inv.idx  = '0;
// assign icache_rtrn_o.inv.way  = '0;
// assign icache_rtrn_o.inv.vld  = '0;
// assign icache_rtrn_o.inv.all  = '0;

// assign dcache_rtrn_o.inv.idx  = '0;
// assign dcache_rtrn_o.inv.way  = '0;
// assign dcache_rtrn_o.inv.vld  = '0;
// assign dcache_rtrn_o.inv.all  = '0;



///////////////////////////////////////////////////////
// axi adapter
///////////////////////////////////////////////////////

axi_adapter2 #(
  .DATA_WORDS      ( AxiNumWords     ),
  .AXI_ID_WIDTH    ( AxiIdWidth      )
) i_axi_adapter (
  .clk_i           ( clk_i             ),
  .rst_ni          ( rst_ni            ),
  .rd_req_i        ( axi_rd_req        ),
  .rd_gnt_o        ( axi_rd_gnt        ),
  .rd_addr_i       ( axi_rd_addr       ),
  .rd_blen_i       ( axi_rd_blen       ),
  .rd_size_i       ( axi_rd_size       ),
  .rd_id_i         ( axi_rd_id_in      ),
  .rd_rdy_i        ( axi_rd_rdy        ),
  .rd_lock_i       ( axi_rd_lock       ),
  .rd_valid_o      ( axi_rd_valid      ),
  .rd_data_o       ( axi_rd_data       ),
  .rd_id_o         ( axi_rd_id_out     ),
  .rd_exokay_o     ( axi_rd_exokay     ),    
  .wr_req_i        ( axi_wr_req        ),
  .wr_gnt_o        ( axi_wr_gnt        ),
  .wr_addr_i       ( axi_wr_addr       ),
  .wr_data_i       ( axi_wr_data       ),
  .wr_be_i         ( axi_wr_be         ),
  .wr_blen_i       ( axi_wr_blen       ),
  .wr_size_i       ( axi_wr_size       ),
  .wr_id_i         ( axi_wr_id_in      ),
  .wr_lock_i       ( axi_wr_lock       ),
  .wr_atop_i       ( axi_wr_atop       ),
  .wr_rdy_i        ( axi_wr_rdy        ),
  .wr_valid_o      ( axi_wr_valid      ),
  .wr_id_o         ( axi_wr_id_out     ),
  .wr_exokay_o     ( axi_wr_exokay     ),
  .axi_req_o       ( axi_req_o         ),
  .axi_resp_i      ( axi_resp_i        )
);

///////////////////////////////////////////////////////
// assertions
///////////////////////////////////////////////////////

//pragma translate_off
`ifndef VERILATOR
  initial begin
    assert (AxiIdWidth >= $clog2(serpent_cache_pkg::DCACHE_MAX_TX)+3) else
      $fatal(1,$psprintf("[axi adapter] AXI ID must be at least %01d bit wide", $clog2(serpent_cache_pkg::DCACHE_MAX_TX)+3));
    assert (ariane_pkg::ICACHE_LINE_WIDTH <= ariane_pkg::DCACHE_LINE_WIDTH) else 
      $fatal(1,"[axi adapter] AXI shim currently assumes that the icache line size >= dcache line size");
  end

  lr_exokay: assert property (
  @(posedge clk_i) disable iff (~rst_ni) axi_rd_valid |-> axi_rd_rdy |-> tx_t'(axi_rd_id_out[2:1]) == LRSC |-> axi_rd_exokay)
    else $warning("[axi adapter] LR did not receive an exokay, indicating that atomics are not supported");
  
`endif
//pragma translate_on

endmodule // serpent_l15_adapter
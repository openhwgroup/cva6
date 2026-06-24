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
// Author: Florian Zaruba, ETH Zurich
// Date: 22.05.2017
// Description: Store Unit, takes care of all store requests and atomic memory operations (AMOs)


module store_unit
  import ariane_pkg::*;
#(
    parameter config_pkg::cva6_cfg_t CVA6Cfg = config_pkg::cva6_cfg_empty,
    parameter type dcache_req_i_t = logic,
    parameter type dcache_req_o_t = logic,
    parameter type exception_t = logic,
    parameter type lsu_ctrl_t = logic,
    parameter type cbo_t = logic
) (
    // Subsystem Clock - SUBSYSTEM
    input logic clk_i,
    // Asynchronous reset active low - SUBSYSTEM
    input logic rst_ni,
    // Flush - CONTROLLER
    input logic flush_i,
    // TO_BE_COMPLETED - TO_BE_COMPLETED
    input logic stall_st_pending_i,
    // TO_BE_COMPLETED - TO_BE_COMPLETED
    output logic no_st_pending_o,
    // Store buffer is empty - TO_BE_COMPLETED
    output logic store_buffer_empty_o,
    // Store instruction is valid - ISSUE_STAGE
    input logic valid_i,
    // Data input - ISSUE_STAGE
    input lsu_ctrl_t lsu_ctrl_i,
    // TO_BE_COMPLETED - TO_BE_COMPLETED
    output logic pop_st_o,
    // Instruction commit - TO_BE_COMPLETED
    input logic commit_i,
    // TO_BE_COMPLETED - TO_BE_COMPLETED
    output logic commit_ready_o,
    // TO_BE_COMPLETED - TO_BE_COMPLETED
    input logic amo_valid_commit_i,
    // Data Endian mode - CSR_REGFILE
    input logic mbe_i,
    // Store result is valid - ISSUE_STAGE
    output logic valid_o,
    // Transaction ID - ISSUE_STAGE
    output logic [CVA6Cfg.TRANS_ID_BITS-1:0] trans_id_o,
    // Store result - ISSUE_STAGE
    output logic [CVA6Cfg.XLEN-1:0] result_o,
    // Store exception output - TO_BE_COMPLETED
    output exception_t ex_o,
    // Address translation request - TO_BE_COMPLETED
    output logic translation_req_o,
    // Virtual address - TO_BE_COMPLETED
    output logic [CVA6Cfg.VLEN-1:0] vaddr_o,
    // RVFI information - RVFI
    output logic [CVA6Cfg.PLEN-1:0] rvfi_mem_paddr_o,
    // Transformed trap instruction out - TO_BE_COMPLETED
    output logic [31:0] tinst_o,
    // TO_BE_COMPLETED - TO_BE_COMPLETED
    output logic hs_ld_st_inst_o,
    // TO_BE_COMPLETED - TO_BE_COMPLETED
    output logic hlvx_inst_o,
    // Physical address - TO_BE_COMPLETED
    input logic [CVA6Cfg.PLEN-1:0] paddr_i,
    // Exception raised before store - TO_BE_COMPLETED
    input exception_t ex_i,
    // Data TLB hit - lsu
    input logic dtlb_hit_i,
    // Physical memory attributes - MMU
    input logic dtlb_pbmt_i,
    // Physical address of PTE for A-bit - MMU
    input logic [CVA6Cfg.PLEN-1:0] accessed_req_paddr_i,
    // PTE A-bit update valid - MMU
    input logic accessed_req_valid_i,
    // A-bit update queue full - MMU
    output logic accessed_queue_full_o,
    // Physical address of PTE for D-bit - MMU
    input logic [CVA6Cfg.PLEN-1:0] dirty_req_pte_paddr_i,
    // PTE D-bit fault - MMU
    input logic dirty_bit_fault_valid_i,
    // Virtual address of the request that caused D-bit fault - MMU
    input logic [CVA6Cfg.VLEN-1:0] dirty_req_vaddr_i,
    // VMID of the request that caused D-bit fault - MMU
    input logic [CVA6Cfg.VMID_WIDTH-1:0] dirty_req_vmid_i,
    // ASID of the request that caused D-bit fault - MMU
    input logic [CVA6Cfg.ASID_WIDTH-1:0] dirty_req_asid_i,
    // DTLB ready for PTE synchronization - MMU
    input logic dirty_req_tlb_ready_i,
    // DTLB sync valid - MMU
    input logic dirty_req_tlb_sync_i,
    // DTLB sync ACK - MMU
    output logic dirty_req_tlb_sync_o,
    // Virtual address of DTLB sync request - MMU
    output logic [CVA6Cfg.XLEN-1:0] dirty_req_tlb_vaddr_o,
    // VMID of DTLB sync request - MMU
    output logic [CVA6Cfg.VMID_WIDTH-1:0] dirty_req_tlb_vmid_o,
    // ASID of DTLB sync request - MMU
    output logic [CVA6Cfg.ASID_WIDTH-1:0] dirty_req_tlb_asid_o,

    // Address to be checked - load_unit
    input logic [11:0] page_offset_i,
    // Address check result - load_unit
    output logic page_offset_matches_o,
    // AMO request - CACHES
    output amo_req_t amo_req_o,
    // AMO response - CACHES
    input amo_resp_t amo_resp_i,
    // AMO commit - COMMIT STAGE
    output amo_resp_t amo_commit_o,
    // Data cache request - CACHES
    input dcache_req_o_t req_port_i,
    // Data cache response - CACHES
    output dcache_req_i_t req_port_o
);

  // align data to address e.g.: shift data to be naturally 64
  function automatic [CVA6Cfg.XLEN-1:0] data_align(logic [2:0] addr, logic [63:0] data);
    // Set addr[2] to 1'b0 when 32bits
    logic [ 2:0] addr_tmp = {(addr[2] && CVA6Cfg.IS_XLEN64), addr[1:0]};
    logic [63:0] data_tmp = {64{1'b0}};
    case (addr_tmp)
      3'b000: data_tmp[CVA6Cfg.XLEN-1:0] = {data[CVA6Cfg.XLEN-1:0]};
      3'b001:
      data_tmp[CVA6Cfg.XLEN-1:0] = {data[CVA6Cfg.XLEN-9:0], data[CVA6Cfg.XLEN-1:CVA6Cfg.XLEN-8]};
      3'b010:
      data_tmp[CVA6Cfg.XLEN-1:0] = {data[CVA6Cfg.XLEN-17:0], data[CVA6Cfg.XLEN-1:CVA6Cfg.XLEN-16]};
      3'b011:
      data_tmp[CVA6Cfg.XLEN-1:0] = {data[CVA6Cfg.XLEN-25:0], data[CVA6Cfg.XLEN-1:CVA6Cfg.XLEN-24]};
      default:
      if (CVA6Cfg.IS_XLEN64) begin
        case (addr_tmp)
          3'b100:  data_tmp = {data[31:0], data[63:32]};
          3'b101:  data_tmp = {data[23:0], data[63:24]};
          3'b110:  data_tmp = {data[15:0], data[63:16]};
          3'b111:  data_tmp = {data[7:0], data[63:8]};
          default: data_tmp = {data[63:0]};
        endcase
      end
    endcase
    return data_tmp[CVA6Cfg.XLEN-1:0];
  endfunction

  // it doesn't matter what we are writing back as stores don't return anything
  assign result_o = lsu_ctrl_i.data;

  enum logic [1:0] {
    IDLE,
    VALID_STORE,
    WAIT_TRANSLATION,
    WAIT_STORE_READY
  }
      state_d, state_q;

  // store buffer control signals
  logic st_ready;
  logic st_valid;
  logic st_valid_without_flush;
  logic instr_is_amo;
  assign instr_is_amo = is_amo(lsu_ctrl_i.operation);
  // keep the data and the byte enable for the second cycle (after address translation)
  logic [CVA6Cfg.XLEN-1:0] st_data_n, st_data_q;
  logic [(CVA6Cfg.XLEN/8)-1:0] st_be_n, st_be_q;
  logic [1:0] st_data_size_n, st_data_size_q;
  amo_t amo_op_d, amo_op_q;
  cbo_t cbo_op_d, cbo_op_q;

  logic [CVA6Cfg.TRANS_ID_BITS-1:0] trans_id_n, trans_id_q;

  logic dirty_req_valid;
  logic dirty_bit_fault_d, dirty_bit_fault_q;

  // output assignments
  assign vaddr_o         = lsu_ctrl_i.vaddr;  // virtual address
  assign hs_ld_st_inst_o = CVA6Cfg.RVH ? lsu_ctrl_i.hs_ld_st_inst : 1'b0;
  assign hlvx_inst_o     = CVA6Cfg.RVH ? lsu_ctrl_i.hlvx_inst : 1'b0;
  assign tinst_o         = CVA6Cfg.RVH ? lsu_ctrl_i.tinst : '0;  // transformed instruction
  assign trans_id_o      = trans_id_q;  // transaction id from previous cycle

  always_comb begin : store_control
    translation_req_o      = 1'b0;
    valid_o                = 1'b0;
    st_valid               = 1'b0;
    st_valid_without_flush = 1'b0;
    pop_st_o               = 1'b0;
    ex_o                   = ex_i;
    trans_id_n             = lsu_ctrl_i.trans_id;
    state_d                = state_q;
    
    dirty_bit_fault_d = dirty_bit_fault_q;
    dirty_req_valid = 1'b0;

    case (state_q)
      // we got a valid store
      IDLE: begin
        if (valid_i) begin
          state_d = VALID_STORE;
          translation_req_o = 1'b1;
          pop_st_o = 1'b1;
          
          dirty_bit_fault_d = dirty_bit_fault_valid_i;

          // check if translation was valid and we have space in the store buffer
          // otherwise simply stall
          if (CVA6Cfg.MmuPresent && !dtlb_hit_i) begin
            state_d  = WAIT_TRANSLATION;
            pop_st_o = 1'b0;
          end

          if (!st_ready || (CVA6Cfg.SvaduEn && dirty_bit_fault_valid_i && dirty_queue_full_o)) begin
            state_d  = WAIT_STORE_READY;
            pop_st_o = 1'b0;
          end
        end
      end

      VALID_STORE: begin
        valid_o = 1'b1;
        // post this store to the store buffer if we are not flushing
        if (!flush_i) begin
          st_valid = 1'b1;
          if (CVA6Cfg.SvaduEn && dirty_bit_fault_q && !dirty_queue_full_o) begin
            dirty_bit_fault_d = 1'b0;
            dirty_req_valid = 1'b1;
          end
        end

        st_valid_without_flush = 1'b1;

        // we have another request and its not an AMO (the AMO buffer only has depth 1)
        if ((valid_i && CVA6Cfg.RVA && !instr_is_amo) || (valid_i && !CVA6Cfg.RVA)) begin

          translation_req_o = 1'b1;
          state_d = VALID_STORE;
          pop_st_o = 1'b1;

          if (CVA6Cfg.MmuPresent && !dtlb_hit_i) begin
            state_d  = WAIT_TRANSLATION;
            pop_st_o = 1'b0;
          end

          if (!st_ready) begin
            state_d  = WAIT_STORE_READY;
            pop_st_o = 1'b0;
          end

          if (CVA6Cfg.SvaduEn && dirty_queue_full_o && dirty_bit_fault_valid_i) begin
            state_d = WAIT_STORE_READY;
            pop_st_o = 1'b0;
          end
          // if we do not have another request go back to idle
        end else begin
          state_d = IDLE;
        end
      end

      // the store queue is currently full
      WAIT_STORE_READY: begin
        // keep the translation request high
        translation_req_o = 1'b1;

        if (st_ready && dtlb_hit_i && !dirty_queue_full_o) begin
          state_d = IDLE;
        end
      end

      default: begin
        // we didn't receive a valid translation, wait for one
        // but we know that the store queue is not full as we could only have landed here if
        // it wasn't full
        if (state_q == WAIT_TRANSLATION && CVA6Cfg.MmuPresent) begin
          translation_req_o = 1'b1;

          if (dtlb_hit_i) begin
            state_d = IDLE;
          end
        end
      end
    endcase

    // -----------------
    // Access Exception
    // -----------------
    // we got an address translation exception (access rights, misaligned or page fault)
    if (ex_i.valid && (state_q != IDLE)) begin
      // the only difference is that we do not want to store this request
      pop_st_o = 1'b1;
      st_valid = 1'b0;
      state_d  = IDLE;
      valid_o  = 1'b1;
      dirty_req_valid = 1'b0;
    end

    if (flush_i) state_d = IDLE;
  end

  // -------------
  // Byte-Swapper
  // -------------
  // We need to reverse the byte order of what we intend to Store in Data Memory if we are in Big Endian Mode (mbe defines endianness and comes from CSRregfile).
  logic [CVA6Cfg.XLEN-1:0] endian_data;

  always_comb begin
    endian_data = lsu_ctrl_i.data;
    if (mbe_i) begin
      case (lsu_ctrl_i.operation)
        SB, HSV_B, FSB: endian_data[7:0] = {lsu_ctrl_i.data[7:0]};
        SH, HSV_H, FSH: endian_data[15:0] = {<<8{lsu_ctrl_i.data[15:0]}};
        SW, HSV_W, FSW, AMO_LRW, AMO_SCW, AMO_SWAPW, AMO_ADDW, AMO_ANDW, AMO_ORW, AMO_XORW, AMO_MAXW,
        AMO_MINW, AMO_MAXWU, AMO_MINWU:
        endian_data[31:0] = {<<8{lsu_ctrl_i.data[31:0]}};
        default: endian_data[CVA6Cfg.XLEN-1:0] = {<<8{lsu_ctrl_i.data[CVA6Cfg.XLEN-1:0]}};
      endcase
    end
  end

  // -----------
  // Re-aligner
  // -----------
  // re-align the write data to comply with the address offset
  always_comb begin
    st_be_n = lsu_ctrl_i.be;
    // don't shift the data if we are going to perform an AMO as we still need to operate on this data
    st_data_n = ((CVA6Cfg.RVA && instr_is_amo) ? endian_data[CVA6Cfg.XLEN-1:0] :
                 data_align(lsu_ctrl_i.vaddr[2:0], {{64 - CVA6Cfg.XLEN{1'b0}}, endian_data}));
    st_data_size_n = extract_transfer_size(lsu_ctrl_i.operation);
    // save AMO op for next cycle
    if (CVA6Cfg.RVA) begin
      case (lsu_ctrl_i.operation)
        AMO_LRW, AMO_LRD:     amo_op_d = AMO_LR;
        AMO_SCW, AMO_SCD:     amo_op_d = AMO_SC;
        AMO_SWAPW, AMO_SWAPD: amo_op_d = AMO_SWAP;
        AMO_ADDW, AMO_ADDD:   amo_op_d = AMO_ADD;
        AMO_ANDW, AMO_ANDD:   amo_op_d = AMO_AND;
        AMO_ORW, AMO_ORD:     amo_op_d = AMO_OR;
        AMO_XORW, AMO_XORD:   amo_op_d = AMO_XOR;
        AMO_MAXW, AMO_MAXD:   amo_op_d = AMO_MAX;
        AMO_MAXWU, AMO_MAXDU: amo_op_d = AMO_MAXU;
        AMO_MINW, AMO_MIND:   amo_op_d = AMO_MIN;
        AMO_MINWU, AMO_MINDU: amo_op_d = AMO_MINU;
        default:              amo_op_d = AMO_NONE;
      endcase
    end else begin
      amo_op_d = AMO_NONE;
    end

    if (CVA6Cfg.RVZiCbom) begin
      case (lsu_ctrl_i.operation)
        ariane_pkg::CBO_INVAL: cbo_op_d = ariane_pkg::CBO_INVAL;
        ariane_pkg::CBO_CLEAN: cbo_op_d = ariane_pkg::CBO_CLEAN;
        ariane_pkg::CBO_FLUSH: cbo_op_d = ariane_pkg::CBO_FLUSH;
        default:               cbo_op_d = ariane_pkg::CBO_NONE;
      endcase
    end else begin
      cbo_op_d = ariane_pkg::CBO_NONE;
    end
  end

  logic store_buffer_valid, amo_buffer_valid;
  logic store_buffer_ready, amo_buffer_ready;

  logic [CVA6Cfg.PLEN-1:0] store_buffer_pue_paddr, amo_buffer_pue_paddr, pue_commit_paddr;
  logic store_buffer_pue_commit, amo_buffer_pue_commit, pue_commit_valid;
  logic dirty_queue_full_o;

  // multiplex between store unit and amo buffer
  assign store_buffer_valid = st_valid & (!CVA6Cfg.RVA || (amo_op_q == AMO_NONE));
  assign amo_buffer_valid = st_valid & (CVA6Cfg.RVA && (amo_op_q != AMO_NONE));

  assign st_ready = store_buffer_ready & amo_buffer_ready;

  // ---------------
  // Store Queue
  // ---------------
  store_buffer #(
      .CVA6Cfg       (CVA6Cfg),
      .dcache_req_i_t(dcache_req_i_t),
      .dcache_req_o_t(dcache_req_o_t),
      .cbo_t         (cbo_t)
  ) store_buffer_i (
      .clk_i,
      .rst_ni,
      .flush_i,
      .stall_st_pending_i,
      .no_st_pending_o,
      .store_buffer_empty_o,
      .page_offset_i,
      .page_offset_matches_o,
      .commit_i,
      .commit_ready_o,
      .ready_o              (store_buffer_ready),
      .valid_i              (store_buffer_valid),
      // the flush signal can be critical and we need this valid
      // signal to check whether the page_offset matches or not,
      // functionally it doesn't make a difference whether we use
      // the correct valid signal or not as we are flushing
      // the whole pipeline anyway
      .valid_without_flush_i(st_valid_without_flush),
      .paddr_i,
      .rvfi_mem_paddr_o     (rvfi_mem_paddr_o),
      .data_i               (st_data_q),
      .cbo_op_i             (cbo_op_q),
      .st_pbmt_i            (dtlb_pbmt_i),
      .be_i                 (st_be_q),
      .data_size_i          (st_data_size_q),
      .pue_commit_valid_o   (store_buffer_pue_commit),
      .pue_commit_paddr_o   (store_buffer_pue_paddr),
      .req_port_i           (req_port_i),
      .req_port_o           (req_port_o)
  );

  if (CVA6Cfg.RVA && !CVA6Cfg.SvaduEn) begin
    amo_buffer #(
        .CVA6Cfg(CVA6Cfg)
    ) i_amo_buffer (
        .clk_i,
        .rst_ni,
        .flush_i,
        .valid_i           (amo_buffer_valid),
        .ready_o           (amo_buffer_ready),
        .paddr_i           (paddr_i),
        .amo_op_i          (amo_op_q),
        .data_i            (st_data_q),
        .data_size_i       (st_data_size_q),
        .amo_pbmt_i        (dtlb_pbmt_i),
        .amo_req_o         (amo_req_o),
        .amo_resp_i        (amo_resp_i),
        .pue_commit_valid_o(amo_buffer_pue_commit),
        .pue_commit_paddr_o(amo_buffer_pue_paddr),
        .amo_valid_commit_i(amo_valid_commit_i),
        .no_st_pending_i   (no_st_pending_o)
    );
    
    assign amo_commit_o = amo_resp_i;

  end else if (CVA6Cfg.RVA && CVA6Cfg.SvaduEn) begin

      // Shared AMO port arbitration 
      amo_req_t  shared_amo_req_o [1:0];
      amo_resp_t shared_amo_resp_i [1:0];
      logic bus_owner, bus_busy;

      amo_buffer #(
          .CVA6Cfg(CVA6Cfg)
      ) i_amo_buffer (
          .clk_i,
          .rst_ni,
          .flush_i,
          .valid_i           (amo_buffer_valid),
          .ready_o           (amo_buffer_ready),
          .paddr_i           (paddr_i),
          .amo_op_i          (amo_op_q),
          .data_i            (st_data_q),
          .data_size_i       (st_data_size_q),
          .amo_pbmt_i        (dtlb_pbmt_i),
          .amo_req_o         (shared_amo_req_o[0]),
          .amo_resp_i        (shared_amo_resp_i[0]),
          .pue_commit_valid_o(amo_buffer_pue_commit),
          .pue_commit_paddr_o(amo_buffer_pue_paddr),
          .amo_valid_commit_i(amo_valid_commit_i),
          .no_st_pending_i   (no_st_pending_o)
      );

      pte_update_unit #(
        .CVA6Cfg(CVA6Cfg),
        .DEPTH(8)
      ) i_cva6_pue (
        .clk_i,
        .rst_ni,
        .pipeline_flush_i      (flush_i),

        .accessed_req_pte_paddr_i  (accessed_req_paddr_i),
        .accessed_req_valid_i      (accessed_req_valid_i),
        .accessed_queue_full_o     (accessed_queue_full_o),
        
        .dirty_req_pte_paddr_i (dirty_req_pte_paddr_i),
        .dirty_req_paddr_i     (paddr_i),
        .dirty_req_vaddr_i     (dirty_req_vaddr_i),
        .dirty_req_asid_i      (dirty_req_asid_i),
        .dirty_req_vmid_i      (dirty_req_vmid_i),
        .dirty_req_valid_i     (dirty_req_valid),
        .dirty_queue_full_o    (dirty_queue_full_o),

        .dirty_req_tlb_sync_i  (dirty_req_tlb_sync_i),
        .dirty_req_tlb_ready_i (dirty_req_tlb_ready_i),

        .dirty_req_tlb_sync_o  (dirty_req_tlb_sync_o),
        .dirty_req_tlb_vaddr_o (dirty_req_tlb_vaddr_o),
        .dirty_req_tlb_asid_o  (dirty_req_tlb_asid_o),
        .dirty_req_tlb_vmid_o  (dirty_req_tlb_vmid_o),

        .commit_valid_i        (pue_commit_valid),
        .commit_paddr_i        (pue_commit_paddr),

        .amo_req_o             (shared_amo_req_o[1]),
        .amo_resp_i            (shared_amo_resp_i[1])
      );

      always_ff@(posedge clk_i or negedge rst_ni) begin
        if(!rst_ni) begin
          bus_owner <= 0;
          bus_busy  <= 0;
        end else begin
          if(amo_resp_i.ack) begin
            bus_busy  <= 0;
            bus_owner <= 0;
          end else if(shared_amo_req_o[0].req && !bus_busy) begin
            bus_busy  <= 1;
            bus_owner <= 0;
          end else if(shared_amo_req_o[1].req && !bus_busy) begin
            bus_busy  <= 1;
            bus_owner <= 1;
          end
        end
      end

      assign amo_req_o            = (bus_owner) ? shared_amo_req_o[1] : shared_amo_req_o[0];
      assign shared_amo_resp_i[0] = (bus_busy && !bus_owner) ? amo_resp_i : '0;
      assign shared_amo_resp_i[1] = (bus_busy && bus_owner)  ? amo_resp_i : '0;

      assign amo_commit_o         = shared_amo_resp_i[0];

      assign pue_commit_valid = amo_buffer_pue_commit || store_buffer_pue_commit;
      assign pue_commit_paddr = (amo_buffer_pue_commit) ? amo_buffer_pue_paddr : 
                                  ((store_buffer_pue_commit) ? store_buffer_pue_paddr : '0); 

  end else begin
    assign amo_buffer_ready = 1'b1;
    assign amo_req_o        = '0;

    assign amo_commit_o     = 1'b0;

    assign pue_commit_valid = 1'b0;
    assign pue_commit_paddr = '0;
  end

  // ---------------
  // Registers
  // ---------------
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (~rst_ni) begin
      state_q           <= IDLE;
      st_be_q           <= '0;
      st_data_q         <= '0;
      st_data_size_q    <= '0;
      trans_id_q        <= '0;
      amo_op_q          <= AMO_NONE;
      cbo_op_q          <= ariane_pkg::CBO_NONE;
      dirty_bit_fault_q <= '0;
    end else begin
      state_q           <= state_d;
      st_be_q           <= st_be_n;
      st_data_q         <= st_data_n;
      trans_id_q        <= trans_id_n;
      st_data_size_q    <= st_data_size_n;
      amo_op_q          <= amo_op_d;
      cbo_op_q          <= cbo_op_d;
      dirty_bit_fault_q <= dirty_bit_fault_d;
    end
  end

endmodule

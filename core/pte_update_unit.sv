// seongwon

module pte_update_unit #(
    parameter config_pkg::cva6_cfg_t CVA6Cfg = config_pkg::cva6_cfg_empty,
    parameter integer DEPTH = 4
)(
    input logic clk_i,     // Clock
    input logic rst_ni,    // Asynchronous reset active low
    input logic pipeline_flush_i,

    // PTW unit - Accessed-bit Update Request
    input logic [CVA6Cfg.PLEN-1:0] accessed_req_pte_paddr_i,    // PAddr of PTE for Accessed-bit update
    input logic accessed_req_valid_i,                       // Valid for generation of Accessed-bit update
    output logic accessed_queue_full_o,                     // Accessed-queue full

    // DTLB - Dirty-bit Update Request
    input logic [CVA6Cfg.PLEN-1:0] dirty_req_pte_paddr_i,   // PAddr of PTE for Dirty-bit update
    input logic [CVA6Cfg.PLEN-1:0] dirty_req_paddr_i,       // PAddr of Req for tracking committable request
    input logic [CVA6Cfg.VLEN-1:0] dirty_req_vaddr_i,       // VAddr of Req for synchronizing DTLB 
    input logic [CVA6Cfg.ASID_WIDTH-1:0] dirty_req_asid_i,  // ASID of Req for synchronizng DTLB
    input logic [CVA6Cfg.VMID_WIDTH-1:0] dirty_req_vmid_i,  // VMID of Req for synchronizing DTLB
    input logic dirty_req_valid_i,                          // Valid for generation of Dirty-bit update
    output logic dirty_queue_full_o,                        // Dirty-queue full

    // DTLB - synchronization response
    input logic dirty_req_tlb_sync_i,                       // ACK (Valid) for synchronizing DTLB
    input logic dirty_req_tlb_ready_i,                      // Ready from DTLB and STLB for synchronizing DTLB

    // DTLB - synchronization request
    output logic dirty_req_tlb_sync_o,                      // Valid for synchronizing DTLB
    output logic [CVA6Cfg.VLEN-1:0] dirty_req_tlb_vaddr_o,      // VAddr of Req for synchronizing DTLB
    output logic [CVA6Cfg.ASID_WIDTH-1:0] dirty_req_tlb_asid_o, // ASID of Req for synchronizing DTLB
    output logic [CVA6Cfg.VMID_WIDTH-1:0] dirty_req_tlb_vmid_o, // VMID of Req for synchronizing DTLB

    // Tracking non-speculative request - store/AMO buffer
    input logic commit_valid_i,                                 // Valid for committable dirty-bit update
    input logic [CVA6Cfg.PLEN-1:0] commit_paddr_i,              // PAddr of committable request for committable dirty-bit update

    // AMO request - CACHES
    input ariane_pkg::amo_resp_t amo_resp_i,                
    // AMO response - CACHES
    output ariane_pkg::amo_req_t amo_req_o
);


  typedef struct packed {
    ariane_pkg::amo_t        op;
    logic [CVA6Cfg.PLEN-1:0] pte_paddr;
    logic [CVA6Cfg.XLEN-1:0] data;
    logic [1:0]              size;
  } amo_op_t;

  typedef struct packed {
    amo_op_t amo_req;
    logic valid;
  } accessed_queue_entry_t;

  typedef struct packed {
    amo_op_t amo_req;
    logic valid;

    logic [CVA6Cfg.PLEN-1:0] paddr;
    logic [CVA6Cfg.VLEN-1:0] vaddr;
    logic [CVA6Cfg.ASID_WIDTH-1:0] asid;
    logic [CVA6Cfg.VMID_WIDTH-1:0] vmid;
    logic committable;
  } dirty_queue_entry_t;



  localparam int PTE_A_BIT = 6;
  localparam int PTE_D_BIT = 7;
  localparam logic [CVA6Cfg.XLEN-1:0] ACCESSED_UPDATE_MASK  = ({{CVA6Cfg.XLEN-1{1'b0}}, 1'b1} << PTE_A_BIT);
  localparam logic [CVA6Cfg.XLEN-1:0] DIRTY_UPDATE_MASK     = ({{CVA6Cfg.XLEN-1{1'b0}}, 1'b1} << PTE_D_BIT);

  localparam logic [1:0] PUE_SIZE_MASK = (CVA6Cfg.XLEN == 64) ? 2'b11 : 2'b10;
  

  accessed_queue_entry_t [DEPTH-1:0] accessed_queue_d, accessed_queue_q;
  dirty_queue_entry_t    [DEPTH-1:0] dirty_queue_d, dirty_queue_q;
  
  logic [$clog2(DEPTH)-1:0] accessed_queue_read_pointer_d, accessed_queue_read_pointer_q; 
  logic [$clog2(DEPTH)-1:0] accessed_queue_write_pointer_d, accessed_queue_write_pointer_q; 
  logic [$clog2(DEPTH)  :0] accessed_queue_status_d, accessed_queue_status_q;


  logic [$clog2(DEPTH)-1:0] dirty_queue_read_pointer_d, dirty_queue_read_pointer_q; 
  logic [$clog2(DEPTH)-1:0] dirty_queue_write_pointer_d, dirty_queue_write_pointer_q;
  logic [$clog2(DEPTH) : 0] dirty_queue_entry_status_d, dirty_queue_entry_status_q;

  logic [$clog2(DEPTH)-1:0] dirty_queue_commit_pointer_d, dirty_queue_commit_pointer_q;
  logic [$clog2(DEPTH) : 0] dirty_queue_commit_status_d, dirty_queue_commit_status_q;

  typedef enum logic[1:0] { 
    IDLE,
    D_BIT_TLB_SYNC,
    D_BIT_AMO_SEND,
    A_BIT_AMO_SEND
  } pue_state_t;
  
  pue_state_t pue_state_d, pue_state_q;

  // PUE QUEUE MANAGEMENT
  always_comb begin  : PUEQueueManagement
    amo_req_o   = '0;
    pue_state_d = pue_state_q;
    // Enqueue process 
    accessed_queue_d               = accessed_queue_q;
    dirty_queue_d                  = dirty_queue_q;

    accessed_queue_read_pointer_d  = accessed_queue_read_pointer_q;
    accessed_queue_write_pointer_d = accessed_queue_write_pointer_q;
    accessed_queue_status_d        = accessed_queue_status_q;

    dirty_queue_read_pointer_d     = dirty_queue_read_pointer_q;
    dirty_queue_write_pointer_d    = dirty_queue_write_pointer_q;
    dirty_queue_entry_status_d     = dirty_queue_entry_status_q;

    dirty_queue_commit_pointer_d = dirty_queue_commit_pointer_q;
    dirty_queue_commit_status_d  = dirty_queue_commit_status_q;

    // DTLB-side
    dirty_req_tlb_sync_o = 1'b0;
    dirty_req_tlb_vaddr_o = '0;
    dirty_req_tlb_vmid_o = '0;
    dirty_req_tlb_asid_o  = '0;

    if(accessed_req_valid_i && !accessed_queue_full_o) begin
        accessed_queue_d[accessed_queue_write_pointer_d].amo_req.op    = ariane_pkg::AMO_OR;
        accessed_queue_d[accessed_queue_write_pointer_d].amo_req.pte_paddr = accessed_req_pte_paddr_i;
        accessed_queue_d[accessed_queue_write_pointer_d].amo_req.data  = ACCESSED_UPDATE_MASK; 
        accessed_queue_d[accessed_queue_write_pointer_d].amo_req.size  = PUE_SIZE_MASK;

        accessed_queue_d[accessed_queue_write_pointer_d].valid = 1;

        accessed_queue_write_pointer_d++;
        accessed_queue_status_d++;
    end
    if(dirty_req_valid_i && !dirty_queue_full_o) begin
        dirty_queue_d[dirty_queue_write_pointer_d].amo_req.op    = ariane_pkg::AMO_OR;
        dirty_queue_d[dirty_queue_write_pointer_d].amo_req.pte_paddr = dirty_req_pte_paddr_i;
        dirty_queue_d[dirty_queue_write_pointer_d].amo_req.data  = DIRTY_UPDATE_MASK;
        dirty_queue_d[dirty_queue_write_pointer_d].amo_req.size  = PUE_SIZE_MASK;

        dirty_queue_d[dirty_queue_write_pointer_d].paddr = dirty_req_paddr_i;
        dirty_queue_d[dirty_queue_write_pointer_d].vaddr = dirty_req_vaddr_i;
        dirty_queue_d[dirty_queue_write_pointer_d].asid = dirty_req_asid_i;
        dirty_queue_d[dirty_queue_write_pointer_d].vmid = dirty_req_vmid_i;

        dirty_queue_d[dirty_queue_write_pointer_d].valid = 1'b1;
        dirty_queue_d[dirty_queue_write_pointer_d].committable = 1'b0;

        dirty_queue_write_pointer_d++;
        dirty_queue_entry_status_d++;
//        $display("[%0t] DIRTY-QUEUE ENQUEUE", $time);
    end

    if(commit_valid_i) begin
        if(dirty_queue_q[dirty_queue_commit_pointer_d].paddr == commit_paddr_i) begin
            dirty_queue_d[dirty_queue_commit_pointer_d].committable = 1;
            dirty_queue_commit_pointer_d++;
            dirty_queue_commit_status_d++;
         //   $display("[%0t] dirty-req commit", $time);
        end
    end

    if(pipeline_flush_i) begin
        for (int unsigned i = 0; i < DEPTH; i++) begin
            if(dirty_queue_q[i].valid && !dirty_queue_q[i].committable) begin
                dirty_queue_d[i].valid = 1'b0;
                dirty_queue_entry_status_d--;
            end
        end
        dirty_queue_write_pointer_d  = dirty_queue_commit_pointer_q;
    end

    // PUE STATE FSM
    case(pue_state_q) 
        IDLE: begin
            if(dirty_queue_entry_status_q != 0 && dirty_queue_commit_status_q != 0) begin
                if(dirty_req_tlb_ready_i) begin
                    pue_state_d = D_BIT_TLB_SYNC;
                end
      //          $display("[%0t] IDLE -> D_BIT_TLB_SYNC | Drity-status: %d | Commit-status: %d", $time, dirty_queue_entry_status_q, dirty_queue_commit_status_q);
            end
            else if((accessed_queue_status_q != 0)) begin
                pue_state_d = A_BIT_AMO_SEND;
     //           $display("[%0t] IDLE -> A_BIT_AMO_SEND | Access-status: %d", $time, accessed_queue_status_q);
            end else begin
                pue_state_d = IDLE;
            end
        end 
        D_BIT_TLB_SYNC : begin
            if(dirty_queue_q[dirty_queue_read_pointer_d].committable && dirty_queue_q[dirty_queue_read_pointer_d].valid) begin
                dirty_req_tlb_sync_o    = 1'b1;
                dirty_req_tlb_vaddr_o   = dirty_queue_q[dirty_queue_read_pointer_d].vaddr;
                dirty_req_tlb_asid_o    = dirty_queue_q[dirty_queue_read_pointer_d].asid;
                dirty_req_tlb_vmid_o    = dirty_queue_q[dirty_queue_read_pointer_d].vmid;
                if(dirty_req_tlb_sync_i) begin
                    pue_state_d = D_BIT_AMO_SEND;
                    $display("[%0t] [PUE] [D_BIT_TLB_SYNC] hit, D_TLB_SYNC -> D_AMO_REQ ", $time);
                end else begin
                    pue_state_d = D_BIT_TLB_SYNC;
                    $display("[%0t] [PUE] [D_BIT_TLB_SYNC] hit, D_TLB_SYNC -> D_TLB_SYNC ", $time);
                end

            end else begin
                pue_state_d = IDLE;
                $display("[%0t] [PUE] ERROR OCCURS", $time);
            end
        end
        D_BIT_AMO_SEND : begin
            if(dirty_queue_q[dirty_queue_read_pointer_d].committable && dirty_queue_q[dirty_queue_read_pointer_d].valid) begin
                amo_req_o.req       = dirty_queue_q[dirty_queue_read_pointer_d].valid;
                amo_req_o.amo_op    = dirty_queue_q[dirty_queue_read_pointer_d].amo_req.op;
                amo_req_o.size      = dirty_queue_q[dirty_queue_read_pointer_d].amo_req.size;
                amo_req_o.operand_a = {{64 - CVA6Cfg.PLEN{1'b0}}, dirty_queue_q[dirty_queue_read_pointer_d].amo_req.pte_paddr};
                amo_req_o.operand_b = {{64 - CVA6Cfg.PLEN{1'b0}}, dirty_queue_q[dirty_queue_read_pointer_d].amo_req.data};

                if(amo_resp_i.ack) begin
                    dirty_queue_d[dirty_queue_read_pointer_d].valid = 1'b0;
                    dirty_queue_d[dirty_queue_read_pointer_d].committable = 1'b0;
                    
                    dirty_queue_read_pointer_d++;
                    dirty_queue_entry_status_d--;
                    dirty_queue_commit_status_d--;   
                    
                    pue_state_d = IDLE;       

                end else begin
                    pue_state_d = D_BIT_AMO_SEND;
                end
            end else begin
                pue_state_d = IDLE;
            end
        end
        A_BIT_AMO_SEND : begin
            if(accessed_queue_q[accessed_queue_read_pointer_d].valid) begin
                amo_req_o.req = accessed_queue_q[accessed_queue_read_pointer_d].valid;
                amo_req_o.amo_op = accessed_queue_q[accessed_queue_read_pointer_d].amo_req.op;
                amo_req_o.size = accessed_queue_q[accessed_queue_read_pointer_d].amo_req.size;
                amo_req_o.operand_a = {{64 - CVA6Cfg.PLEN{1'b0}}, accessed_queue_q[accessed_queue_read_pointer_d].amo_req.pte_paddr};
                amo_req_o.operand_b = {{64 - CVA6Cfg.PLEN{1'b0}}, accessed_queue_q[accessed_queue_read_pointer_d].amo_req.data};
                if(amo_resp_i.ack) begin
                    accessed_queue_d[accessed_queue_read_pointer_d].valid = 1'b0;
                    accessed_queue_read_pointer_d++;
                    accessed_queue_status_d--;
                    pue_state_d = IDLE;

              //      $display("[%0t] Mode Change A_BIT_AMO_SEND -> IDLE, paddr : %h | op: %b", $time, amo_req_o.operand_a, amo_req_o.amo_op);
                end else begin
                    pue_state_d = A_BIT_AMO_SEND;
             //       $display("[%0t] Mode Change A_BIT_AMO_SEND  Waiting, paddr : %h | op: %b", $time, amo_req_o.operand_a, amo_req_o.amo_op);
                end
            end else begin
                pue_state_d = IDLE;
            end
        end
    endcase
  end

  always_ff@(posedge clk_i or negedge rst_ni) begin
    

    if(!rst_ni) begin
        for(int i = 0; i < DEPTH; i++) begin
            accessed_queue_q[i] <= '0;
            dirty_queue_q[i]    <= '0;
        end

        accessed_queue_read_pointer_q   <= 0;
        accessed_queue_write_pointer_q  <= 0;
        accessed_queue_status_q         <= 0;

        dirty_queue_read_pointer_q      <= 0;
        dirty_queue_write_pointer_q     <= 0;
        dirty_queue_entry_status_q      <= 0;

        dirty_queue_commit_status_q     <= 0;
        dirty_queue_commit_pointer_q    <= 0;

        pue_state_q                     <= IDLE;
    end else begin
        accessed_queue_q                <= accessed_queue_d;
        dirty_queue_q                   <= dirty_queue_d;

        accessed_queue_read_pointer_q   <= accessed_queue_read_pointer_d;
        accessed_queue_write_pointer_q  <= accessed_queue_write_pointer_d;
        accessed_queue_status_q         <= accessed_queue_status_d;
                
        dirty_queue_read_pointer_q      <= dirty_queue_read_pointer_d;
        dirty_queue_write_pointer_q     <= dirty_queue_write_pointer_d;
        dirty_queue_entry_status_q      <= dirty_queue_entry_status_d;
                
        dirty_queue_commit_pointer_q    <= dirty_queue_commit_pointer_d;
        dirty_queue_commit_status_q     <= dirty_queue_commit_status_d;
                
        pue_state_q                     <= pue_state_d;

        if(dirty_req_valid_i && !dirty_queue_full_o) begin
            $display("[%0t] [PUE] DIRTY-QUEUE ENQUEUE | PTE-PAddr : %h | REQ-PAddr : %h | REQ-VAddr : %h | (ASID, VMID : %d, %d)", $time, dirty_req_pte_paddr_i,
                                dirty_req_paddr_i, dirty_req_vaddr_i, dirty_req_asid_i, dirty_req_vmid_i);
        end
        if(accessed_req_valid_i && !accessed_queue_full_o) begin
            $display("[%0t] [PUE] ACCESSED-QUEUE ENQUEUE | PTE-PAddr : %h", $time, accessed_req_pte_paddr_i);
        end
        if(commit_valid_i) begin
            if(dirty_queue_q[dirty_queue_commit_pointer_q].paddr == commit_paddr_i) begin
                 $display("[%0t] [PUE] DIRTY-QUEUE COMMIT | Commit-Pointer: %d | PAddr : %h", $time,dirty_queue_commit_pointer_q,  commit_paddr_i);
            end
        end
        if(pue_state_q == IDLE) begin
            if(dirty_queue_entry_status_q != 0 && dirty_queue_commit_status_q != 0) begin
                $display("[%0t] [PUE] IDLE -> D_BIT_TLB_SYNC | Dirty-status: %d | Commit-status: %d", $time, dirty_queue_entry_status_q, dirty_queue_commit_status_q);
            end
            else if((accessed_queue_status_q != 0)) begin
                $display("[%0t] [PUE] IDLE -> A_BIT_AMO_SEND | Access-status: %d", $time, accessed_queue_status_q);
            end    
        end
        if(pue_state_q == D_BIT_TLB_SYNC) begin
            if(dirty_req_tlb_sync_i) begin
                $display("[%0t] [PUE] D_BIT_TLB_SYNC -> D_BIT_AMO_SEND", $time);
            end 
        end
        if(pue_state_q == A_BIT_AMO_SEND) begin
            if(amo_resp_i.ack) $display("[%0t] [PUE] A_BIT_AMO_SEND -> IDLE | PTE-PAddr: %h ", $time, accessed_queue_q[accessed_queue_read_pointer_q].amo_req.pte_paddr);
        end
        if(pue_state_q == D_BIT_AMO_SEND) begin
            if(amo_resp_i.ack) $display("[%0t] [PUE] D_BIT_AMO_SEND -> IDLE | PTE-PAddr: %h | REQ-PAddr: %h | REQ-VAddr: %h",$time,  dirty_queue_q[dirty_queue_read_pointer_q].amo_req.pte_paddr,
                         dirty_queue_q[dirty_queue_read_pointer_q].paddr,  dirty_queue_q[dirty_queue_read_pointer_q].vaddr);
        end
    end
  end

  assign dirty_queue_full_o    = (dirty_queue_entry_status_q == DEPTH);
  assign accessed_queue_full_o = (accessed_queue_status_q == DEPTH);

// Sanity check 
  // Accessed Queue Enqueue Check
  ap_accessed_enqueue_error : assert property (
        @(posedge clk_i) disable iff (!rst_ni || pipeline_flush_i)
        (accessed_req_valid_i && !accessed_queue_full_o) |-> !accessed_queue_q[accessed_queue_write_pointer_q].valid
    ) else $fatal(0, "cva6_pue.sv : Accessed-bit Enqueue Overwrite Error!");

    // Dirty Queue Enqueue Check 
  ap_dirty_enqueue_error : assert property (
        @(posedge clk_i) disable iff (!rst_ni || pipeline_flush_i)
        (dirty_req_valid_i && !dirty_queue_full_o) |-> !dirty_queue_q[dirty_queue_write_pointer_q].valid
    ) else $fatal(0, "cva6_pue.sv : Dirty-bit Enqueue Overwrite Error!");

endmodule
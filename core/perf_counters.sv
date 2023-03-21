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
// Date: 06.10.2017
// Description: Performance counters


module perf_counters import ariane_pkg::*; #(
  parameter int unsigned                NumPorts      = 3    // number of miss ports
) ( 
  input  logic                                    clk_i,
  input  logic                                    rst_ni,
  input  logic                                    debug_mode_i, // debug mode
  // SRAM like interface
  input  logic [11:0]                             addr_i,   // read/write address (up to 6 counters possible)
  input  logic                                    we_i,     // write enable
  input  riscv::xlen_t                            data_i,   // data to write
  output riscv::xlen_t                            data_o,   // data to read
  // from commit stage
  input  scoreboard_entry_t [NR_COMMIT_PORTS-1:0] commit_instr_i,     // the instruction we want to commit
  input  logic [NR_COMMIT_PORTS-1:0]              commit_ack_i,       // acknowledge that we are indeed committing
  // from L1 caches
  input  logic                                    l1_icache_miss_i,
  input  logic                                    l1_dcache_miss_i,
  // from MMU
  input  logic                                    itlb_miss_i,
  input  logic                                    dtlb_miss_i,
  // from issue stage
  input  logic                                    sb_full_i,
  // from frontend
  input  logic                                    if_empty_i,
  // from PC Gen
  input  exception_t                              ex_i,
  input  logic                                    eret_i,
  input  bp_resolve_t                             resolved_branch_i,
  // for newly added events
  input  exception_t                              branch_exceptions_i,  //Branch exceptions->execute unit-> branch_exception_o
  input  icache_dreq_i_t                          l1_icache_access_i,
  input  dcache_req_i_t[2:0]                      l1_dcache_access_i,
  input  logic [NumPorts-1:0][DCACHE_SET_ASSOC-1:0]miss_vld_bits_i,  //For Cache eviction (3ports-LOAD,STORE,PTW)
  input  logic                                    i_tlb_flush_i,
  input  logic                                    stall_issue_i  //stall-read operands
);

  logic [63:0] generic_counter_d[6:1];
  logic [63:0] generic_counter_q[6:1];

  //internal signal to keep track of exception
  logic read_access_exception,update_access_exception;  

  logic events[6:1]; 
  //internal signal for  MUX select line input
  logic [4:0] mhpmevent_d[6:1];
  logic [4:0] mhpmevent_q[6:1];

  //Multiplexer   
   always_comb begin : Mux
        events[6:1]='{default:0}; 
 
        case(mhpmevent_q[1])
           5'b00000 : events[1] = 0;
           5'b00001 : events[1] = l1_icache_miss_i;//L1 I-Cache misses
           5'b00010 : events[1] = l1_dcache_miss_i;//L1 D-Cache misses
           5'b00011 : events[1] = itlb_miss_i;//ITLB misses
           5'b00100 : events[1] = dtlb_miss_i;//DTLB misses
           5'b00101 : for (int unsigned i = 0; i < NR_COMMIT_PORTS; i++) if (commit_ack_i[i]) events[1] = commit_instr_i[i].fu == LOAD;//Load accesses							 
           5'b00110 : for (int unsigned i = 0; i < NR_COMMIT_PORTS; i++) if (commit_ack_i[i]) events[1] = commit_instr_i[i].fu == STORE;//Store accesses
           5'b00111 : events[1] = ex_i.valid;//Exceptions
           5'b01000 : events[1] = eret_i;//Exception handler returns
           5'b01001 : for (int unsigned i = 0; i < NR_COMMIT_PORTS; i++) if (commit_ack_i[i]) events[1] = commit_instr_i[i].fu == CTRL_FLOW;//Branch instructions 
           5'b01010 : events[1] = resolved_branch_i.valid && resolved_branch_i.is_mispredict;//Branch mispredicts
           5'b01011 : events[1] = branch_exceptions_i.valid;//Branch exceptions
                   // The standard software calling convention uses register x1 to hold the return address on a call
                   // the unconditional jump is decoded as ADD op
           5'b01100 : for (int unsigned i = 0; i < NR_COMMIT_PORTS; i++) if (commit_ack_i[i]) events[1] = commit_instr_i[i].fu == CTRL_FLOW && (commit_instr_i[i].op == ADD || commit_instr_i[i].op == JALR) && (commit_instr_i[i].rd == 'd1 || commit_instr_i[i].rd == 'd5);//Call
           5'b01101 : for (int unsigned i = 0; i < NR_COMMIT_PORTS; i++) if (commit_ack_i[i]) events[1] = commit_instr_i[i].op == JALR && commit_instr_i[i].rd == 'd0;//Return
           5'b01110 : events[1] = sb_full_i;//MSB Full
           5'b01111 : events[1] = if_empty_i;//Instruction fetch Empty
           5'b10000 : events[1] = l1_icache_access_i.req;//L1 I-Cache accesses
           5'b10001 : events[1] = l1_dcache_access_i[0].data_req || l1_dcache_access_i[1].data_req || l1_dcache_access_i[2].data_req;//L1 D-Cache accesses
           5'b10010 : events[1] = (l1_dcache_miss_i && miss_vld_bits_i[0] == 8'hFF) || (l1_dcache_miss_i && miss_vld_bits_i[1] == 8'hFF) || (l1_dcache_miss_i && miss_vld_bits_i[2] == 8'hFF);//eviction 
           5'b10011 : events[1] = i_tlb_flush_i;//I-TLB flush
           5'b10100 : for (int unsigned i = 0; i < NR_COMMIT_PORTS; i++) if (commit_ack_i[i]) events[1] = commit_instr_i[i].fu == ALU || commit_instr_i[i].fu == MULT;//Integer instructions
           5'b10101 : for (int unsigned i = 0; i < NR_COMMIT_PORTS; i++) if (commit_ack_i[i]) events[1] = commit_instr_i[i].fu == FPU || commit_instr_i[i].fu == FPU_VEC;//Floating Point Instructions
           5'b10110 : events[1] = stall_issue_i;//Pipeline bubbles
           default:   events[1] = 0;
         endcase
       
        case(mhpmevent_q[2])
           5'b00000 : events[2] = 0;
           5'b00001 : events[2] = l1_icache_miss_i;
           5'b00010 : events[2] = l1_dcache_miss_i;
           5'b00011 : events[2] = itlb_miss_i;
           5'b00100 : events[2] = dtlb_miss_i;
           5'b00101 : for (int unsigned i = 0; i < NR_COMMIT_PORTS; i++) if (commit_ack_i[i]) events[2] = commit_instr_i[i].fu == LOAD; 							 
           5'b00110 : for (int unsigned i = 0; i < NR_COMMIT_PORTS; i++) if (commit_ack_i[i]) events[2] = commit_instr_i[i].fu == STORE;
           5'b00111 : events[2] = ex_i.valid;
           5'b01000 : events[2] = eret_i;
           5'b01001 : for (int unsigned i = 0; i < NR_COMMIT_PORTS; i++) if (commit_ack_i[i]) events[2] = commit_instr_i[i].fu == CTRL_FLOW;
           5'b01010 : events[2] = resolved_branch_i.valid && resolved_branch_i.is_mispredict;
           5'b01011 : events[2] = branch_exceptions_i.valid;
           5'b01100 : for (int unsigned i = 0; i < NR_COMMIT_PORTS; i++) if (commit_ack_i[i]) events[2] = commit_instr_i[i].fu == CTRL_FLOW && (commit_instr_i[i].op == ADD || commit_instr_i[i].op == JALR) && (commit_instr_i[i].rd == 'd1 || commit_instr_i[i].rd == 'd5);
           5'b01101 : for (int unsigned i = 0; i < NR_COMMIT_PORTS; i++) if (commit_ack_i[i]) events[2] = commit_instr_i[i].op == JALR && commit_instr_i[i].rd == 'd0;
           5'b01110 : events[2] = sb_full_i;
           5'b01111 : events[2] = if_empty_i;
           5'b10000 : events[2] = l1_icache_access_i.req;
           5'b10001 : events[2] = l1_dcache_access_i[0].data_req || l1_dcache_access_i[1].data_req || l1_dcache_access_i[2].data_req;
           5'b10010 : events[2] = (l1_dcache_miss_i && miss_vld_bits_i[0] == 8'hFF) || (l1_dcache_miss_i && miss_vld_bits_i[1] == 8'hFF) || (l1_dcache_miss_i && miss_vld_bits_i[2] == 8'hFF); 
           5'b10011 : events[2] = i_tlb_flush_i;
           5'b10100 : for (int unsigned i = 0; i < NR_COMMIT_PORTS; i++) if (commit_ack_i[i]) events[2] = commit_instr_i[i].fu == ALU || commit_instr_i[i].fu == MULT;
           5'b10101 : for (int unsigned i = 0; i < NR_COMMIT_PORTS; i++) if (commit_ack_i[i]) events[2] = commit_instr_i[i].fu == FPU || commit_instr_i[i].fu == FPU_VEC;
           5'b10110 : events[2] = stall_issue_i;
           default:   events[2] = 0;
         endcase
       
         case(mhpmevent_q[3])
           5'b00000 : events[3] = 0;
           5'b00001 : events[3] = l1_icache_miss_i;
           5'b00010 : events[3] = l1_dcache_miss_i;
           5'b00011 : events[3] = itlb_miss_i;
           5'b00100 : events[3] = dtlb_miss_i;
           5'b00101 : for (int unsigned i = 0; i < NR_COMMIT_PORTS; i++) if (commit_ack_i[i]) events[3] = commit_instr_i[i].fu == LOAD; 							 
           5'b00110 : for (int unsigned i = 0; i < NR_COMMIT_PORTS; i++) if (commit_ack_i[i]) events[3] = commit_instr_i[i].fu == STORE;
           5'b00111 : events[3] = ex_i.valid;
           5'b01000 : events[3] = eret_i;
           5'b01001 : for (int unsigned i = 0; i < NR_COMMIT_PORTS; i++) if (commit_ack_i[i]) events[3] = commit_instr_i[i].fu == CTRL_FLOW; 
           5'b01010 : events[3] = resolved_branch_i.valid && resolved_branch_i.is_mispredict;
           5'b01011 : events[3] = branch_exceptions_i.valid;
           5'b01100 : for (int unsigned i = 0; i < NR_COMMIT_PORTS; i++) if (commit_ack_i[i]) events[3] = commit_instr_i[i].fu == CTRL_FLOW && (commit_instr_i[i].op == ADD || commit_instr_i[i].op == JALR) && (commit_instr_i[i].rd == 'd1 || commit_instr_i[i].rd == 'd5);
           5'b01101 : for (int unsigned i = 0; i < NR_COMMIT_PORTS; i++) if (commit_ack_i[i]) events[3] = commit_instr_i[i].op == JALR && commit_instr_i[i].rd == 'd0;
           5'b01110 : events[3] = sb_full_i;
           5'b01111 : events[3] = if_empty_i;
           5'b10000 : events[3] = l1_icache_access_i.req;
           5'b10001 : events[3] = l1_dcache_access_i[0].data_req || l1_dcache_access_i[1].data_req || l1_dcache_access_i[2].data_req;
           5'b10010 : events[3] = (l1_dcache_miss_i && miss_vld_bits_i[0] == 8'hFF) || (l1_dcache_miss_i && miss_vld_bits_i[1] == 8'hFF) || (l1_dcache_miss_i && miss_vld_bits_i[2] == 8'hFF); 
           5'b10011 : events[3] = i_tlb_flush_i;
           5'b10100 : for (int unsigned i = 0; i < NR_COMMIT_PORTS; i++) if (commit_ack_i[i]) events[3] = commit_instr_i[i].fu == ALU || commit_instr_i[i].fu == MULT;
           5'b10101 : for (int unsigned i = 0; i < NR_COMMIT_PORTS; i++) if (commit_ack_i[i]) events[3] = commit_instr_i[i].fu == FPU || commit_instr_i[i].fu == FPU_VEC;
           5'b10110 : events[3] = stall_issue_i;
           default:   events[3] = 0;
         endcase

         case(mhpmevent_q[4])
           5'b00000 : events[4] = 0;
           5'b00001 : events[4] = l1_icache_miss_i;
           5'b00010 : events[4] = l1_dcache_miss_i;
           5'b00011 : events[4] = itlb_miss_i;
           5'b00100 : events[4] = dtlb_miss_i;
           5'b00101 : for (int unsigned i = 0; i < NR_COMMIT_PORTS; i++) if (commit_ack_i[i]) events[4] = commit_instr_i[i].fu == LOAD; 							 
           5'b00110 : for (int unsigned i = 0; i < NR_COMMIT_PORTS; i++) if (commit_ack_i[i]) events[4] = commit_instr_i[i].fu == STORE;
           5'b00111 : events[4] = ex_i.valid;
           5'b01000 : events[4] = eret_i;
           5'b01001 : for (int unsigned i = 0; i < NR_COMMIT_PORTS; i++) if (commit_ack_i[i]) events[4] = commit_instr_i[i].fu == CTRL_FLOW;
           5'b01010 : events[4] = resolved_branch_i.valid && resolved_branch_i.is_mispredict;
           5'b01011 : events[4] = branch_exceptions_i.valid;
           5'b01100 : for (int unsigned i = 0; i < NR_COMMIT_PORTS; i++) if (commit_ack_i[i]) events[4] = commit_instr_i[i].fu == CTRL_FLOW && (commit_instr_i[i].op == ADD || commit_instr_i[i].op == JALR) && (commit_instr_i[i].rd == 'd1 || commit_instr_i[i].rd == 'd5);
           5'b01101 : for (int unsigned i = 0; i < NR_COMMIT_PORTS; i++) if (commit_ack_i[i]) events[4] = commit_instr_i[i].op == JALR && commit_instr_i[i].rd == 'd0;
           5'b01110 : events[4] = sb_full_i;
           5'b01111 : events[4] = if_empty_i;
           5'b10000 : events[4] = l1_icache_access_i.req;
           5'b10001 : events[4] = l1_dcache_access_i[0].data_req || l1_dcache_access_i[1].data_req || l1_dcache_access_i[2].data_req;
           5'b10010 : events[4] = (l1_dcache_miss_i && miss_vld_bits_i[0] == 8'hFF) || (l1_dcache_miss_i && miss_vld_bits_i[1] == 8'hFF) || (l1_dcache_miss_i && miss_vld_bits_i[2] == 8'hFF); 
           5'b10011 : events[4] = i_tlb_flush_i;
           5'b10100 : for (int unsigned i = 0; i < NR_COMMIT_PORTS; i++) if (commit_ack_i[i]) events[4] = commit_instr_i[i].fu == ALU || commit_instr_i[i].fu == MULT;
           5'b10101 : for (int unsigned i = 0; i < NR_COMMIT_PORTS; i++) if (commit_ack_i[i]) events[4] = commit_instr_i[i].fu == FPU || commit_instr_i[i].fu == FPU_VEC;
           5'b10110 : events[4] = stall_issue_i;
           default:   events[4] = 0;
         endcase
       
         case(mhpmevent_q[5])
           5'b00000 : events[5] = 0;
           5'b00001 : events[5] = l1_icache_miss_i;
           5'b00010 : events[5] = l1_dcache_miss_i;
           5'b00011 : events[5] = itlb_miss_i;
           5'b00100 : events[5] = dtlb_miss_i;
           5'b00101 : for (int unsigned i = 0; i < NR_COMMIT_PORTS; i++) if (commit_ack_i[i]) events[5] = commit_instr_i[i].fu == LOAD; 							 
           5'b00110 : for (int unsigned i = 0; i < NR_COMMIT_PORTS; i++) if (commit_ack_i[i]) events[5] = commit_instr_i[i].fu == STORE;
           5'b00111 : events[5] = ex_i.valid;
           5'b01000 : events[5] = eret_i;
           5'b01001 : for (int unsigned i = 0; i < NR_COMMIT_PORTS; i++) if (commit_ack_i[i]) events[5] = commit_instr_i[i].fu == CTRL_FLOW;
           5'b01010 : events[5] = resolved_branch_i.valid && resolved_branch_i.is_mispredict;
           5'b01011 : events[5] = branch_exceptions_i.valid;
           5'b01100 : for (int unsigned i = 0; i < NR_COMMIT_PORTS; i++) if (commit_ack_i[i]) events[5] = commit_instr_i[i].fu == CTRL_FLOW && (commit_instr_i[i].op == ADD || commit_instr_i[i].op == JALR) && (commit_instr_i[i].rd == 'd1 || commit_instr_i[i].rd == 'd5);
           5'b01101 : for (int unsigned i = 0; i < NR_COMMIT_PORTS; i++) if (commit_ack_i[i]) events[5] = commit_instr_i[i].op == JALR && commit_instr_i[i].rd == 'd0;
           5'b01110 : events[5] = sb_full_i;
           5'b01111 : events[5] = if_empty_i;
           5'b10000 : events[5] = l1_icache_access_i.req;
           5'b10001 : events[5] = l1_dcache_access_i[0].data_req || l1_dcache_access_i[1].data_req || l1_dcache_access_i[2].data_req;
           5'b10010 : events[5] = (l1_dcache_miss_i && miss_vld_bits_i[0] == 8'hFF) || (l1_dcache_miss_i && miss_vld_bits_i[1] == 8'hFF) || (l1_dcache_miss_i && miss_vld_bits_i[2] == 8'hFF);
           5'b10011 : events[5] = i_tlb_flush_i;
           5'b10100 : for (int unsigned i = 0; i < NR_COMMIT_PORTS; i++) if (commit_ack_i[i]) events[5] = commit_instr_i[i].fu == ALU || commit_instr_i[i].fu == MULT;
           5'b10101 : for (int unsigned i = 0; i < NR_COMMIT_PORTS; i++) if (commit_ack_i[i]) events[5] = commit_instr_i[i].fu == FPU || commit_instr_i[i].fu == FPU_VEC;
           5'b10110 : events[5] = stall_issue_i;
           default:   events[5] = 0;
         endcase

         case(mhpmevent_q[6])
            5'b00000 : events[6] = 0;
            5'b00001 : events[6] = l1_icache_miss_i;
            5'b00010 : events[6] = l1_dcache_miss_i;
            5'b00011 : events[6] = itlb_miss_i;
            5'b00100 : events[6] = dtlb_miss_i;
            5'b00101 : for (int unsigned i = 0; i < NR_COMMIT_PORTS; i++) if (commit_ack_i[i]) events[6] = commit_instr_i[i].fu == LOAD; 							 
            5'b00110 : for (int unsigned i = 0; i < NR_COMMIT_PORTS; i++) if (commit_ack_i[i]) events[6] = commit_instr_i[i].fu == STORE;
            5'b00111 : events[6] = ex_i.valid;
            5'b01000 : events[6] = eret_i;
            5'b01001 : for (int unsigned i = 0; i < NR_COMMIT_PORTS; i++) if (commit_ack_i[i]) events[6] = commit_instr_i[i].fu == CTRL_FLOW; 
            5'b01010 : events[6] = resolved_branch_i.valid && resolved_branch_i.is_mispredict;
            5'b01011 : events[6] = branch_exceptions_i.valid;
            5'b01100 : for (int unsigned i = 0; i < NR_COMMIT_PORTS; i++) if (commit_ack_i[i]) events[6] = commit_instr_i[i].fu == CTRL_FLOW && (commit_instr_i[i].op == ADD || commit_instr_i[i].op == JALR) && (commit_instr_i[i].rd == 'd1 || commit_instr_i[i].rd == 'd5);
            5'b01101 : for (int unsigned i = 0; i < NR_COMMIT_PORTS; i++) if (commit_ack_i[i]) events[6] = commit_instr_i[i].op == JALR && commit_instr_i[i].rd == 'd0;
            5'b01110 : events[6] = sb_full_i;
            5'b01111 : events[6] = if_empty_i;
            5'b10000 : events[6] = l1_icache_access_i.req;
            5'b10001 : events[6] = l1_dcache_access_i[0].data_req || l1_dcache_access_i[1].data_req || l1_dcache_access_i[2].data_req;
            5'b10010 : events[6] = (l1_dcache_miss_i && miss_vld_bits_i[0] == 8'hFF) || (l1_dcache_miss_i && miss_vld_bits_i[1] == 8'hFF) || (l1_dcache_miss_i && miss_vld_bits_i[2] == 8'hFF);
            5'b10011 : events[6] = i_tlb_flush_i;
            5'b10100 : for (int unsigned i = 0; i < NR_COMMIT_PORTS; i++) if (commit_ack_i[i]) events[6] = commit_instr_i[i].fu == ALU || commit_instr_i[i].fu == MULT;
            5'b10101 : for (int unsigned i = 0; i < NR_COMMIT_PORTS; i++) if (commit_ack_i[i]) events[6] = commit_instr_i[i].fu == FPU || commit_instr_i[i].fu == FPU_VEC;
            5'b10110 : events[6] = stall_issue_i;
            default:   events[6] = 0;
         endcase
         
    end     
            
    always_comb begin : generic_counter
        generic_counter_d = generic_counter_q;
        data_o = 'b0;
        mhpmevent_d = mhpmevent_q;
	    read_access_exception =  1'b0;
	    update_access_exception =  1'b0;
	  	  
      for(int unsigned i = 1; i <= 6; i++) begin	  
         if ((!debug_mode_i) && (!we_i)) begin   
             if (events[i] == 1)begin
                generic_counter_d[i] = generic_counter_q[i] + 1'b1;end
            else begin
                generic_counter_d[i] = 'b0;end           
        end
      end    
      
     //Read
         unique case (addr_i)
            riscv::CSR_MHPM_COUNTER_3,  
            riscv::CSR_MHPM_COUNTER_4,            
            riscv::CSR_MHPM_COUNTER_5,             
            riscv::CSR_MHPM_COUNTER_6,  
            riscv::CSR_MHPM_COUNTER_7,  
            riscv::CSR_MHPM_COUNTER_8  :begin if (riscv::XLEN == 32) data_o = generic_counter_q[addr_i-riscv::CSR_MHPM_COUNTER_3 + 1][31:0]; else data_o = generic_counter_q[addr_i-riscv::CSR_MHPM_COUNTER_3 + 1];end
            riscv::CSR_MHPM_COUNTER_3H,  
            riscv::CSR_MHPM_COUNTER_4H,   
            riscv::CSR_MHPM_COUNTER_5H, 
            riscv::CSR_MHPM_COUNTER_6H,   
            riscv::CSR_MHPM_COUNTER_7H, 
            riscv::CSR_MHPM_COUNTER_8H :begin if (riscv::XLEN == 32) data_o = generic_counter_q[addr_i-riscv::CSR_MHPM_COUNTER_3H + 1][63:32]; else read_access_exception = 1'b1;end
            riscv::CSR_MHPM_EVENT_3,  
            riscv::CSR_MHPM_EVENT_4,  
            riscv::CSR_MHPM_EVENT_5,  
            riscv::CSR_MHPM_EVENT_6,  
            riscv::CSR_MHPM_EVENT_7,  
            riscv::CSR_MHPM_EVENT_8   : data_o = mhpmevent_q[addr_i-riscv::CSR_MHPM_EVENT_3 + 1] ;
            default: data_o = 'b0;
        endcase    
 
     //Write
     if(we_i) begin
        unique case(addr_i)
            riscv::CSR_MHPM_COUNTER_3,  
            riscv::CSR_MHPM_COUNTER_4,            
            riscv::CSR_MHPM_COUNTER_5,             
            riscv::CSR_MHPM_COUNTER_6,  
            riscv::CSR_MHPM_COUNTER_7,  
            riscv::CSR_MHPM_COUNTER_8  :begin if (riscv::XLEN == 32) generic_counter_d[addr_i-riscv::CSR_MHPM_COUNTER_3 + 1][31:0] = data_i; else generic_counter_d[addr_i-riscv::CSR_MHPM_COUNTER_3 + 1] = data_i; end
            riscv::CSR_MHPM_COUNTER_3H, 
            riscv::CSR_MHPM_COUNTER_4H,   
            riscv::CSR_MHPM_COUNTER_5H, 
            riscv::CSR_MHPM_COUNTER_6H,   
            riscv::CSR_MHPM_COUNTER_7H, 
            riscv::CSR_MHPM_COUNTER_8H :begin if (riscv::XLEN == 32) generic_counter_d[addr_i-riscv::CSR_MHPM_COUNTER_3H + 1][63:32] = data_i; else update_access_exception = 1'b1;end
            riscv::CSR_MHPM_EVENT_3,  
            riscv::CSR_MHPM_EVENT_4,  
            riscv::CSR_MHPM_EVENT_5,  
            riscv::CSR_MHPM_EVENT_6,  
            riscv::CSR_MHPM_EVENT_7,  
            riscv::CSR_MHPM_EVENT_8   : mhpmevent_d[addr_i-riscv::CSR_MHPM_EVENT_3 + 1] = data_i;
            default: update_access_exception =  1'b1;
        endcase
      end
    end

//Registers
  always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
            generic_counter_q <= '{default:0};
            mhpmevent_q       <= '{default:0};
        end else begin
            generic_counter_q <= generic_counter_d;
            mhpmevent_q       <= mhpmevent_d;
       end
   end

endmodule




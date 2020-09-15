//
// Copyright 2020 OpenHW Group
// Copyright 2020 Datum Technologies
// 
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
// 
//     https://solderpad.org/licenses/
// 
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
// 

module uvmt_cv32e40p_interrupt_assert  
  import uvm_pkg::*;
  import cv32e40p_pkg::*;
  (
    
    input clk_i,
    input rst_ni,

    // Core inputs
    input        fetch_enable_i, // external core fetch enable

    // External interrupt interface
    input [31:0] irq_i,
    input        irq_ack_o,
    input [4:0]  irq_id_o,

    // External debug req (for WFI modeling)
    input        debug_req_i,

    // CSR Interface
    input [5:0]  mcause_n, // mcause_n[5]: interrupt, mcause_n[4]: vector
    input [31:0] mip,     // machine interrupt pending
    input [31:0] mie_q,   // machine interrupt enable
    input        mstatus_mie, // machine mode interrupt enable
    input [1:0]  mtvec_mode_q, // machine mode interrupt vector mode

    // Instruction fetch stage
    input        if_stage_instr_rvalid_i, // Instruction word is valid
    input [31:0] if_stage_instr_rdata_i, // Instruction word data

    // Instruction ID stage (determines executed instructions)  
    input        id_stage_instr_valid_i, // instruction word is valid
    input [31:0] id_stage_instr_rdata_i, // Instruction word data
    input [4:0]  ctrl_fsm_cs,            // Controller FSM to get hint for interrupt taken
    input [1:0]  exc_ctrl_cs,            // Controller FSM to get hint for interrupt pending (for arbitration)

    // WFI Interface
    input core_sleep_o
  );

  // ---------------------------------------------------------------------------
  // Local parameters
  // ---------------------------------------------------------------------------  
  localparam NUM_IRQ        = 32;  
  localparam VALID_IRQ_MASK = 32'hffff_0888; // Valid external interrupt signals

  localparam WFI_INSTR_MASK = 32'hffffffff;
  localparam WFI_INSTR_DATA = 32'h10500073;

  localparam WFI_WAKEUP_LATENCY = 40;

  // ---------------------------------------------------------------------------
  // Local variables
  // ---------------------------------------------------------------------------
  string info_tag = "CV32E40P_IRQ_ASSERT";

  wire [31:0] pending_enabled_irq;

  wire id_instr_is_wfi; // ID instruction is a WFI
  reg  in_wfi; // Local model of WFI state of core

  reg[1:0]  exc_ctrl_cs_q;

  reg[31:0] next_irq;
  reg       next_irq_valid;

  reg[31:0] next_irq_q;    
  reg       next_irq_valid_q;
  reg[31:0] saved_mie_q;

  reg[31:0] expected_irq;
  reg       expected_irq_ack;

  reg[31:0] last_instr_rdata;

  // ---------------------------------------------------------------------------
  // Clocking blocks
  // ---------------------------------------------------------------------------

  // Single clock, single reset design, use default clocking
  default clocking @(posedge clk_i); endclocking
  default disable iff !(rst_ni);

  // ---------------------------------------------------------------------------
  // Begin module code
  // ---------------------------------------------------------------------------
  assign pending_enabled_irq = irq_i & mie_q;

  // ---------------------------------------------------------------------------
  // Interrupt interface checks
  // ---------------------------------------------------------------------------

  // irq_ack_o is always a pulse
  property p_irq_ack_o_pulse;
    irq_ack_o |=> !irq_ack_o;
  endproperty
  a_irq_ack_o_pulse: assert property(p_irq_ack_o_pulse)
    else
      `uvm_error(info_tag,
                 "Interrupt ack was asserted for more than one cycle");

  // irq_id_o is never a reserved irq
  property p_irq_id_o_not_reserved;
    irq_ack_o |-> VALID_IRQ_MASK[irq_id_o];
  endproperty    
  a_irq_id_o_not_reserved: assert property(p_irq_id_o_not_reserved)
    else
      `uvm_error(info_tag,
                 $sformatf("int_id_o output is 0x%0x which is reserved", irq_id_o));

  // irq_id_o is never a disabled irq
  property p_irq_id_o_mie_enabled;
    irq_ack_o |-> saved_mie_q[irq_id_o];
  endproperty    
  a_irq_id_o_mie_enabled: assert property(p_irq_id_o_mie_enabled)
    else
      `uvm_error(info_tag,
                 $sformatf("int_id_o output is 0x%0x which is disabled in MIE: 0x%08x", irq_id_o, mie_q));

  // irq_ack_o cannot be asserted if mstatus_mie is deasserted
  property p_irq_id_o_mstatus_mie_enabled;
    irq_ack_o |-> mstatus_mie;
  endproperty
  a_irq_id_o_mstatus_mie_enabled: assert property(p_irq_id_o_mstatus_mie_enabled)
    else
      `uvm_error(info_tag,
                 $sformatf("int_id_o output is 0x%0x but MSTATUS.MIE is disabled", irq_id_o));
  
  // ---------------------------------------------------------------------------
  // Interrupt CSR checks
  // ---------------------------------------------------------------------------

  // Coverage for individual interupt assertions
  sequence s_irq_taken(irq);
    irq_i[irq] ##0 mie_q[irq] ##0 mstatus_mie ##0 irq_ack_o ##0 irq_id_o == irq;
  endsequence : s_irq_taken

  // Interrupt fired, global interrupts enabled, but not taken due to global MSTATUS.MIE setting
  property p_irq_masked(irq);
    irq_i[irq] ##0 !mie_q[irq] ##0 mstatus_mie;    
  endproperty : p_irq_masked

  // Interrupt fired and locally enabled in MIE, but masked due to MSTATUS_MIE
  property p_irq_masked_mstatus(irq);
    irq_i[irq] ##0 mie_q[irq] ##0 !mstatus_mie;
  endproperty : p_irq_masked_mstatus

  // Interrupt taken
  property p_irq_taken(irq);
    s_irq_taken(irq);
  endproperty : p_irq_taken

  // Interrupt enabled via MIE locally masked
  property p_irq_masked_then_enabled(irq);
    irq_i[irq] ##0 !mie_q[irq] ##0 mstatus_mie ##1 irq_i[irq] ##0 mie_q[irq] ##0 mstatus_mie;
  endproperty : p_irq_masked_then_enabled

  // Interrupt enabled via MSTATUS_MIE locally masked
  property p_irq_masked_mstatus_then_enabled(irq);
    irq_i[irq] ##0 mie_q[irq] ##0 !mstatus_mie ##1 irq_i[irq] ##0 mie_q[irq] ##0 mstatus_mie;
  endproperty : p_irq_masked_mstatus_then_enabled

  // Interrupt request deasserted when enabled but not acked
  property p_irq_deasserted_while_enabled_not_acked(irq);
    irq_i[irq] ##0 mie_q[irq] ##0 mstatus_mie ##0 !irq_ack_o ##1 
    !irq_i[irq] ##0 !irq_ack_o;
  endproperty : p_irq_deasserted_while_enabled_not_acked  

  // Interrupt taken in each supported mtvec mode
  property p_irq_in_mtvec(irq, mtvec);
    s_irq_taken(irq) ##0 mtvec_mode_q == mtvec;
  endproperty

  generate for(genvar gv_i = 0; gv_i < NUM_IRQ; gv_i++) begin : gen_irq_cov
    if (VALID_IRQ_MASK[gv_i]) begin : gen_valid
      c_irq_masked: cover property(p_irq_masked(gv_i));
      c_irq_masked_mstatus: cover property(p_irq_masked_mstatus(gv_i));
      c_irq_taken: cover property(p_irq_taken(gv_i));
      c_irq_masked_then_enabled: cover property(p_irq_masked_then_enabled(gv_i));
      c_irq_masked_mstatus_then_enabled: cover property(p_irq_masked_mstatus_then_enabled(gv_i));
      c_irq_deasserted_while_enabled_not_acked: cover property(p_irq_deasserted_while_enabled_not_acked(gv_i));
      c_irq_in_mtvec_fixed: cover property(p_irq_in_mtvec(gv_i, 0));
      c_irq_in_mtvec_vector: cover property(p_irq_in_mtvec(gv_i, 1));
    end
  end
  endgenerate

  // Detect arbitration of interrupt assertion
  always @* begin
    next_irq_valid = 1'b0;
    next_irq = '0;
    casex ({pending_enabled_irq[31:16], pending_enabled_irq[11], pending_enabled_irq[3], pending_enabled_irq[7]})
      19'b1???_????_????_????_???: begin next_irq = 'd31; next_irq_valid = '1; end
      19'b01??_????_????_????_???: begin next_irq = 'd30; next_irq_valid = '1; end
      19'b001?_????_????_????_???: begin next_irq = 'd29; next_irq_valid = '1; end
      19'b0001_????_????_????_???: begin next_irq = 'd28; next_irq_valid = '1; end
      19'b0000_1???_????_????_???: begin next_irq = 'd27; next_irq_valid = '1; end
      19'b0000_01??_????_????_???: begin next_irq = 'd26; next_irq_valid = '1; end
      19'b0000_001?_????_????_???: begin next_irq = 'd25; next_irq_valid = '1; end
      19'b0000_0001_????_????_???: begin next_irq = 'd24; next_irq_valid = '1; end
      19'b0000_0000_1???_????_???: begin next_irq = 'd23; next_irq_valid = '1; end
      19'b0000_0000_01??_????_???: begin next_irq = 'd22; next_irq_valid = '1; end
      19'b0000_0000_001?_????_???: begin next_irq = 'd21; next_irq_valid = '1; end
      19'b0000_0000_0001_????_???: begin next_irq = 'd20; next_irq_valid = '1; end
      19'b0000_0000_0000_1???_???: begin next_irq = 'd19; next_irq_valid = '1; end
      19'b0000_0000_0000_01??_???: begin next_irq = 'd18; next_irq_valid = '1; end
      19'b0000_0000_0000_001?_???: begin next_irq = 'd17; next_irq_valid = '1; end
      19'b0000_0000_0000_0001_???: begin next_irq = 'd16; next_irq_valid = '1; end
      19'b0000_0000_0000_0000_1??: begin next_irq = 'd11; next_irq_valid = '1; end
      19'b0000_0000_0000_0000_01?: begin next_irq = 'd3; next_irq_valid = '1; end
      19'b0000_0000_0000_0000_001: begin next_irq = 'd7; next_irq_valid = '1; end
    endcase
  end

  always @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      exc_ctrl_cs_q <= 0;
      next_irq_q <= 0;
      next_irq_valid_q <= 0;
      saved_mie_q <= 0;
    end    
    else begin
      exc_ctrl_cs_q <= exc_ctrl_cs;
      // Only latch new interrupt if interrupt controller state machine is idel
      if (exc_ctrl_cs == 0) begin
        next_irq_q <= next_irq;
        next_irq_valid_q <= next_irq_valid;
        saved_mie_q <= mie_q;
      end
    end
  end

  always @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni)
      expected_irq <= 0;
    else if (exc_ctrl_cs == 1 && exc_ctrl_cs_q == 0)
      expected_irq <= next_irq_q;
  end

  always @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni)
      expected_irq_ack <= 0;
    else if (irq_ack_o)
      expected_irq_ack <= 0;
    else if (exc_ctrl_cs == 1 && exc_ctrl_cs_q == 0 && next_irq_valid_q)
      expected_irq_ack <= 1;
  end

  // Check expected interrupt wins
  property p_irq_arb;
    irq_ack_o |-> irq_id_o == expected_irq;
  endproperty
  a_irq_arb: assert property(p_irq_arb)
    else
      `uvm_error(info_tag,
                 $sformatf("Expected winning interrupt: %0d, actual interrupt: %0d", expected_irq, irq_id_o))  

  // Check that an interrupt is expected
  property p_irq_expected;
    irq_ack_o |-> expected_irq_ack;
  endproperty
  a_irq_expected: assert property(p_irq_expected)
    else
      `uvm_error(info_tag,
                 $sformatf("Did not expect interrupt ack: %0d", irq_id_o))

  // mcause is never a reserved interrupt
  property p_mcause_irq_not_reserved;
    mcause_n[5] |-> VALID_IRQ_MASK[mcause_n[4:0]];
  endproperty
  a_mcause_irq_not_reserved: assert property(p_mcause_irq_not_reserved)
    else
      `uvm_error(info_tag,
                 $sformatf("MCAUSE[4:0] is reserved value 0x%0x when reporting interrupt", mcause_n[4:0]));

  // mip reflects input (irq_i) regardless of other configuration
  property p_mip_irq_i;
    mip == (irq_i & VALID_IRQ_MASK);
  endproperty
  a_mip_irq_i: assert property(p_mip_irq_i)
    else 
      `uvm_error(info_tag,
                 $sformatf("MIP of 0x%08x does not follow irq_i input: 0x%08x", mip, irq_i));

  // mip should not be reserved
  property p_mip_not_reserved;
    (mip & ~VALID_IRQ_MASK) == 0;
  endproperty
  a_mip_not_reserved: assert property(p_mip_not_reserved)
    else
      `uvm_error(info_tag,
                 $sformatf("MIP of reserved interrupt is asserted: mip = 0x%08x", mip));

  // ---------------------------------------------------------------------------
  // Instruction coverage when taking an interrupt
  // ---------------------------------------------------------------------------
  always @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      last_instr_rdata <= '0;
    end
    else if (id_stage_instr_valid_i) begin
      last_instr_rdata <= id_stage_instr_rdata_i;
    end
  end
  reg take_cov;

  always @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni)
      take_cov <= 1'b0;
    else if (ctrl_fsm_cs == IRQ_TAKEN_ID)
      take_cov <= 1'b1;
    else
      take_cov <= 1'b0;
  end

  // ---------------------------------------------------------------------------
  // WFI Checks
  // ---------------------------------------------------------------------------
  assign is_wfi = id_stage_instr_valid_i & 
                  ((id_stage_instr_rdata_i & WFI_INSTR_MASK) == WFI_INSTR_DATA);
  always @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      in_wfi <= 1'b0;
    end
    else begin
      if (is_wfi) 
        in_wfi <= 1'b1;
      else if (|pending_enabled_irq || debug_req_i)
        in_wfi <= 1'b0;
    end
  end

  // WFI assertion will assert core_sleep_o in 6 clocks
  property p_wfi_assert_core_sleep_o;
    $rose(in_wfi) ##1 in_wfi[*6] ##0 !pending_enabled_irq |-> core_sleep_o;
  endproperty
  // a_wfi_assert_core_sleep_o: assert property(p_wfi_assert_core_sleep_o)
  //   else
  //     `uvm_error(info_tag,
  //                "Assertion of wfi did not put core to sleep in 4 clocks");

  // core_sleep_o deassertion in wfi should be followed by WFI deassertion
  property p_core_sleep_deassert;
    $fell(core_sleep_o) ##0 in_wfi |-> ##1 !in_wfi;
  endproperty
  a_core_sleep_deassert: assert property(p_core_sleep_deassert)
    else
      `uvm_error(info_tag,
                 "Deassertion of core_sleep_o in WFI not followed by WFI wakeup");
  
  // When WFI deasserts the core should be awake
  property p_wfi_deassert_core_sleep_o;
    $fell(in_wfi) |-> !core_sleep_o;
  endproperty
  a_wfi_deassert_core_sleep_o: assert property(p_wfi_deassert_core_sleep_o) 
    else
      `uvm_error(info_tag,
                 "Deassertion of WFI occurred and core is still asleep");

  // WFI wakeup to next instruction fetch
  property p_wfi_wake_to_instr_fetch; 
    disable iff (!rst_ni || !fetch_enable_i)
      $fell(in_wfi) |-> ##[1:WFI_WAKEUP_LATENCY] if_stage_instr_rvalid_i;
  endproperty
  a_wfi_wake_to_instr_fetch: assert property(p_wfi_wake_to_instr_fetch)
    else
      `uvm_error(info_tag,
                 $sformatf("Core did not start fetching %0d cycles after WFI completed", WFI_WAKEUP_LATENCY));

  // Cover property, detect sleep deassertion due to asserted and non-asserted interrupts
  property p_wfi_wake_mstatus_mie(irq, mie);
    $fell(in_wfi) ##0 irq_i[irq] ##0 mie_q[irq] ##0 mstatus_mie == mie;
  endproperty 
  generate for(genvar gv_i = 0; gv_i < 32; gv_i++) begin : gen_wfi_cov
    if (VALID_IRQ_MASK[gv_i]) begin
      c_wfi_wake_mstatus_mie_0: cover property(p_wfi_wake_mstatus_mie(gv_i, 0));
      c_wfi_wake_mstatus_mie_1: cover property(p_wfi_wake_mstatus_mie(gv_i, 1));
    end
  end
  endgenerate

endmodule : uvmt_cv32e40p_interrupt_assert

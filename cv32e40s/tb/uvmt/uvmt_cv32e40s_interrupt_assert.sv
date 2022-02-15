//
// Copyright 2020 OpenHW Group
// Copyright 2020 Datum Technology Corporation
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

module uvmt_cv32e40s_interrupt_assert
  import uvm_pkg::*;
  import cv32e40s_pkg::*;
  (

    input clk,   // Gated clock
    input clk_i, // Free-running core clock
    input rst_ni,

    // Core inputs
    input        fetch_enable_i, // external core fetch enable

    // External interrupt interface
    input [31:0] irq_i,
    input        irq_ack_o,
    input [4:0]  irq_id_o,

    // External debug req (for WFI modeling)
    input        debug_req_i,
    input        debug_mode_q,

    // CSR Interface
    input [5:0]  mcause_n, // mcause_n[5]: interrupt, mcause_n[4]: vector
    input [31:0] mip,     // machine interrupt pending
    input [31:0] mie_q,   // machine interrupt enable
    input        mstatus_mie, // machine mode interrupt enable
    input [1:0]  mtvec_mode_q, // machine mode interrupt vector mode

    // Instruction fetch stage
    input        if_stage_instr_req_o,
    input        if_stage_instr_rvalid_i, // Instruction word is valid
    input [31:0] if_stage_instr_rdata_i, // Instruction word data
    input [ 1:0] alignbuf_outstanding, // Alignment buffer's number of outstanding transactions

    // Instruction EX stage
    input        ex_stage_instr_valid, // EX pipeline stage has valid input

    // Instruction WB stage (determines executed instructions)
    input              wb_stage_instr_valid_i,    // instruction word is valid
    input [31:0]       wb_stage_instr_rdata_i,    // Instruction word data
    input              wb_stage_instr_err_i,      // OBI "err"
    input mpu_status_e wb_stage_instr_mpu_status, // MPU read/write errors

    // Load-store unit status
    input              lsu_busy,

    // Determine whether to cancel instruction if branch taken
    input branch_taken_ex,

    // WFI Interface
    input core_sleep_o
  );

  // ---------------------------------------------------------------------------
  // Local parameters
  // ---------------------------------------------------------------------------
  localparam NUM_IRQ        = 32;
  localparam VALID_IRQ_MASK = 32'hffff_0888; // Valid external interrupt signals

  localparam WFI_INSTR_DATA = 32'h10500073;

  localparam WFI_TO_CORE_SLEEP_LATENCY = 2;
  localparam WFI_WAKEUP_LATENCY = 40;

  // ---------------------------------------------------------------------------
  // Local variables
  // ---------------------------------------------------------------------------
  string info_tag = "CV32E40S_IRQ_ASSERT";

  wire [31:0] pending_enabled_irq;
  wire [31:0] pending_enabled_irq_q;

  reg  in_wfi; // Local model of WFI state of core

  reg[31:0] irq_q;

  reg[31:0] next_irq;
  reg       next_irq_valid;

  reg[31:0] next_irq_q;
  reg       next_irq_valid_q;
  reg[31:0] saved_mie_q;

  reg[31:0] expected_irq;
  logic     expected_irq_ack;

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
  assign pending_enabled_irq   = irq_i & mie_q;
  assign pending_enabled_irq_q = irq_q & mie_q;

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
    irq_ack_o |-> mie_q[irq_id_o];
  endproperty
  a_irq_id_o_mie_enabled: assert property(p_irq_id_o_mie_enabled)
    else
      `uvm_error(info_tag,
                 $sformatf("irq_id_o output is 0x%0x which is disabled in MIE: 0x%08x", irq_id_o, mie_q));

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
    casex ({pending_enabled_irq_q[31:16], pending_enabled_irq_q[11], pending_enabled_irq_q[3], pending_enabled_irq_q[7]})
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
      irq_q <= 0;
      next_irq_q <= 0;
      next_irq_valid_q <= 0;
      saved_mie_q <= 0;
    end
    else begin
      irq_q <= irq_i;
      next_irq_q <= next_irq;
      next_irq_valid_q <= next_irq_valid;
      saved_mie_q <= mie_q;
    end
  end

  always @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni)
      expected_irq <= 0;
    else
      expected_irq <= next_irq_q;
  end

  assign expected_irq_ack = next_irq_valid & mstatus_mie;

  // Check expected interrupt wins
  property p_irq_arb;
    irq_ack_o |-> irq_id_o == next_irq;
  endproperty
  a_irq_arb: assert property(p_irq_arb)
    else
      `uvm_error(info_tag,
                 $sformatf("Expected winning interrupt: %0d, actual interrupt: %0d", next_irq, irq_id_o))

  // Check that an interrupt is expected
  property p_irq_expected;
    irq_ack_o |-> expected_irq_ack;
  endproperty
  a_irq_expected: assert property(p_irq_expected)
    else
      `uvm_error(info_tag,
                 $sformatf("Did not expect interrupt ack: %0d", irq_id_o))

  // ---------------------------------------------------------------------------
  // The infamous "first" flag (kludge for $past() handling of t=0 values)
  // Would like to use a leading ##1 in the property instead but this currently
  // does not work with dsim
  // ---------------------------------------------------------------------------
  reg first;
  always @(posedge clk or negedge rst_ni)
    if (!rst_ni)
      first <= 1'b1;
    else
      first <= 1'b0;

  // mip reflects flopped interrupt inputs (irq_i) regardless of other configuration
  // Note that this runs on the gated clock
  property p_mip_irq_i;
    @(posedge clk)
      !first |-> mip == ($past(irq_i) & VALID_IRQ_MASK);
  endproperty
  a_mip_irq_i: assert property(p_mip_irq_i)
    else
      `uvm_error(info_tag,
                 $sformatf("MIP of 0x%08x does not follow flopped irq_i input: 0x%08x", mip, $past(irq_i)));

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
    else if (wb_stage_instr_valid_i) begin
      last_instr_rdata <= wb_stage_instr_rdata_i;
    end
  end

  // ---------------------------------------------------------------------------
  // WFI Checks
  // ---------------------------------------------------------------------------
  assign is_wfi = wb_stage_instr_valid_i                     &&
                  (wb_stage_instr_rdata_i == WFI_INSTR_DATA) &&
                  !branch_taken_ex                           &&
                  !wb_stage_instr_err_i                      &&
                  (wb_stage_instr_mpu_status == MPU_OK);
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

  assign pipeline_ready_for_wfi = (alignbuf_outstanding == 0) && !lsu_busy;

  // WFI assertion will assert core_sleep_o (in WFI_TO_CORE_SLEEP_LATENCY cycles after wb, given ideal conditions)
  property p_wfi_assert_core_sleep_o;
    !in_wfi
    ##1 (in_wfi && !pending_enabled_irq && !debug_mode_q && !debug_req_i)[*(WFI_TO_CORE_SLEEP_LATENCY-1)]
    ##1 (
      (in_wfi && !pending_enabled_irq && !debug_mode_q && !debug_req_i)
        throughout $past(pipeline_ready_for_wfi)[->1]
      )
    |->
    core_sleep_o;
  endproperty
  a_wfi_assert_core_sleep_o: assert property(p_wfi_assert_core_sleep_o)
    else
      `uvm_error(info_tag,
                 $sformatf("Assertion of core_sleep_o did not occur within %0d clocks", WFI_TO_CORE_SLEEP_LATENCY))
  c_wfi_assert_core_sleep_o: cover property(p_wfi_assert_core_sleep_o);

  // WFI assertion will assert core_sleep_o (after required conditions are met)
  property p_wfi_assert_core_sleep_o_cond;
    !in_wfi
    ##1 (
      (in_wfi && !pending_enabled_irq && !debug_mode_q && !debug_req_i)
      throughout (##1 ($past(pipeline_ready_for_wfi)[->1]) )
      )
    |->
    core_sleep_o;
  endproperty
  a_wfi_assert_core_sleep_o_cond: assert property(p_wfi_assert_core_sleep_o_cond)
    else
      `uvm_error(info_tag,
                 "Assertion of core_sleep_o did not occur upon its prerequisite conditions")
  c_wfi_assert_core_sleep_o_cond: cover property(p_wfi_assert_core_sleep_o_cond);

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
    core_sleep_o ##1 pending_enabled_irq |-> !core_sleep_o;
  endproperty
  a_wfi_deassert_core_sleep_o: assert property(p_wfi_deassert_core_sleep_o)
    else
      `uvm_error(info_tag,
                 "Deassertion of WFI occurred and core is still asleep");

  // Outside of WFI, the core should not sleep
  a_wfi_deny_core_sleep_o: assert property (
    !in_wfi |-> !core_sleep_o
  ) else
    `uvm_error(info_tag, "Only WFI should trigger core sleep");

  // WFI wakeup to next instruction fetch/execution
  property p_wfi_wake_to_instr_fetch;
    disable iff (!rst_ni || !fetch_enable_i || debug_mode_q)
    core_sleep_o && in_wfi
    ##1 !in_wfi[->1]
    |->
    ##[0:WFI_WAKEUP_LATENCY]
      ($rose(if_stage_instr_req_o)  // IF starts fetching again
        || $rose(ex_stage_instr_valid));  // Or continue with prefetched data
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

endmodule : uvmt_cv32e40s_interrupt_assert

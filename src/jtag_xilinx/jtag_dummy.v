`timescale 1ns / 1ps
`default_nettype none

module jtag_dummy(
    output wire [5:0] DBG,
    output wire WREN,
    output wire [63:0] TO_MEM,
    output wire [31:0] ADDR,
    input wire [63:0] FROM_MEM,
    output wire TCK,
    output wire TCK2,
    output wire RESET,
    output wire RUNTEST);

wire CAPTURE, DRCK, SEL, SHIFT, TDI, TDO, TMS, UPDATE, TCK_unbuf;
wire CAPTURE2, DRCK2, RESET2, RUNTEST2, SEL2, SHIFT2, TDI2, TDO2, TMS2, UPDATE2;
   wire INC, WR;
wire [31:0] ADDR0;
   
BUFH jtag_buf(.I(TCK_unbuf), .O(TCK));

   // BSCANE2: Boundary-Scan User Instruction
   //          Artix-7
   // Xilinx HDL Language Template, version 2017.1

   BSCANE2 #(
      .JTAG_CHAIN(1)  // Value for USER command.
   )
   BSCANE2_inst (
      .CAPTURE(CAPTURE), // 1-bit output: CAPTURE output from TAP controller.
      .DRCK(DRCK),       // 1-bit output: Gated TCK output. When SEL is asserted, DRCK toggles when CAPTURE or
                         // SHIFT are asserted.

      .RESET(RESET),     // 1-bit output: Reset output for TAP controller.
      .RUNTEST(RUNTEST), // 1-bit output: Output asserted when TAP controller is in Run Test/Idle state.
      .SEL(SEL),         // 1-bit output: USER instruction active output.
      .SHIFT(SHIFT),     // 1-bit output: SHIFT output from TAP controller.
      .TCK(TCK_unbuf),   // 1-bit output: Test Clock output. Fabric connection to TAP Clock pin.
      .TDI(TDI),         // 1-bit output: Test Data Input (TDI) output from TAP controller.
      .TMS(TMS),         // 1-bit output: Test Mode Select output. Fabric connection to TAP.
      .UPDATE(UPDATE),   // 1-bit output: UPDATE output from TAP controller
      .TDO(TDO)    // 1-bit input: Test Data Output (TDO) input for USER function.
   );

   BSCANE2 #(
      .JTAG_CHAIN(2)  // Value for USER command.
   )
   BSCANE2_inst2 (
      .CAPTURE(CAPTURE2), // 1-bit output: CAPTURE output from TAP controller.
      .DRCK(DRCK2),       // 1-bit output: Gated TCK output. When SEL is asserted, DRCK toggles when CAPTURE or
                         // SHIFT are asserted.

      .RESET(RESET2),     // 1-bit output: Reset output for TAP controller.
      .RUNTEST(RUNTEST2), // 1-bit output: Output asserted when TAP controller is in Run Test/Idle state.
      .SEL(SEL2),         // 1-bit output: USER instruction active output.
      .SHIFT(SHIFT2),     // 1-bit output: SHIFT output from TAP controller.
      .TCK(TCK2),   // 1-bit output: Test Clock output. Fabric connection to TAP Clock pin.
      .TDI(TDI2),         // 1-bit output: Test Data Input (TDI) output from TAP controller.
      .TMS(TMS2),         // 1-bit output: Test Mode Select output. Fabric connection to TAP.
      .UPDATE(UPDATE2),   // 1-bit output: UPDATE output from TAP controller
      .TDO(TDO2)    // 1-bit input: Test Data Output (TDO) input for USER function.
   );

jtag_rom rom1(
.WREN(WREN),
.TO_MEM(TO_MEM),
.ADDR(ADDR),
.FROM_MEM(FROM_MEM),
.INC(INC),
.WR(WR),
.ADDR0(ADDR0),
.TDO(TDO),	 
.CAPTURE(CAPTURE), 
.RESET(RESET), 
.RUNTEST(RUNTEST), 
.SEL(SEL), 
.SHIFT(SHIFT), 
.TDI(TDI), 
.TMS(TMS), 
.UPDATE(UPDATE), 
.TCK(TCK)
);

jtag_addr addr1(
.DBG(DBG),
.INC(INC),
.WR(WR),
.ADDR(ADDR0),
.TDO(TDO2),	 
.CAPTURE(CAPTURE2), 
.RESET(RESET2), 
.RUNTEST(RUNTEST2), 
.SEL(SEL2), 
.SHIFT(SHIFT2), 
.TDI(TDI2), 
.TMS(TMS2), 
.UPDATE(UPDATE2), 
.TCK(TCK)
);
				
endmodule

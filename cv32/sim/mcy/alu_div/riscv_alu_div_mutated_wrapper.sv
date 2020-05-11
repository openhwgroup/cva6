module riscv_alu_div
  #(
     parameter C_WIDTH     = 32,
     parameter C_LOG_WIDTH = 6
  )
  (
    input  logic                    Clk_CI,
    input  logic                    Rst_RBI,
    // input IF
    input  logic [C_WIDTH-1:0]      OpA_DI,
    input  logic [C_WIDTH-1:0]      OpB_DI,
    input  logic [C_LOG_WIDTH-1:0]  OpBShift_DI,
    input  logic                    OpBIsZero_SI,
    //
    input  logic                    OpBSign_SI, // gate this to 0 in case of unsigned ops
    input  logic [1:0]              OpCode_SI,  // 0: udiv, 2: urem, 1: div, 3: rem
    // handshake
    input  logic                    InVld_SI,
    // output IF
    input  logic                    OutRdy_SI,
    output logic                    OutVld_SO,
    output logic [C_WIDTH-1:0]      Res_DO
  );

if (C_WIDTH != 32 || C_LOG_WIDTH != 6) $error("Changing parameters for mutated modules not supported.");

reg [7:0] mutsel = 8'h00;

export "DPI-C" task set_mutidx;
task set_mutidx(input [7:0] idx);
  mutsel = idx;
endtask

mutated div_i
  (
   .Clk_CI       ( Clk_CI       ),
   .Rst_RBI      ( Rst_RBI      ),

   // input IF
   .OpA_DI       ( OpA_DI       ),
   .OpB_DI       ( OpB_DI ),
   .OpBShift_DI  ( OpBShift_DI  ),
   .OpBIsZero_SI ( OpBIsZero_SI ),

   .OpBSign_SI   ( OpBSign_SI   ),
   .OpCode_SI    ( OpCode_SI    ),

   .Res_DO       ( Res_DO       ),

   // Hand-Shake
   .InVld_SI     ( InVld_SI     ),
   .OutRdy_SI    ( OutRdy_SI    ),
   .OutVld_SO    ( OutVld_SO    ),

   // mutation selection
   .mutsel       ( mutsel       )
  );

endmodule

// Abstraction of subset of Xilinx FIFO generator functionality to a primitive
`default_nettype none

  module my_fifo #(parameter width=9) (
                                       input wire              rd_clk,
                                       input wire              wr_clk,
                                       input wire              rst,
                                       input wire [width-1:0]  din,
                                       input wire              wr_en,
                                       input wire              rd_en,
                                       output wire [width-1:0] dout,
                                       output wire             full,
                                       output wire             empty,
                                       output wire             almostfull,
                                       output wire [11:0]      rdcount, // 12-bit output: Read count
                                       output wire             rderr, // 1-bit output: Read error
                                       output wire [11:0]      wrcount, // 12-bit output: Write count
                                       output wire             wrerr            // 1-bit output: Write error
                                       );

   wire [31:0]                                                 DO, DI;
   wire [3:0]                                                  DOP, DIP;

   assign dout = {DOP[width/9-1:0],DO[width/9*8-1:0]};
   assign DIP = din[width-1:width/9*8];
   assign DI = din[width/9*8-1:0];
   
   
   // FIFO18E1: 18Kb FIFO (First-In-First-Out) Block RAM Memory
   //           Artix-7
   // Xilinx HDL Language Template, version 2015.4

   generate
         if (width==36)
      begin:gen36
     
     FIFO18E1 #(
                .ALMOST_EMPTY_OFFSET(13'h0080),    // Sets the almost empty threshold
                .ALMOST_FULL_OFFSET(13'h0080),     // Sets almost full threshold
                .DATA_WIDTH(width),                // Sets data width to 4-36
                .DO_REG(1),                        // Enable output register (1-0) Must be 1 if EN_SYN = FALSE
                .EN_SYN("FALSE"),                  // Specifies FIFO as dual-clock (FALSE) or Synchronous (TRUE)
                .FIFO_MODE("FIFO18_36"),           // Sets mode to FIFO18 or FIFO18_36
                .FIRST_WORD_FALL_THROUGH("FALSE"), // Sets the FIFO FWFT to FALSE, TRUE
                .INIT(36'h000000000),              // Initial values on output port
                .SIM_DEVICE("7SERIES"),            // Must be set to "7SERIES" for simulation behavior
                .SRVAL(36'h000000000)              // Set/Reset value for output port
                )
      FIFO18E1_inst_36 (
                        // Read Data: 32-bit (each) output: Read output data
                        .DO(DO),                   // 32-bit output: Data output
                        .DOP(DOP),                 // 4-bit output: Parity data output
                        // Status: 1-bit (each) output: Flags and other FIFO status outputs
                        .ALMOSTEMPTY(),            // 1-bit output: Almost empty flag
                        .ALMOSTFULL(almostfull),   // 1-bit output: Almost full flag
                        .EMPTY(empty),             // 1-bit output: Empty flag
                        .FULL(full),               // 1-bit output: Full flag
                        .RDCOUNT(rdcount),         // 12-bit output: Read count
                        .RDERR(rderr),             // 1-bit output: Read error
                        .WRCOUNT(wrcount),         // 12-bit output: Write count
                        .WRERR(wrerr),             // 1-bit output: Write error
                        // Read Control Signals: 1-bit (each) input: Read clock, enable and reset input signals
                        .RDCLK(rd_clk),            // 1-bit input: Read clock
                        .RDEN(rd_en),              // 1-bit input: Read enable
                        .REGCE(1'b1),              // 1-bit input: Clock enable
                        .RSTREG(rst),              // 1-bit input: Asynchronous Reset
                        .RST(rst),                 // 1-bit input: Asynchronous Reset
                        // Write Control Signals: 1-bit (each) input: Write clock and enable input signals
                        .WRCLK(wr_clk),            // 1-bit input: Write clock
                        .WREN(wr_en),              // 1-bit input: Write enable
                        // Write Data: 32-bit (each) input: Write input data
                        .DI(DI),                   // 32-bit input: Data input
                        .DIP(DIP)                  // 4-bit input: Parity input
                        );
         end
         else
           begin:genelse
     FIFO18E1 #(
                .ALMOST_EMPTY_OFFSET(13'h0080),    // Sets the almost empty threshold
                .ALMOST_FULL_OFFSET(13'h0080),     // Sets almost full threshold
                .DATA_WIDTH(width),                // Sets data width to 4-36
      .DO_REG(0),                        // Enable output register (1-0) Must be 1 if EN_SYN = FALSE
      .EN_SYN("TRUE"),                   // Specifies FIFO as dual-clock (FALSE) or Synchronous (TRUE)
                .FIFO_MODE("FIFO18"),              // Sets mode to FIFO18 or FIFO18_36
                .FIRST_WORD_FALL_THROUGH("FALSE"), // Sets the FIFO FWFT to FALSE, TRUE
                .INIT(36'h000000000),              // Initial values on output port
                .SIM_DEVICE("7SERIES"),            // Must be set to "7SERIES" for simulation behavior
                .SRVAL(36'h000000000)              // Set/Reset value for output port
                )
      FIFO18E1_inst_18 (
                        // Read Data: 32-bit (each) output: Read output data
                        .DO(DO),                   // 32-bit output: Data output
                        .DOP(DOP),                 // 4-bit output: Parity data output
                        // Status: 1-bit (each) output: Flags and other FIFO status outputs
                        .ALMOSTEMPTY(),            // 1-bit output: Almost empty flag
                        .ALMOSTFULL(almostfull),   // 1-bit output: Almost full flag
                        .EMPTY(empty),             // 1-bit output: Empty flag
                        .FULL(full),               // 1-bit output: Full flag
                        .RDCOUNT(rdcount),         // 12-bit output: Read count
                        .RDERR(rderr),             // 1-bit output: Read error
                        .WRCOUNT(wrcount),         // 12-bit output: Write count
                        .WRERR(wrerr),             // 1-bit output: Write error
                        // Read Control Signals: 1-bit (each) input: Read clock, enable and reset input signals
                        .RDCLK(rd_clk),              // 1-bit input: Read clock
                        .RDEN(rd_en),              // 1-bit input: Read enable
                        .REGCE(1'b1),              // 1-bit input: Clock enable
                        .RST(rst),                 // 1-bit input: Asynchronous Reset
                        .RSTREG(rst),              // 1-bit input: Output register set/reset
                        // Write Control Signals: 1-bit (each) input: Write clock and enable input signals
                        .WRCLK(wr_clk),              // 1-bit input: Write clock
                        .WREN(wr_en),               // 1-bit input: Write enable
                        // Write Data: 32-bit (each) input: Write input data
                        .DI(DI),                   // 32-bit input: Data input
                        .DIP(DIP)                  // 4-bit input: Parity input
                        );
      end
   endgenerate
   
endmodule
`default_nettype wire

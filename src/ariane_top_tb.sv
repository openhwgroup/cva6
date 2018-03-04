`timescale 1ns/1ps

module ariane_top_tb;

logic  clk_p;
logic  rst_top;
logic [15:0] i_dip = 16'h55AA;
logic [15:0] o_led;  
   
   ariane_top top(
   .clk_p(clk_p),
   .rst_top(rst_top),
   .i_dip(i_dip),
   .o_led(o_led));

    assign glbl.JTAG_TMS_GLBL = 1'b0;
    assign glbl.JTAG_TCK_GLBL = 1'b0;
    assign glbl.JTAG_TDI_GLBL = 1'b0;
    assign glbl.JTAG_TRST_GLBL = 1'b0;

initial
    begin
    $dumpvars(0, top);   
    glbl.JTAG_RESET_GLBL = 1'b1;
    glbl.JTAG_SHIFT_GLBL = 1'b0;
    glbl.JTAG_UPDATE_GLBL = 1'b0;
    glbl.JTAG_CAPTURE_GLBL = 1'b0;
    glbl.JTAG_RUNTEST_GLBL = 1'b0;
    force glbl.JTAG_TRST_GLBL = 1'b1;       
    rst_top = 1'b0;
    clk_p = 1'b0;                    
    forever
        begin
        #1000 clk_p = ~clk_p;
           force glbl.JTAG_TCK_GLBL = 1'b1;
        #1000 clk_p = ~clk_p;
           release glbl.JTAG_TCK_GLBL;
        #1000 clk_p = ~clk_p;
           force glbl.JTAG_TCK_GLBL = 1'b1;
        #1000 clk_p = ~clk_p;
           release glbl.JTAG_TCK_GLBL;
           release glbl.JTAG_TRST_GLBL;
           glbl.JTAG_RESET_GLBL = 1'b0;
           rst_top = 1'b1;
        end
    end

endmodule

`ifdef VCS
`ifdef STILLX
`include "stillx.log"
`endif
`endif

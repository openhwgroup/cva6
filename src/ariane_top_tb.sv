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

initial
    begin
    $dumpvars(0, top);
    rst_top = 1'b0;
    clk_p = 1'b0;                    
    forever
        begin
        #1000 clk_p = ~clk_p;
        #1000 clk_p = ~clk_p;
        #1000 clk_p = ~clk_p;
        #1000 clk_p = ~clk_p;
        #1000 clk_p = ~clk_p;
        rst_top = 1'b1;
        end
    end

endmodule

`ifdef VCS
`include "stillx.log"
`endif

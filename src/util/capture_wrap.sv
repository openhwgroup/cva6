module capture_wrap(
    input logic    clk_i,    // Clock
    input logic    rst_ni,  // Asynchronous reset active low
    AXI_BUS        capture_if,
    output logic [289:0] capture
);

capture_in capture1(
         .clk_i(clk_i),
         .rst_ni(rst_ni),
         .capture_out(capture),              // output wire [96 : 0] pc_status
         .capture_in({
 capture_if.aw_valid  ,
 capture_if.aw_prot   ,
 capture_if.aw_region ,
 capture_if.aw_len    ,
 capture_if.aw_size   ,
 capture_if.aw_burst  ,
 capture_if.aw_lock   ,
 capture_if.aw_cache  ,
 capture_if.aw_qos    ,
 capture_if.aw_id     ,
 capture_if.aw_ready  ,
 capture_if.ar_valid  ,
 capture_if.ar_prot   ,
 capture_if.ar_region ,
 capture_if.ar_len    ,
 capture_if.ar_size   ,
 capture_if.ar_burst  ,
 capture_if.ar_lock   ,
 capture_if.ar_cache  ,
 capture_if.ar_qos    ,
 capture_if.ar_id     ,
 capture_if.ar_ready  ,
 capture_if.w_valid   ,
 capture_if.w_strb    ,
 capture_if.w_last    ,
 capture_if.w_ready   ,
 capture_if.r_valid   ,
 capture_if.r_resp    ,
 capture_if.r_last    ,
 capture_if.r_id      ,
 capture_if.r_ready   ,
 capture_if.b_valid   ,
 capture_if.b_resp    ,
 capture_if.b_id      ,
 capture_if.b_ready   ,
 capture_if.w_data    ,
 capture_if.r_data    ,
 capture_if.aw_addr   ,
 capture_if.ar_addr   }));
 
endmodule

module capture_in(
input logic    clk_i,    // Clock
input logic    rst_ni,  // Asynchronous reset active low
input logic [289:0] capture_in,
output logic [289:0] capture_out
);

always @(posedge clk_i)
    if (rst_ni == 0)
    capture_out <= 0;
    else
    capture_out <= capture_in;
    
endmodule
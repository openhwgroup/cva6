module ariane_top(
                  input logic  clk_p,
                  input logic  rst_top,
                  input logic [15:0] i_dip,
                  output logic [15:0] o_led
                  );

   logic             clk_i, locked;          
   logic             test_en_i = 'b0; // enable all clock gates for testing
   // Core ID; Cluster ID and boot address are considered more or less static
   logic [ 3:0]      core_id_i = 'b0;
   logic [ 5:0]      cluster_id_i = 'b0;
   logic             flush_req_i = 'b0;
   logic             flushing_o;
   // Interrupt s
   logic [1:0]       irq_i = 'b0; // level sensitive IR lines; mip & sip
   logic             ipi_i = 'b0; // inter-processor interrupts
   logic             sec_lvl_o; // current privilege level oot
   // Timer facilities
   logic [63:0]      time_i = 'b0; // global time (most probably coming from an RTC)
   logic             time_irq_i = 'b0; // timer interrupt in

   parameter logic [63:0]               CACHE_START_ADDR  = 64'h8000_0000;
 // address on which to decide whether the request is cache-able or not
   parameter int                        unsigned AXI_ID_WIDTH      = 10;
   parameter int                        unsigned AXI_USER_WIDTH    = 1;
   parameter int                        unsigned AXI_ADDRESS_WIDTH = 64;
   parameter int                        unsigned AXI_DATA_WIDTH    = 64;

   ariane_wrapped dut(
   .clk_i(clk_i),
   .rst_ni(rst_top && locked),
   .*);

     clk_wiz_ariane clk_wiz_instance
      (
       .resetn(rst_top),
      // Clock in ports
       .clk_in1(clk_p),      // input clk_in1
       // Clock out ports
       .clk_i(clk_i),     // output clk_i
       // Status and control signals
       .locked(locked));      // output locked
                     
endmodule
                        

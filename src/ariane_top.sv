module ariane_top(
                  input logic  clk_p,
                  input logic  rst_top,
                  input logic [15:0] i_dip,
                  output logic [15:0] o_led
                  );
          
   logic             test_en_i; // enable all clock gates for testing
   // CPU Control Signals
   logic             fetch_enable_i;
   // Core ID; Cluster ID and boot address are considered more or less static
   logic [63:0]      boot_addr_i;
   logic [ 3:0]      core_id_i;
   logic [ 5:0]      cluster_id_i;
   logic             flush_req_i;
   logic             flushing_o;
   // Interrupt s
   logic [1:0]       irq_i; // level sensitive IR lines; mip & sip
   logic             ipi_i; // inter-processor interrupts
   logic             sec_lvl_o; // current privilege level oot
   // Timer facilities
   logic [63:0]      time_i; // global time (most probably coming from an RTC)
   logic             time_irq_i; // timer interrupt in
   // Debug Interface
   logic             debug_req_i;
   logic             debug_gnt_o;
   logic             debug_rvalid_o;
   logic [15:0]      debug_addr_i;
   logic             debug_we_i;
   logic [63:0]      debug_wdata_i;
   logic [63:0]      debug_rdata_o;
   logic             debug_halted_o;
   logic             debug_halt_i;
   logic             debug_resume_i;
   

   parameter logic [63:0]               CACHE_START_ADDR  = 64'h8000_0000;
 // address on which to decide whether the request is cache-able or not
   parameter int                        unsigned AXI_ID_WIDTH      = 10;
   parameter int                        unsigned AXI_USER_WIDTH    = 1;
   parameter int                        unsigned AXI_ADDRESS_WIDTH = 64;
   parameter int                        unsigned AXI_DATA_WIDTH    = 64;
   
   ariane_wrapped dut(
   .clk_i(clk_p),
   .rst_ni(rst_top),
   .*);
                      
endmodule
                        

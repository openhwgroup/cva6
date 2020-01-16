// COPYRIGHT HEADER


`ifndef __UVMA_DEBUG_IF_SV__
`define __UVMA_DEBUG_IF_SV__


/**
 * Encapsulates all signals and clocking of Debug interface. Used by
 * monitor and driver.
 */
interface uvma_debug_if(
   input  clk  ,
   input  reset
);
   
   // TODO Add uvma_debug_if signals
   // Ex:  wire        enable;
   //      wire [7:0]  data;
   
   
   /**
    * Used by target DUT.
    */
   clocking dut_cb @(posedge clk or reset);
      // TODO Implement uvma_debug_if::dut_cb()
      //      Ex: input  enable,
      //                 data  ;
   endclocking : dut_cb
   
   /**
    * Used by uvma_debug_drv_c.
    */
   clocking drv_cb @(posedge clk or reset);
      // TODO Implement uvma_debug_if::drv_cb()
      //      Ex: output  enable,
      //                  data  ;
   endclocking : drv_cb
   
   /**
    * Used by uvma_debug_mon_c.
    */
   clocking mon_cb @(posedge clk or reset);
      // TODO Implement uvma_debug_if::mon_cb()
      //      Ex: input  enable,
      //                 data  ;
   endclocking : mon_cb
   
   
   modport dut_mp    (clocking dut_cb);
   modport active_mp (clocking drv_cb);
   modport passive_mp(clocking mon_cb);
   
endinterface : uvma_debug_if


`endif // __UVMA_DEBUG_IF_SV__

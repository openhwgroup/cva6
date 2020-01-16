// COPYRIGHT HEADER


`ifndef __UVMA_RESET_IF_SV__
`define __UVMA_RESET_IF_SV__


/**
 * Encapsulates all signals and clocking of Reset interface. Used by
 * monitor and driver.
 */
interface uvma_reset_if(
   input  clk  ,
   input  reset
);
   
   // TODO Add uvma_reset_if signals
   // Ex:  wire        enable;
   //      wire [7:0]  data;
   
   
   /**
    * Used by target DUT.
    */
   clocking dut_cb @(posedge clk or reset);
      // TODO Implement uvma_reset_if::dut_cb()
      //      Ex: input  enable,
      //                 data  ;
   endclocking : dut_cb
   
   /**
    * Used by uvma_reset_drv_c.
    */
   clocking drv_cb @(posedge clk or reset);
      // TODO Implement uvma_reset_if::drv_cb()
      //      Ex: output  enable,
      //                  data  ;
   endclocking : drv_cb
   
   /**
    * Used by uvma_reset_mon_c.
    */
   clocking mon_cb @(posedge clk or reset);
      // TODO Implement uvma_reset_if::mon_cb()
      //      Ex: input  enable,
      //                 data  ;
   endclocking : mon_cb
   
   
   modport dut_mp    (clocking dut_cb);
   modport active_mp (clocking drv_cb);
   modport passive_mp(clocking mon_cb);
   
endinterface : uvma_reset_if


`endif // __UVMA_RESET_IF_SV__

`timescale 1ns / 1ps

module Top;

  localparam integer ADDR_BITW      = 32;
  localparam integer MST_DATA_BITW  = 32;
  localparam integer SLV_DATA_BITW  = 96;

  BramPort
    #(
      .DATA_BITW(MST_DATA_BITW),
      .ADDR_BITW(ADDR_BITW)
    )
    fromMaster ();

  BramPort
    #(
      .DATA_BITW(SLV_DATA_BITW),
      .ADDR_BITW(ADDR_BITW)
    )
    toSlave ();

  BramDwc
    #(
      .ADDR_BITW      (ADDR_BITW),
      .MST_DATA_BITW  (MST_DATA_BITW),
      .SLV_DATA_BITW  (SLV_DATA_BITW)
    ) dwc (
      .FromMaster_PS  (fromMaster),
      .ToSlave_PM     (toSlave)
    );

  assign fromMaster.Clk_C   = '0;
  assign fromMaster.Rst_R   = '0;
  assign fromMaster.En_S    = '0;
  assign fromMaster.Addr_S  = '0;
  assign fromMaster.Wr_D    = '0;
  assign fromMaster.WrEn_S  = '0;

  assign toSlave.Rd_D       = '0;

endmodule

// vim: nosmartindent autoindent

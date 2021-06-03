`ifndef TCDM_EXPLODE_MACROS_SVH
`define TCDM_EXPLODE_MACROS_SVH


  `define TCDM_EXPLODE_ARRAY_DECLARE(signal_prefix, length) \
logic [length-1:0]                 signal_prefix``_req; \
logic [length-1:0][31:0]           signal_prefix``_add; \
logic [length-1:0]                 signal_prefix``_wen; \
logic [length-1:0][31:0]           signal_prefix``_wdata; \
logic [length-1:0][3:0]            signal_prefix``_be; \
logic [length-1:0]                 signal_prefix``_gnt; \
logic [length-1:0]                 signal_prefix``_r_opc; \
logic [length-1:0][31:0]           signal_prefix``_r_rdata; \
logic [length-1:0]                 signal_prefix``_r_valid;

  `define TCDM_EXPLODE_DECLARE(signal_prefix) \
logic                  signal_prefix``_req; \
logic [31:0]           signal_prefix``_add; \
logic                  signal_prefix``_wen; \
logic [31:0]           signal_prefix``_wdata; \
logic [3:0]            signal_prefix``_be; \
logic                  signal_prefix``_gnt; \
logic                  signal_prefix``_r_opc; \
logic [31:0]           signal_prefix``_r_rdata; \
logic                  signal_prefix``_r_valid;

//Connect a TCDM Master Interface to a set of exploded interface signals
  `define TCDM_SLAVE_EXPLODE(iface, exploded_prefix, postfix) \
assign iface.req = exploded_prefix``_req postfix; \
assign iface.add = exploded_prefix``_add postfix; \
assign iface.wen = exploded_prefix``_wen postfix; \
assign iface.wdata = exploded_prefix``_wdata postfix; \
assign iface.be = exploded_prefix``_be postfix; \
assign exploded_prefix``_gnt postfix = iface.gnt; \
assign exploded_prefix``_r_opc postfix = iface.r_opc; \
assign exploded_prefix``_r_rdata postfix = iface.r_rdata; \
assign exploded_prefix``_r_valid postfix = iface.r_valid;

//Connect a TCDM Slave Interface to a set of exploded interface signals
  `define TCDM_MASTER_EXPLODE(iface, exploded_prefix, postfix) \
assign exploded_prefix``_req postfix = iface.req; \
assign exploded_prefix``_add postfix = iface.add; \
assign exploded_prefix``_wen postfix = iface.wen; \
assign exploded_prefix``_wdata postfix = iface.wdata; \
assign exploded_prefix``_be postfix = iface.be; \
assign iface.gnt = exploded_prefix``_gnt postfix; \
assign iface.r_opc = exploded_prefix``_r_opc postfix; \
assign iface.r_rdata = exploded_prefix``_r_rdata postfix; \
assign iface.r_valid = exploded_prefix``_r_valid postfix;

  `define TCDM_ASSIGN_INTF(b, a) \
assign b.req  = a.req; \
assign b.add  = a.add; \
assign b.wen  = a.wen; \
assign b.wdata  = a.wdata; \
assign b.be  = a.be; \
assign a.gnt = b.gnt ; \
assign a.r_opc = b.r_opc ; \
assign a.r_rdata= b.r_rdata ; \
assign a.r_valid = b.r_valid ;

  `define TCDM_ASSIGN(b, postfix_b, a, postfix_a) \
assign b``_req postfix_b  = a``_req postfix_a; \
assign b``_add postfix_b  = a``_add postfix_a; \
assign b``_wen postfix_b  = a``_wen postfix_a; \
assign b``_wdata postfix_b  = a``_wdata postfix_a; \
assign b``_be postfix_b  = a``_be postfix_a; \
assign a``_gnt postfix_a = b``_gnt postfix_b ; \
assign a``_r_opc postfix_a = b``_r_opc postfix_b ; \
assign a``_r_rdata postfix_a= b``_r_rdata postfix_b ; \
assign a``_r_valid postfix_a = b``_r_valid postfix_b ;

`endif

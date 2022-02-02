

`ifndef __UVMA_CVXIF_TDEFS_SV__
`define __UVMA_CVXIF_TDEFS_SV__

   localparam X_DATAWIDTH  = cvxif_pkg::X_DATAWIDTH;
   localparam X_ID_WIDTH   = cvxif_pkg::X_ID_WIDTH;
   localparam X_RFW_WIDTH  = cvxif_pkg::X_RFW_WIDTH;
   localparam X_NUM_RS     = cvxif_pkg::X_NUM_RS;
   localparam X_RFR_WIDTH  = cvxif_pkg::X_RFR_WIDTH;

typedef struct packed {
      logic    accept;
      logic    writeback;
      logic    dualwrite;
      logic    dualread;
      logic    loadstore;
      logic    exc;
   } issue_resp_t;

   typedef struct packed {
      logic  [X_ID_WIDTH-1:0]   id;
      logic  [X_DATAWIDTH-1:0]  data;
      logic  [4:0]              rd;
      logic  [X_RFW_WIDTH-1:0]  we;
      logic                     exc;
      logic  [5:0]              exccode;
   } result_t ;

  typedef struct packed {
    logic  [31:0]                          instr;
    logic  [X_ID_WIDTH-1:0]                id;
    logic  [1:0]                           mode;
    logic  [X_NUM_RS-1:0][X_RFR_WIDTH-1:0] rs;
  } x_issue_req;

  typedef struct packed {
    logic  [X_ID_WIDTH-1:0]      id;
    logic                        commit_kill;
  } x_commit;


`endif //__UVMA_CVXIF_TDEFS_SV__

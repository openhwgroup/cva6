package wt_new_cache_pkg;
  parameter int unsigned NUM_DUAL_SETS = 2; // number of sets accessible by Controller B

  typedef enum logic [0:0] {
    CTRL_A = 1'b0,
    CTRL_B = 1'b1
  } wt_new_ctrl_sel_e;
endpackage

package wt_new_cache_pkg;
  parameter int unsigned NUM_DUAL_SETS = 2; // number of sets accessible by Controller B

  // Replacement policy for dual-addressable sets
  typedef enum logic [1:0] {
    REPL_ROUND_ROBIN = 2'b00,
    REPL_RANDOM      = 2'b01,
    REPL_PSEUDO_LRU  = 2'b10
  } wt_new_replacement_e;

  // Flush policy when switching privilege levels
  typedef enum logic [0:0] {
    FLUSH_ON_SWITCH,
    RETAIN_ON_SWITCH
  } wt_new_flush_policy_e;

  // Enable or disable the secondary controller
  typedef enum logic [0:0] {
    B_CTRL_DISABLE = 1'b0,
    B_CTRL_ENABLE  = 1'b1
  } wt_new_b_ctrl_e;

  typedef enum logic [0:0] {
    CTRL_A = 1'b0,
    CTRL_B = 1'b1
  } wt_new_ctrl_sel_e;
endpackage

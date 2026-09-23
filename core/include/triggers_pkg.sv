package triggers_pkg;
  // Triggers
  typedef struct packed {
    logic [31:28] t_type;   // type 3 for icount
    logic         dmode;
    logic         vs;
    logic         vu;
    logic         hit;
    logic [23:10] count;
    logic         m;
    logic         pending;
    logic         s;
    logic         u;
    logic [5:0]   action;
  } icount32_tdata1_t;

  typedef struct packed {
    logic [31:26] mhvalue;
    logic [25:23] mhselect;
    logic [22:20] zeroes;
    logic [19:18] sbytemask;
    logic [17:2]  svalue;
    logic [1:0]   sselect;
  } textra32_tdata3_t;

  typedef struct packed {
    logic [63:51] mhvalue;
    logic [50:48] mhselect;
    logic [47:40] zeroes;
    logic [39:36] sbytemask;
    logic [35:34] zero_field;
    logic [33:2]  svalue;
    logic [1:0]   sselect;
  } textra64_tdata3_t;

  typedef struct packed {
    logic [31:28] t_type;  // type 6 for mcontrol6
    logic dmode;
    logic uncertain;
    logic hit1;
    logic vs;
    logic vu;
    logic hit0;
    logic select;
    logic [20:19] zeroes;
    logic [18:16] size;
    logic [15:12] action;
    logic chain;
    logic [10:7] match;
    logic m;
    logic uncertainen;
    logic s;
    logic u;
    logic execute;
    logic store;
    logic load;
  } mcontrol6_32_tdata1_t;

  typedef struct packed {
    logic [31:28] t_type;  // type 4 for itrigger
    logic dmode;
    logic hit;
    logic [25:13] zeroed;
    logic vs;
    logic vu;
    logic nmi;
    logic m;
    logic zero;
    logic s;
    logic u;
    logic [5:0] action;
  } itrigger32_tdata1_t;

  typedef struct packed {
    logic [31:28] t_type;  // type 5 for etrigger
    logic dmode;
    logic hit;
    logic [25:13] zeroes;
    logic vs;
    logic vu;
    logic zeroed;
    logic m;
    logic zero;
    logic s;
    logic u;
    logic [5:0] action;
  } etrigger32_tdata1_t;

  typedef union packed {
    logic [31:0] tdata1_type;
    mcontrol6_32_tdata1_t mc6_type;
    etrigger32_tdata1_t etrigger_type;
    itrigger32_tdata1_t itrigger_type;
    icount32_tdata1_t icount_type;
  } trigger_32_tdata1_type;

  // NAPOT range match, per the encoding of the privileged specification (table
  // "NAPOT range encoding in PMP address and configuration registers"): the
  // value is the base address followed by a run of low ones, and n trailing
  // ones select a range of 2^(n+1) bytes. Only the bits above the run take
  // part in the comparison.
  //
  // The address bits above the run are free, so no validity check applies; and
  // the run of n ones has to mask off n + 1 bits, the range being twice the
  // weight of the lowest zero. This matches what cva6's own PMP does in
  // core/pmp/src/pmp_entry.sv and what Spike does in triggers.cc.
  function automatic logic napot_match32(logic [31:0] base, logic [31:0] value);
    logic [31:0] mask;
    int unsigned trailing_ones;

    trailing_ones = 0;
    for (int unsigned i = 0; i < 32; i++) begin
      if (base[i]) trailing_ones = i + 1;
      else break;
    end

    mask = ~((32'd1 << (trailing_ones + 1)) - 32'd1);
    return (value & mask) == (base & mask);
  endfunction

  // NAPOT range match, per the encoding of the privileged specification (table
  // "NAPOT range encoding in PMP address and configuration registers"): the
  // value is the base address followed by a run of low ones, and n trailing
  // ones select a range of 2^(n+1) bytes. Only the bits above the run take
  // part in the comparison.
  //
  // The address bits above the run are free, so no validity check applies; and
  // the run of n ones has to mask off n + 1 bits, the range being twice the
  // weight of the lowest zero. This matches what cva6's own PMP does in
  // core/pmp/src/pmp_entry.sv and what Spike does in triggers.cc.
  function automatic logic napot_match64(logic [63:0] base, logic [63:0] value);
    logic [63:0] mask;
    int unsigned trailing_ones;

    trailing_ones = 0;
    for (int unsigned i = 0; i < 64; i++) begin
      if (base[i]) trailing_ones = i + 1;
      else break;
    end

    mask = ~((64'd1 << (trailing_ones + 1)) - 64'd1);
    return (value & mask) == (base & mask);
  endfunction

  function automatic logic match_scontext32(input logic [31:0] scontext, input logic [1:0] sselect,
                                            input logic [1:0] sbytemask, input logic [15:0] svalue,
                                            input logic flag);
    logic match;
    int   max_bytes = 0;
    match = 1'b1;
    if (sselect == 2'd1) begin
      max_bytes = (flag) ? 4 : 2;
      for (int b = 0; b < max_bytes; b++) begin
        if (!sbytemask[b]) begin
          if (scontext[8*b+:8] != svalue[8*b+:8]) match = 1'b0;
        end
      end
    end else match = 1'b0;
    return match;
  endfunction

  function automatic logic match_scontext64(input logic [31:0] scontext, input logic [1:0] sselect,
                                            input logic [3:0] sbytemask, input logic [31:0] svalue,
                                            input logic flag);
    logic match;
    int   max_bytes = 0;
    match = 1'b1;
    if (sselect == 2'd1) begin
      max_bytes = (flag) ? 4 : 2;
      for (int b = 0; b < max_bytes; b++) begin
        if (!sbytemask[b]) begin
          if (scontext[8*b+:8] != svalue[8*b+:8]) match = 1'b0;
        end
      end
    end else match = 1'b0;
    return match;
  endfunction


endpackage

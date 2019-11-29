///////////////////////////////////////////////
// unsigned division test

// init
NumStim_T   = 6+1000;

TestName_T  = "urem test";

AcqTrig_T     <= 1;
applWaitCyc(Clk_CI,2);
AcqTrig_T     <= 0;
applWaitCyc(Clk_CI,2);

///////////////////////////////////////////////

OpBSign_SI  = 0;
OpCode_SI   = 2;

OpA_T       = 100;
OpB_T       = 2;

OpA_DI      = OpA_T;
OpBShift_DI = 32-$clog2(OpB_T+1);
OpB_DI      = OpB_T << OpBShift_DI;
InVld_SI    = 1;

applWaitCyc(Clk_CI,1);
////////////////////
applWait(Clk_CI, OutVld_SO);

InVld_SI    = 0;

OpA_T       = 2**32-1;
OpB_T       = 1;

OpA_DI      = OpA_T;
OpBShift_DI = 32-$clog2(OpB_T+1);
OpB_DI      = OpB_T << OpBShift_DI;
InVld_SI    = 1;

applWaitCyc(Clk_CI,1);
////////////////////
applWait(Clk_CI, OutVld_SO);

InVld_SI    = 0;

OpA_T       = 1;
OpB_T       = 2**32-1;

OpA_DI      = OpA_T;
OpBShift_DI = 32-$clog2(OpB_T+1);
OpB_DI      = OpB_T << OpBShift_DI;
InVld_SI    = 1;

applWaitCyc(Clk_CI,1);
////////////////////
applWait(Clk_CI, OutVld_SO);

InVld_SI    = 0;

OpA_T       = 0;
OpB_T       = 5456;

OpA_DI      = OpA_T;
OpBShift_DI = 32-$clog2(OpB_T+1);
OpB_DI      = OpB_T << OpBShift_DI;
InVld_SI    = 1;

applWaitCyc(Clk_CI,1);
////////////////////
applWait(Clk_CI, OutVld_SO);

InVld_SI    = 0;

OpA_T       = 875;
OpB_T       = 0;

OpA_DI      = OpA_T;
OpBShift_DI = 32-$clog2(OpB_T+1);
OpB_DI      = OpB_T << OpBShift_DI;
InVld_SI    = 1;

applWaitCyc(Clk_CI,1);
////////////////////
applWait(Clk_CI, OutVld_SO);

InVld_SI    = 0;

OpA_T       = 0;
OpB_T       = 0;

OpA_DI      = OpA_T;
OpBShift_DI = 32-$clog2(OpB_T+1);
OpB_DI      = OpB_T << OpBShift_DI;
InVld_SI    = 1;

applWaitCyc(Clk_CI,1);

applWait(Clk_CI, OutVld_SO);
InVld_SI    = 0;

////////////////////
// a couple of random stimuli

for (k = 0; k < 1000; k++) begin

  applWait(Clk_CI, OutVld_SO);

  ok = randomize(OpA_T) with {OpA_T>=0; OpA_T<=2**C_WIDTH-1;};
  ok = randomize(OpB_T) with {OpB_T>=0; OpB_T<=2**C_WIDTH-1;};

  OpA_DI      = OpA_T;
  OpBShift_DI = 32-$clog2(OpB_T+1);
  OpB_DI      = OpB_T << OpBShift_DI;
  InVld_SI    = 1;

  applWaitCyc(Clk_CI,1);
  applWait(Clk_CI, OutVld_SO);

  InVld_SI    = 0;

end

applWaitCyc(Clk_CI,100);
///////////////////////////////////////////////

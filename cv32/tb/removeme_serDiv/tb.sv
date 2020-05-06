///////////////////////////////////////////////////////////////////////////////
// File       : TB for Simple Serial Divider
// Ver        : 1.0
// Date       : 15.03.2016
///////////////////////////////////////////////////////////////////////////////
//
// Description: this is a simple serial divider for signed integers (int32).
//
///////////////////////////////////////////////////////////////////////////////
//
// Authors    : Michael Schaffner (schaffner@iis.ee.ethz.ch)
//              Andreas Traber    (traber@iis.ee.ethz.ch)
//
// Copyright (c) 2016 Integrated Systems Laboratory, ETH Zurich
///////////////////////////////////////////////////////////////////////////////


// tb package
module tb;

  // leave this
  timeunit 1ps;
  timeprecision 1ps;

///////////////////////////////////////////////////////////////////////////////
// MUT signal declarations
///////////////////////////////////////////////////////////////////////////////
  time C_CLK_HI               = 5ns;     // set clock high time
  time C_CLK_LO               = 5ns;     // set clock low time
  time C_APPL_DEL             = 2ns;     // set stimuli application delay
  time C_ACQ_DEL              = 8ns;     // set response acquisition delay

  parameter C_WIDTH           = 32;
  parameter C_LOG_WIDTH       = 6;

  longint                 OpA_T, OpA_tmp;
  longint                 OpB_T, OpB_tmp;

  logic [C_WIDTH-1:0]     OpA_DI;
  logic [C_WIDTH-1:0]     OpB_DI;
  logic [C_LOG_WIDTH-1:0] OpBShift_DI;
  logic                   OpBIsZero_SI;

  logic                   OpBSign_SI;
  logic [1:0]             OpCode_SI;
  logic [1:0]             OpCode_tmp;

  logic                   InVld_SI;

  logic                   OutRdy_SI;
  logic                   OutVld_SO;
  logic [C_WIDTH-1:0]     Res_DO;

///////////////////////////////////////////////////////////////////////////////
// TB signal declarations
///////////////////////////////////////////////////////////////////////////////

  logic   Clk_CI, Rst_RBI;
  logic   StimStart_T, StimEnd_T, EndOfSim_T;
  longint NumStim_T;
  logic   AcqTrig_T;
  string  TestName_T;

///////////////////////////////////////////////////////////////////////////////
// use to ensure proper ATI timing
///////////////////////////////////////////////////////////////////////////////

  task automatic applWaitCyc(ref logic Clk_C, input int unsigned n);
     if (n > 0)
     begin
       repeat (n) @(posedge(Clk_C));
       #(C_APPL_DEL);
     end
  endtask

  task automatic acqWaitCyc(ref logic Clk_C, input int unsigned n);
     if (n > 0)
     begin
       repeat (n) @(posedge(Clk_C));
       #(C_ACQ_DEL);
     end
  endtask

  task automatic applWait(ref logic Clk_C, ref logic SigToWaitFor_S);
     do begin
       @(posedge(Clk_C));
       #(C_APPL_DEL);
     end while(SigToWaitFor_S == 1'b0);
  endtask

  task automatic acqWait(ref logic Clk_C, ref logic SigToWaitFor_S);
     do begin
       @(posedge(Clk_C));
       #(C_ACQ_DEL);
     end while(SigToWaitFor_S == 1'b0);
  endtask

  task automatic acqWait2(ref logic Clk_C, ref logic SigToWaitFor_S, ref logic SigToWaitFor2_S);
     do begin
       @(posedge(Clk_C));
       #(C_ACQ_DEL);
     end while(SigToWaitFor_S == 1'b0 || SigToWaitFor2_S == 1'b0);
  endtask


///////////////////////////////////////////////////////////////////////////////
// Clock Process
///////////////////////////////////////////////////////////////////////////////

  always @*
  begin
    do begin
      Clk_CI = 1; #(C_CLK_HI);
      Clk_CI = 0; #(C_CLK_LO);
    end while (EndOfSim_T == 1'b0);
    // generate one extra cycle to allow response acquisition to complete
    Clk_CI = 1; #(C_CLK_HI);
    Clk_CI = 0; #(C_CLK_LO);
  end


///////////////////////////////////////////////////////////////////////////////
// MUT
///////////////////////////////////////////////////////////////////////////////


  assign OpBIsZero_SI = ~(|OpB_DI);
  riscv_alu_div #(.C_WIDTH(C_WIDTH), .C_LOG_WIDTH(C_LOG_WIDTH)) i_mut (.*);

///////////////////////////////////////////////////////////////////////////////
// application process
///////////////////////////////////////////////////////////////////////////////

  initial   // process runs just once
  begin : p_stim

    longint signed k, j, i;
    bit ok, randBit;

    StimStart_T = 0;
    StimEnd_T   = 0;
    NumStim_T   = 0;
    TestName_T  = "";
    AcqTrig_T   = 0;

    Rst_RBI     = 0;

    OpA_T       = 0;
    OpB_T       = 0;

    OpA_DI      = 0;
    OpB_DI      = 0;
    OpBShift_DI = 0;
    OpBSign_SI  = 0;
    OpCode_SI   = 0;
    InVld_SI    = 0;

    applWaitCyc(Clk_CI,100);

    Rst_RBI <= 1'b1;

    applWaitCyc(Clk_CI,100);


    $display("stimuli application started");
    StimStart_T <= 1'b1;
    applWaitCyc(Clk_CI,100);

    ///////////////////////////////////////////////
    // unsigned division test

    `include "tb_udiv.sv"

    ///////////////////////////////////////////////
    // unsigned modulo test

    `include "tb_urem.sv"

    ///////////////////////////////////////////////
    // signed div test

    `include "tb_div.sv"

    ///////////////////////////////////////////////
    // signed div test

    `include "tb_rem.sv"

    ///////////////////////////////////////////////

    applWaitCyc(Clk_CI,400);

    StimEnd_T <= 1;
    $display("stimuli application ended");

  end


///////////////////////////////////////////////////////////////////////////////
// acquisition process
///////////////////////////////////////////////////////////////////////////////


  initial   // process runs just once
  begin : p_acq

    ///////////////////////////////////////////////
    // define vars, init...
    ///////////////////////////////////////////////

    longint acqCnt, errCnt, res, act;

    OutRdy_SI  = 0;
    EndOfSim_T = 0;

    acqWait(Clk_CI,StimStart_T);

    $display("response acquisition started");

    ///////////////////////////////////////////////
    // acquisiton and verification
    ///////////////////////////////////////////////


    while (1)
    begin

      // wait for acquisition trigger
      do begin
        acqWaitCyc(Clk_CI,1);
        if (StimEnd_T == 1)
        begin
          EndOfSim_T <= 1;
          $display("response acquisition ended");
          $finish();
        end
      end while(AcqTrig_T == 1'b0);

      acqCnt = 0;

      $display("");
      $display("------------------------------------------------");
      $display("%s", TestName_T);
      $display("------------------------------------------------");
      $display("");

      $display("checking %00d vectors",NumStim_T);
      $display("");

      do begin

        OutRdy_SI = 1'b1;

        applWait(Clk_CI, InVld_SI);

        OpCode_tmp = OpCode_SI;
        OpA_tmp = OpA_T;
        OpB_tmp = OpB_T;

        //////////////////////////
        // udiv / udiv
        if(OpCode_SI[1] == 1'b0)
        begin

          res = OpA_tmp/OpB_tmp;

          if((OpB_tmp == 0) && (OpCode_SI[0] == 0))
          begin
            res = 2**C_WIDTH-1;
          end
          else if ((OpB_tmp == 0) && (OpCode_SI[0] == 1'b1))
          begin
            res = -1;
          end
          else if ((OpA_tmp == -(2**(C_WIDTH-1)))  && (OpB_tmp == -1) && (OpCode_SI[0] == 1'b1))
          begin
            res = -(2**(C_WIDTH-1));
          end

          acqWait(Clk_CI, OutVld_SO);

          // interpret result correctly!
          if (OpCode_tmp[0] == 1'b1)
            act = $signed(Res_DO);
          else
            act = $unsigned(Res_DO);

          if(res !== act)
          begin
            $display("vector %d> %d / %d = %d != %d -> error!",acqCnt,OpA_tmp,OpB_tmp,res,act);
            errCnt++;
            $stop();
          end else
          begin
            $display("vector %d> %d / %d = %d == %d ",acqCnt,OpA_tmp,OpB_tmp,res,act);
          end
        //////////////////////////
        // rem / urem
        end else if(OpCode_SI[1] == 1'b1)
        begin

          res = OpA_tmp % OpB_tmp;

          if((OpB_tmp == 0))
          begin
            res = OpA_tmp;
          end

          acqWait(Clk_CI, OutVld_SO);

          // interpret result correctly!
          if (OpCode_tmp[0] == 1'b1)
            act = $signed(Res_DO);
          else
            act = $unsigned(Res_DO);

          if(res !== act)
          begin
            $display("vector %d> %d mod %d = %d != %d -> error!",acqCnt,OpA_tmp,OpB_tmp, res,act);
            errCnt++;
            $stop();
          end else
          begin
            $display("vector %d> %d mod %d = %d == %d ",acqCnt,OpA_tmp,OpB_tmp,res,act);
          end
        end
        // status
        acqCnt++;
      end
      while (acqCnt < NumStim_T);


    end
    ///////////////////////////////////////////////



    EndOfSim_T <= 1;
    $display("response acquisition ended");
    $finish();
    ///////////////////////////////////////////////

  end

endmodule

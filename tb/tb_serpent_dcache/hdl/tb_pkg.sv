// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// Author: Michael Schaffner <schaffner@iis.ee.ethz.ch>, ETH Zurich
// Date: 15.08.2018
// Description: testbench package with some helper functions.


package tb_pkg;

  // // for abs(double) function
  // import mti_cstdlib::*;

  // for timestamps
  import "DPI-C" \time = function int _time (inout int tloc[4]);
  import "DPI-C" function string ctime(inout int tloc[4]);

///////////////////////////////////////////////////////////////////////////////
// parameters
///////////////////////////////////////////////////////////////////////////////

  // creates a 10ns ATI timing cycle
  time CLK_HI               = 5ns;     // set clock high time
  time CLK_LO               = 5ns;     // set clock low time
  time CLK_PERIOD           = CLK_HI+CLK_LO;
  time APPL_DEL             = 2ns;     // set stimuli application delay
  time ACQ_DEL              = 8ns;     // set response aquisition delay

  parameter ERROR_CNT_STOP_LEVEL = 1; // use 1 for debugging. 0 runs the complete simulation...

  // tb_readport sequences
  typedef enum logic [2:0] { RANDOM_SEQ, LINEAR_SEQ, BURST_SEQ, IDLE_SEQ, WRAP_SEQ } seq_t;

///////////////////////////////////////////////////////////////////////////////
// progress
///////////////////////////////////////////////////////////////////////////////

  class progress;
    real newState, oldState;
    longint numResp, acqCnt, errCnt, totAcqCnt, totErrCnt;
    string name;

    function new(string name);
      begin
          this.name     = name;
          this.acqCnt   = 0;
          this.errCnt   = 0;
          this.newState = 0.0;
          this.oldState = 0.0;
          this.numResp  = 1;
          this.totAcqCnt = 0;
          this.totErrCnt = 0;

      end
    endfunction : new

    function void reset(longint numResp_);
      begin
          this.acqCnt   = 0;
          this.errCnt   = 0;
          this.newState = 0.0;
          this.oldState = 0.0;
          this.numResp  = numResp_;
      end
    endfunction : reset

    function void addRes(int isError);
      begin
          this.acqCnt++;
          this.totAcqCnt++;
          this.errCnt += isError;
          this.totErrCnt += isError;

          if(ERROR_CNT_STOP_LEVEL <= this.errCnt && ERROR_CNT_STOP_LEVEL > 0) begin
            $error("%s> simulation stopped (ERROR_CNT_STOP_LEVEL = %d reached).", this.name, ERROR_CNT_STOP_LEVEL);
            $stop();
          end
      end
    endfunction : addRes

    function void print();
      begin
        this.newState = $itor(this.acqCnt) / $itor(this.numResp);
        if(this.newState - this.oldState >= 0.01) begin
          $display("%s> validated %03d%% -- %01d failed (%03.3f%%) ",
                  this.name,
                  $rtoi(this.newState*100.0),
                  this.errCnt,
                  $itor(this.errCnt) / $itor(this.acqCnt) * 100.0);
          // $fflush();
          this.oldState = this.newState;
        end
      end
    endfunction : print

    function void printToFile(string file, bit summary = 0);
      begin
        int fptr;

        // sanitize string
        for(fptr=0; fptr<$size(file);fptr++) begin
          if(file[fptr] == " " || file[fptr] == "/" || file[fptr] == "\\") begin
            file[fptr] = "_";
          end
        end


        fptr = $fopen(file,"w");
        if(summary) begin
          $fdisplay(fptr, "Simulation Summary of %s", this.name);
          $fdisplay(fptr, "total: %01d of %01d vectors failed (%03.3f%%) ",
                    this.totErrCnt,
                    this.totAcqCnt,
                    $itor(this.totErrCnt) / ($itor(this.totAcqCnt) * 100.0 + 0.000000001));
          if(this.totErrCnt == 0) begin
            $fdisplay(fptr, "CI: PASSED");
          end else begin
            $fdisplay(fptr, "CI: FAILED");
          end
        end else begin
          $fdisplay(fptr, "test name: %s", file);
          $fdisplay(fptr, "this test: %01d of %01d vectors failed (%03.3f%%) ",
                    this.errCnt,
                    this.acqCnt,
                    $itor(this.errCnt) / $itor(this.acqCnt) * 100.0);

          $fdisplay(fptr, "total so far: %01d of %01d vectors failed (%03.3f%%) ",
                    this.totErrCnt,
                    this.totAcqCnt,
                    $itor(this.totErrCnt) / $itor(this.totAcqCnt) * 100.0);
        end
        $fclose(fptr);
      end
    endfunction : printToFile

  endclass : progress

endpackage : tb_pkg


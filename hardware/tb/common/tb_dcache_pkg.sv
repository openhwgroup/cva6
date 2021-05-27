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
  typedef enum logic [2:0] { RANDOM_SEQ, LINEAR_SEQ, BURST_SEQ, IDLE_SEQ, WRAP_SEQ, SET_SEQ, CONST_SEQ } seq_t;

  typedef enum logic [1:0] { OTHER, BYPASS, CACHED } port_type_t;

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

///////////////////////////////////////////////////////////////////////////////
// memory emulation
///////////////////////////////////////////////////////////////////////////////

  class tb_mem_port #(
    parameter string MEM_NAME = "TB_MEM",
    // AXI interface parameters
    parameter int   AW = 32,
    parameter int   DW = 32,
    parameter int   IW = 8,
    parameter int   UW = 1,
    // Stimuli application and test time
    parameter time  TA = 0ps,
    parameter time  TT = 0ps,
    // Upper and lower bounds on wait cycles on Ax, W, and resp (R and B) channels
    parameter int   AX_MIN_WAIT_CYCLES   = 0,
    parameter int   AX_MAX_WAIT_CYCLES   = 100,
    parameter int   R_MIN_WAIT_CYCLES    = 0,
    parameter int   R_MAX_WAIT_CYCLES    = 5,
    parameter int   RESP_MIN_WAIT_CYCLES = 0,
    parameter int   RESP_MAX_WAIT_CYCLES = 20,
    parameter int   MEM_BYTES            = 512 * 1024
    );
    typedef axi_test::axi_driver #(
      .AW(AW), .DW(DW), .IW(IW), .UW(UW), .TA(TA), .TT(TT)
    ) axi_driver_t;
    typedef rand_id_queue_pkg::rand_id_queue #(
      .data_t   (axi_driver_t::ax_beat_t),
      .ID_WIDTH (IW)
    ) rand_ax_beat_queue_t;
    typedef axi_driver_t::ax_beat_t ax_beat_t;
    typedef axi_driver_t::b_beat_t b_beat_t;
    typedef axi_driver_t::r_beat_t r_beat_t;
    typedef axi_driver_t::w_beat_t w_beat_t;

    typedef logic [AW-1:0] addr_t;
    typedef logic [7:0]    byte_t;

    port_type_t          port_type;
    string               port_name;
    int unsigned         min_paddr;
    int unsigned         max_paddr;
    axi_driver_t         drv;
    rand_ax_beat_queue_t ar_queue;
    ax_beat_t            aw_queue[$];
    int unsigned         b_wait_cnt;

    static byte_t memory_q[MEM_BYTES-1:0]; // Main memory
    static byte_t shadow_q[MEM_BYTES-1:0]; // Shadow of main memory for verification.

    static progress status;

    function new(
      virtual AXI_BUS_DV #(
      .AXI_ADDR_WIDTH(AW),
      .AXI_DATA_WIDTH(DW),
      .AXI_ID_WIDTH(IW),
      .AXI_USER_WIDTH(UW)
      ) axi,
      port_type_t port_type
    );
      this.port_type = port_type;
      if      (port_type == BYPASS) this.port_name = "Bypassed";
      else if (port_type == CACHED) this.port_name = "Cached";
      else                          this.port_name = "";
      this.drv = new(axi);
      this.ar_queue = new;
      this.b_wait_cnt = 0;
      this.min_paddr = 0;
      this.max_paddr = 1<<MEM_BYTES;
      this.reset();
    endfunction

    function void reset();
      this.drv.reset_slave();
    endfunction

    // Set the memory region this port is expected to access. Accesses outside this region will
    // throw an error.
    function void set_region(int unsigned min_paddr, int unsigned max_paddr);
      this.min_paddr = min_paddr;
      this.max_paddr = max_paddr;
    endfunction

    // Initialize shadow and real memory with identical random values
    static function void init_mem();
      automatic byte_t val;
      for (int k=0; k<MEM_BYTES; k++) begin
        void'(std::randomize(val));
        memory_q[k] <= val;
        shadow_q[k] <= val;
      end
      status = new(MEM_NAME);
    endfunction

    // Crosscheck whether shadow and real memory arrays still match
    static function void check_mem();
      bit ok;
      status.reset(MEM_BYTES);
      for(int k=0; k<MEM_BYTES; k++) begin
        ok = (memory_q[k] == shadow_q[k]);
        if(!ok) begin
          $display("%s> mismatch at k=%016X: real[k>>3]=%016X, shadow[k>>3]=%016X",
            MEM_NAME, k, memory_q[k], shadow_q[k]);
        end
        status.addRes(!ok);
        status.print();
      end
    endfunction

    static function void report_mem();
      status.printToFile({MEM_NAME, "_summary.rep"}, 1);

      if(status.totErrCnt == 0) begin
        $display("%s> ----------------------------------------------------------------------", MEM_NAME);
        $display("%s> PASSED %0d VECTORS", MEM_NAME, status.totAcqCnt);
        $display("%s> ----------------------------------------------------------------------\n", MEM_NAME);
      end else begin
        $display("%s> ----------------------------------------------------------------------\n", MEM_NAME);
        $display("%s> FAILED %0d OF %0d VECTORS\n", MEM_NAME , status.totErrCnt, status.totAcqCnt);
        $display("%s> ----------------------------------------------------------------------\n", MEM_NAME);
      end
    endfunction

    task automatic rand_wait(input int unsigned min, max);
      int unsigned rand_success, cycles;
      rand_success = std::randomize(cycles) with {
      cycles >= min;
      cycles <= max;
      };
      assert (rand_success) else $error("Failed to randomize wait cycles!");
      repeat (cycles) @(posedge this.drv.axi.clk_i);
    endtask

    task recv_ars();
      forever begin
        automatic ax_beat_t ar_beat;
        rand_wait(AX_MIN_WAIT_CYCLES, AX_MAX_WAIT_CYCLES);
        drv.recv_ar(ar_beat);
        assert (ar_beat.ax_burst != axi_pkg::BURST_WRAP) else
        $error("axi_pkg::BURST_WRAP not supported.");
        ar_queue.push(ar_beat.ax_id, ar_beat);
      end
    endtask

    task send_rs();
      forever begin
        automatic logic     rand_success;
        automatic ax_beat_t ar_beat;
        automatic r_beat_t  r_beat = new;
        automatic addr_t    byte_addr;

        // Receive AR
        // automatic byte_t   byte_data;
        wait (!ar_queue.empty());
        ar_beat    = ar_queue.peek();
        byte_addr  = (ar_beat.ax_addr >> $clog2(DW/8)) << $clog2(DW/8);

        assert (min_paddr != max_paddr && byte_addr inside {[min_paddr:max_paddr]}) else
        $error("%s read out of bounds. Address: %16X -- Permitted region: %16X--%16X", port_name, byte_addr, min_paddr, max_paddr);

        // Prepare R
        // Read from real memory
        for (int unsigned i = 0; i < (DW/8); i++) begin
          r_beat.r_data[i*8+:8] = memory_q[byte_addr];
          byte_addr++;
        end
        r_beat.r_resp = axi_pkg::RESP_OKAY;
        r_beat.r_id  = ar_beat.ax_id;

        if (ar_beat.ax_lock)
          r_beat.r_resp[0]= $random();
        rand_wait(R_MIN_WAIT_CYCLES, R_MAX_WAIT_CYCLES);
        if (ar_beat.ax_len == '0) begin
          r_beat.r_last = 1'b1;
          void'(ar_queue.pop_id(ar_beat.ax_id));
        end else begin
          if (ar_beat.ax_burst == axi_pkg::BURST_INCR) begin
          ar_beat.ax_addr = ((ar_beat.ax_addr >> ar_beat.ax_size) << ar_beat.ax_size) +
                      2**ar_beat.ax_size;
          end
          ar_beat.ax_len--;
          ar_queue.set(ar_beat.ax_id, ar_beat);
        end
        drv.send_r(r_beat);
      end
    endtask

    task recv_aws();
      forever begin
        automatic ax_beat_t aw_beat;
        rand_wait(AX_MIN_WAIT_CYCLES, AX_MAX_WAIT_CYCLES);
        drv.recv_aw(aw_beat);
        assert (aw_beat.ax_atop == '0) else
          $error("ATOP not supported.");
        assert (aw_beat.ax_burst != axi_pkg::BURST_WRAP) else
          $error("axi_pkg::BURST_WRAP not supported.");
        aw_queue.push_back(aw_beat);
        // Atomic{Load,Swap,Compare}s require an R response.
        if (aw_beat.ax_atop[5]) begin
          ar_queue.push(aw_beat.ax_id, aw_beat);
        end
      end
    endtask

    task recv_ws();
      forever begin
        automatic ax_beat_t aw_beat;
        automatic addr_t  byte_addr;
        forever begin
          automatic w_beat_t w_beat;
          rand_wait(RESP_MIN_WAIT_CYCLES, RESP_MAX_WAIT_CYCLES);
          drv.recv_w(w_beat);
          wait (aw_queue.size() > 0);
          aw_beat = aw_queue[0];
          byte_addr  = (aw_beat.ax_addr >> $clog2(DW/8)) << $clog2(DW/8);

          assert (min_paddr != max_paddr && byte_addr inside {[min_paddr:max_paddr]}) else
          $error("%s write out of bounds. Address: %16X -- Permitted region: %16X--%16X", port_name, byte_addr, min_paddr, max_paddr);

          // Write data to real memory if the strobe is defined
          for (int unsigned i = 0; i < (DW/8); i++) begin
            if (w_beat.w_strb[i]) begin
              memory_q[byte_addr] = w_beat.w_data[i*8+:8];
            end
            byte_addr++;
          end
          // Update address in beat
          if (aw_beat.ax_burst == axi_pkg::BURST_INCR) begin
            aw_beat.ax_addr = ((aw_beat.ax_addr >> aw_beat.ax_size) << aw_beat.ax_size) +
                      2**aw_beat.ax_size;
          end
          aw_queue[0] = aw_beat;
          if (w_beat.w_last)
            break;
        end
        b_wait_cnt++;
      end
    endtask

    task send_bs();
      forever begin
        automatic ax_beat_t aw_beat;
        automatic b_beat_t b_beat = new;
        automatic logic rand_success;
        wait (b_wait_cnt > 0 && (aw_queue.size() != 0));
        aw_beat = aw_queue.pop_front();
        rand_success = std::randomize(b_beat); assert(rand_success);
        b_beat.b_id = aw_beat.ax_id;
        if (aw_beat.ax_lock) begin
          b_beat.b_resp[0]= $random();
        end
        rand_wait(RESP_MIN_WAIT_CYCLES, RESP_MAX_WAIT_CYCLES);
        b_beat.b_resp = axi_pkg::RESP_OKAY;
        drv.send_b(b_beat);
        b_wait_cnt--;
      end
    endtask

    task run();
      fork
      recv_ars();
      send_rs();
      recv_aws();
      recv_ws();
      send_bs();
      join
    endtask

  endclass : tb_mem_port

endpackage : tb_pkg


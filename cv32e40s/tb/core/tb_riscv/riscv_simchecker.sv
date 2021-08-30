// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

//////////////////////////////////////////////////////////////////////////////////////////////
// Engineer:       Andreas Traber - atraber@iis.ee.ethz.ch                                  //
//                                                                                          //
// Additional contributions by:                                                             //
//                 Francesco Minervini - minervif@student.ethz.ch                           //
//                                                                                          //
// Design Name:    RISC-V Simchecker                                                        //
// Project Name:   RI5CY                                                                    //
// Language:       SystemVerilog                                                            //
//                                                                                          //
// Description:    Compares the executed instructions with a golden model                   //
//                                                                                          //
//////////////////////////////////////////////////////////////////////////////////////////////
`ifndef VERILATOR
`include "riscv_config.sv"

import riscv_defines::*;

// do not import anything if the simchecker is not used
// this gets rid of warnings during simulation
import "DPI-C" function chandle riscv_checker_init(input int boot_addr, input int core_id, input int cluster_id, input string name);
import "DPI-C" function int     riscv_checker_step(input chandle cpu, input longint simtime, input int cycle, input logic [31:0] pc, input logic [31:0] instr);
import "DPI-C" function void    riscv_checker_irq(input chandle cpu, input int irq, input int irq_no);
import "DPI-C" function void    riscv_checker_mem_access(input chandle cpu, input int we, input logic [31:0] addr, input logic [31:0] data);
import "DPI-C" function void    riscv_checker_reg_access(input chandle cpu, input logic [31:0] addr, input logic [31:0] data);

module riscv_simchecker
(
  // Clock and Reset
  input  logic        clk,
  input  logic        rst_n,

  input  logic        fetch_enable,
  input  logic [31:0] boot_addr,
  input  logic [3:0]  core_id,
  input  logic [5:0]  cluster_id,

  input  logic [15:0] instr_compressed,
  input  logic        if_valid,
  input  logic        pc_set,

  input  logic [31:0] pc,
  input  logic [31:0] instr,
  input  logic        is_compressed,
  input  logic        id_valid,
  input  logic        is_decoding,
  input  logic        is_illegal,
  input  logic        is_interrupt,
  input  logic [4:0]  irq_no,
  input  logic        pipe_flush,
  input  logic        irq_i,
  input  logic        is_mret,

  input  logic        int_enable,

  //Signals added for FPU ops
  input  logic        lsu_ready_wb,
  input  logic        apu_ready_wb,
  input  logic        wb_contention,

  input  logic        apu_en_id,
  input  logic        apu_req,
  input  logic        apu_gnt,
  input  logic        apu_valid,
  input  logic        apu_singlecycle,
  input  logic        apu_multicycle,
  input  logic [1:0]  apu_latency,
  input  logic        apu_active,
  input  logic        apu_en_ex,
////////////////////////////////////////////
  input  logic        ex_valid,
  input  logic [ 5:0] ex_reg_addr,

  input  logic        ex_reg_we,
  input  logic [31:0] ex_reg_wdata,

  input  logic        ex_data_req,
  input  logic        ex_data_gnt,
  input  logic        ex_data_we,
  input  logic [31:0] ex_data_addr,
  input  logic [31:0] ex_data_wdata,

  input  logic        lsu_misaligned,
  input  logic        wb_bypass,

  input  logic        wb_valid,
  input  logic [ 5:0] wb_reg_addr,

  input  logic        wb_reg_we,
  input  logic [31:0] wb_reg_wdata,

  input  logic        wb_data_rvalid,
  input  logic [31:0] wb_data_rdata


);

  // DPI stuff
  chandle dpi_simdata;

  // SV-only stuff
  typedef struct {
    logic [ 5:0] addr;
    logic [31:0] value;
  } reg_t;

  typedef struct {
    logic [31:0] addr;
    logic        we;
    logic [ 3:0] be;
    logic [31:0] wdata;
    logic [31:0] rdata;
  } mem_acc_t;

  class instr_trace_t;
    time         simtime;
    int          cycles;
    logic [31:0] pc;
    logic [31:0] instr;
    logic        irq;
    logic [ 4:0] irq_no;
    logic        wb_bypass;
    logic        fpu_first;
    int          next_wait;
    reg_t        regs_write[$];
    mem_acc_t    mem_access[$];

    function new ();
      irq        = 1'b0;
      wb_bypass  = 1'b1;
      fpu_first  = 1'b0;
      next_wait = 0;
      regs_write = {};
      mem_access = {};
    endfunction
  endclass


  mailbox rdata_stack = new (4);
  integer rdata_writes = 0;

  integer      cycles;
  integer      mismatch=0;
  logic       pipe_wait;
  logic       fpu_in_ex;
  int      fp_completed;
  int          fp_ended;
  int       instr_is_valid;

  logic [15:0] instr_compressed_id;
  logic        is_irq_if, is_irq_id;
  logic [ 4:0] irq_no_id, irq_no_if;
  logic apu_req_accepted;
  logic apu_res_on_alu_port;
  logic apu_res_on_lsu_port;
  logic enable = 0;
  logic [ 1:0] apu_lat;

  instr_trace_t instr_queue[$];

  localparam SIMCHECKER_VERBOSE = 0;

  mailbox instr_ex = new (4);
  mailbox instr_wb = new (4);
  mailbox fpu_active = new (4);
  mailbox fpu_ex = new (4);
  mailbox fpu_wb = new (4);
  mailbox fpu_done = new (4);
  mailbox fpu_end  = new (4);
  mailbox instr_wait = new (4);

  mailbox fpu_wait = new (4);

  // simchecker initialization
  initial
  begin

      enable = 1'b1;
      pipe_wait = 1'b0;
      fpu_in_ex = 1'b0;
      fp_completed = 0;
      fp_ended = 0;
      instr_is_valid = 0;
      instr_queue = {};
      wait(rst_n == 1'b1);
      wait(fetch_enable == 1'b1);

      dpi_simdata = riscv_checker_init(boot_addr, core_id, cluster_id, "riscyv2");

  end

  // virtual ID/EX pipeline
  initial
  begin

      instr_trace_t trace;
      mem_acc_t     mem_acc;
      reg_t         reg_write;

      while(1) begin
        instr_ex.get(trace);


        // wait until we are going to the next stage
        do begin
          @(negedge clk);

          reg_write.addr  = ex_reg_addr;
          reg_write.value = ex_reg_wdata;

          if(trace.fpu_first == 1'b1) begin  //If the fp operation has been completed, the instruction doesn't have to wait anymore
            if(apu_valid)
              trace.fpu_first = 1'b0;
          end


          if (ex_reg_we) begin
            trace.regs_write.push_back(reg_write);
          end
          // look for data accesses and log them
          if (ex_data_req && ex_data_gnt) begin
            mem_acc.addr = ex_data_addr;
            mem_acc.we   = ex_data_we;


            if (mem_acc.we)
              mem_acc.wdata = ex_data_wdata;
            else
              mem_acc.wdata = 'x;

            trace.mem_access.push_back(mem_acc);
          end
        end while (((!ex_valid || lsu_misaligned) && (!wb_bypass)) || (wb_contention));   //wb_contention is normally low, so it will not stop the process. As soon as there is a contention, this
                                                                                          //condition is true and restart storing values without unlocking the following check process.
        trace.wb_bypass = wb_bypass;

        instr_wb.put(trace);
      end

  end

  // virtual EX/WB pipeline
  initial
  begin

      instr_trace_t trace, fpu_trace;
      reg_t         reg_write;
      logic [31:0]  tmp_discard;
      logic [31:0]  rdata_tmp;

      while(1) begin
        instr_wb.get(trace);

        if (!trace.wb_bypass) begin

            // wait until we are going to the next stage
            do begin
              @(negedge clk);
              #1;


              // pop rdata from stack when there were pending writes
              while(rdata_stack.num() > 0 && rdata_writes > 0) begin
                rdata_writes--;
                rdata_stack.get(tmp_discard);
              end

              if(lsu_ready_wb && !apu_ready_wb) begin
                reg_write.addr = wb_reg_addr;
                reg_write.value = wb_reg_wdata;
                if(wb_reg_we) begin
                  trace.regs_write.push_back(reg_write);
                end
              end

            end while ((!wb_valid) && (!lsu_ready_wb));


            reg_write.addr  = wb_reg_addr;
            reg_write.value = wb_reg_wdata;



          if (wb_reg_we && !apu_valid) begin
              trace.regs_write.push_back(reg_write);
          end

          // take care of rdata
          foreach(trace.mem_access[i]) begin
            if (trace.mem_access[i].we) begin
              // for writes we don't need to wait for the rdata, so if it has
              // not appeared yet, we count it and remove it later from out
              // stack
              if (rdata_stack.num() > 0)
                rdata_stack.get(tmp_discard);
              else
                rdata_writes++;

            end else begin
              if (rdata_stack.num() == 0)
                $warning("rdata stack is empty, but we are waiting for a read");

              if (rdata_writes > 0)
                $warning("rdata_writes is > 0, but we are waiting for a read");

              // indirect addressing workaround for ncsim
              rdata_tmp = trace.mem_access[i].rdata;
              rdata_stack.get(rdata_tmp);
            end
          end
        end


        if(trace.fpu_first == 1'b1) begin  //Check whether one instruction has to wait for the fp operation to be completed, then accumulate all the incoming instructions
          pipe_wait = 1'b1;
          #1;
        end

        if(pipe_wait) begin
          instr_wait.put(trace);

        end else begin

          foreach(trace.mem_access[i]) begin
            if (trace.mem_access[i].we) begin
              //TEMPORARY SOLUTION WITH BYPASS FOR UNINITIALIZED REGISTERS
              if(trace.mem_access[i].wdata === 'X)
                $display("Uninitialized register was met, skip this check");
              else begin
                riscv_checker_mem_access(dpi_simdata, trace.mem_access[i].we, trace.mem_access[i].addr, trace.mem_access[i].wdata);
              end
            end else begin
              riscv_checker_mem_access(dpi_simdata, trace.mem_access[i].we, trace.mem_access[i].addr, trace.mem_access[i].rdata);
            end
          end

          foreach(trace.regs_write[i]) begin
            riscv_checker_reg_access(dpi_simdata, trace.regs_write[i].addr, trace.regs_write[i].value);
          end

          riscv_checker_irq(dpi_simdata, trace.irq, trace.irq_no);

          if (riscv_checker_step(dpi_simdata, trace.simtime, trace.cycles, trace.pc, trace.instr)) begin
            $display("SIMCHECKER: CORE pipeline: Cycle %d at %g ps 0x%x: Cluster %d, Core %d: Mismatch between simulator and RTL detected", trace.cycles, trace.simtime, trace.pc, cluster_id, core_id);
            mismatch ++;
            if(mismatch > 10)
              $stop();
          end
        end
      end
    end





  assign apu_req_accepted = apu_req & apu_gnt;
  assign apu_res_on_alu_port = apu_singlecycle | apu_multicycle;
  assign apu_res_on_lsu_port = (!apu_singlecycle & !apu_multicycle);

  initial
  begin

      instr_trace_t trace;
      while(1) begin
        fpu_active.get(trace);

        if(apu_en_ex) begin    //This is 1 if we already have a fp instruction in execution
          if(~apu_active) begin  //APU is active if there is an unreturned request. If it's low but apu_en_ex is high, we have to wait for the
            apu_lat = apu_latency;  //previous instruction to be done. This depends on the latency of that instruction
            while(apu_lat > 1) begin
              @(negedge clk);
              apu_lat --;
            end

          end else begin
            do begin
              @(negedge clk);
            end while(apu_active);  //APU is active when there is an unreturned request. FPU is still not available for a new operation.
          end
        end

        fpu_ex.put(trace);
      end

  end


  initial  //FPU pipeline: "ID/EX stage"
  begin


      instr_trace_t trace;
      reg_t reg_write;/////////////////////////////////////////////////
      while(1) begin
        fpu_ex.get(trace);

        if(!apu_req_accepted) begin
          do begin
            @(negedge clk);
          end while(!apu_req_accepted);
        end

        if((id_valid && is_decoding) || (pipe_flush && is_decoding) || (is_decoding && is_illegal) || (id_valid && is_mret)) begin
          if(apu_en_id)
            trace.next_wait = 0;
          else  begin

            fpu_in_ex = 1'b1;
            trace.next_wait = 1;
          end
        end else trace.next_wait = 0;

        fpu_wb.put(trace);
      end

  end

  initial  //FPU pipeline: "EX/WB stage"
  begin


      instr_trace_t trace;
      reg_t reg_write;

      while(1) begin
        fpu_wb.get(trace);

        while(!apu_valid) begin
          @(negedge clk);
        end

        if(apu_res_on_lsu_port) begin
          reg_write.addr = wb_reg_addr;
          reg_write.value = wb_reg_wdata;
          if(wb_reg_we) begin

            trace.regs_write.push_back(reg_write);
          end
        end else begin
          if(apu_res_on_alu_port) begin
            reg_write.addr = ex_reg_addr;
            reg_write.value = ex_reg_wdata;
            if(ex_reg_we)
              trace.regs_write.push_back(reg_write);
          end
        end

        fpu_done.put(trace);
      end

  end

  initial  //FPU pipeline: "WB/CHECK STAGE". Call the ISS to check the results
  begin


      instr_trace_t trace;
      while(1) begin
        fpu_done.get(trace);


        foreach(trace.regs_write[i]) begin

          riscv_checker_reg_access(dpi_simdata, trace.regs_write[i].addr, trace.regs_write[i].value);
        end
        if(riscv_checker_step(dpi_simdata, trace.simtime, trace.cycles, trace.pc, trace.instr)) begin
          $display("SIMCHECKER: FPU pipeline: Cycle %d at %g ps 0x%x: Cluster %d, Core %d: Mismatch between simulator and RTL detected", trace.cycles, trace.simtime, trace.pc, cluster_id, core_id);
          mismatch ++;
          if(mismatch > 10)
            $stop();
        end
        #1;


        if(trace.next_wait == 1) begin
          fpu_end.put(1);
        end
        fpu_in_ex = 1'b0;
      end

  end


  initial
  begin

    instr_trace_t trace;

    while(1) begin
      @(negedge clk);
      instr_is_valid = instr_wait.try_get(trace);
      if(instr_is_valid == 1) begin

        instr_queue.push_back(trace);
      end

      fp_completed = fpu_end.try_get(fp_ended);
      if(fp_completed == 1) begin
        foreach(instr_queue[i]) begin
          for (int j = 0; j < instr_queue[i].mem_access.size(); j++) begin
            /* code */
            if(instr_queue[i].mem_access[j].we) begin
              if(instr_queue[i].mem_access[j].wdata === 'X)
                $display("Uninitialized register was met, skip this check");
              else begin
                riscv_checker_mem_access(dpi_simdata, instr_queue[i].mem_access[j].we, instr_queue[i].mem_access[j].addr, instr_queue[i].mem_access[j].wdata);
              end
            end else begin
              riscv_checker_mem_access(dpi_simdata, instr_queue[i].mem_access[j].we, instr_queue[i].mem_access[j].addr, instr_queue[i].mem_access[j].rdata);
            end
          end

          for (int j = 0; j < instr_queue[i].regs_write.size(); j++) begin
            /* code */
            riscv_checker_reg_access(dpi_simdata, instr_queue[i].regs_write[j].addr, instr_queue[i].regs_write[j].value);
          end

          riscv_checker_irq(dpi_simdata, instr_queue[i].irq, instr_queue[i].irq_no);

          if(riscv_checker_step(dpi_simdata, instr_queue[i].simtime, instr_queue[i].cycles, instr_queue[i].pc, instr_queue[i].instr)) begin
            $display("SIMCHECKER: In INSTR QUEUE: CORE pipeline: Cycle %d at %g ps 0x%x: Cluster %d, Core %d: Mismatch between simulator and RTL detected", cycles, instr_queue[i].simtime, instr_queue[i].pc, cluster_id, core_id);
            mismatch ++;
            if(mismatch > 10)
              $stop();
          end
        end

        instr_queue = {};  //Empty the queue, so that is available to accumulate new instructions
        pipe_wait = 1'b0;  //Pipe doesn't have to wait anymore
        fp_completed = 0;
      end
    end
  end


  // cycle counter
  always_ff @(posedge clk, negedge rst_n)
  begin
    if (rst_n == 1'b0)
      cycles = 0;
    else
      cycles = cycles + 1;
  end

  // create rdata stack
  initial
  begin

      while(1) begin
        @(negedge clk);

        if (wb_data_rvalid) begin
          rdata_stack.put(wb_data_rdata);
        end
      end

  end

  always_ff @(enable, posedge clk)
  begin
    if (pc_set) begin
      is_irq_if <= is_interrupt;
      irq_no_if <= irq_no;
    end else if (if_valid) begin
      is_irq_if <= 1'b0;
    end
  end

  always_ff @(enable, posedge clk)
  begin
    if (if_valid) begin
      instr_compressed_id <= instr_compressed;
      is_irq_id           <= is_irq_if;
      irq_no_id           <= irq_no_if;
    end else begin
      is_irq_id           <= is_irq_if;
      irq_no_id           <= irq_no_if;
    end
  end



  // log execution
  initial
  begin

      instr_trace_t trace;

      while(1) begin
        @(negedge clk);

        // - special case for WFI because we don't wait for unstalling there
        // - special case for illegal instructions, since they will not go through
        //   the pipe

        if ((id_valid && is_decoding) || (pipe_flush && is_decoding) || (is_decoding && is_illegal) || (id_valid && is_mret))
        begin
          trace = new ();

          trace.simtime    = $time;
          trace.cycles      = cycles;
          trace.pc         = pc;

          if (is_compressed)
            trace.instr = {instr_compressed_id, instr_compressed_id};
          else
            trace.instr = instr;


            if(is_irq_id) begin
              trace.irq = 1'b1;
              trace.irq_no = irq_no_id;
            end else begin
              if(!int_enable) begin
                trace.irq    = irq_i;
                trace.irq_no = irq_no;
              end
            end
            if(apu_en_id) begin
              fpu_active.put(trace);
            end
            else begin
              #1;
              if(apu_req_accepted && apu_en_ex && ~apu_valid && fpu_in_ex) begin
                trace.fpu_first = 1'b1;    //This means the instruction will go out of the pipeline
              end
              instr_ex.put(trace);
            end
        end
      end
  end

endmodule
`endif

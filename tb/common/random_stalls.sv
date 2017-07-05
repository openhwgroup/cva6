// Author: Andreas Traber, ACP
// Date: 22/02/2016
// Description: Randomly inject stalls in the instruction interface
//
// Copyright (C) 2017 ETH Zurich, University of Bologna
// All rights reserved.
//
// This code is under development and not yet released to the public.
// Until it is released, the code is under the copyright of ETH Zurich and
// the University of Bologna, and may contain confidential and/or unpublished
// work. Any reuse/redistribution is strictly forbidden without written
// permission from ETH Zurich.
//
// Bug fixes and contributions will eventually be released under the
// SolderPad open hardware license in the context of the PULP platform
// (http://www.pulp-platform.org), under the copyright of ETH Zurich and the
// University of Bologna.
//

module random_stalls
(
    input  logic         clk_i,

    input  logic         core_req_i,
    output logic         core_gnt_o,
    input  logic [63:0]  core_addr_i,
    input  logic         core_we_i,
    input  logic [ 3:0]  core_be_i,
    input  logic [63:0]  core_wdata_i,
    output logic [63:0]  core_rdata_o,
    output logic         core_rvalid_o,

    output logic         data_req_o,
    input  logic         data_gnt_i,
    output logic [63:0]  data_addr_o,
    output logic         data_we_o,
    output logic [ 3:0]  data_be_o,
    output logic [63:0]  data_wdata_o,
    input  logic [63:0]  data_rdata_i,
    input  logic         data_rvalid_i
  );

  class rand_wait_cycles;
    rand int n;
    constraint default_c { n >= 0 ; n < 6;}
  endclass

  // random staller
  typedef struct {
    logic [63:0] addr;
    logic        we;
    logic [ 3:0] be;
    logic [63:0] wdata;
    logic [63:0] rdata;
  } stall_mem_t;

  mailbox   core_reqs          = new (4);
  mailbox   core_resps         = new (4);
  mailbox   core_resps_granted = new (4);
  mailbox   platform_transfers = new (4);
  semaphore req_served         = new (1);
  // ------------------
  // Core Request Side
  // ------------------
  // Waits for requests and puts them in a queue, does not perform actual
  // requests to the platform
  initial begin

    stall_mem_t mem_acc;
    automatic rand_wait_cycles wait_cycles = new ();
    int temp;

    forever begin
      core_gnt_o = 1'b0;

      #1;
      if (!core_req_i)
        continue;

      // we got a request, now let's wait for a random number of cycles before
      // we give the grant
      temp = wait_cycles.randomize();

      while(wait_cycles.n != 0) begin
        @(posedge clk_i);
        wait_cycles.n--;
        #1;
      end

      // block until the we served all outstanding requests
     req_served.get();

      // we waited for a random number of cycles, let's give the grant
      core_gnt_o = 1'b1;

      mem_acc.addr  = core_addr_i;
      mem_acc.be    = core_be_i;
      mem_acc.we    = core_we_i;
      mem_acc.wdata = core_wdata_i;

      core_reqs.put(mem_acc);

      @(posedge clk_i);

      core_resps_granted.put(1'b1);
    end
  end

  // ------------------
  // Core Response Side
  // ------------------
  // Waits for a response from the platform and then waits for a random number
  // of cycles before giving the rvalid
  initial begin
    stall_mem_t mem_acc;
    automatic rand_wait_cycles wait_cycles = new ();
    logic granted;
    int temp;

    forever begin
      @(posedge clk_i);
      core_rvalid_o = 1'b0;
      core_rdata_o = 'x;

      core_resps_granted.get(granted);
      core_resps.get(mem_acc);

      // we got a response, now let's wait for a random amount of cycles
      // we give the grant
      temp = wait_cycles.randomize();

      while(wait_cycles.n != 0) begin
        @(posedge clk_i);
        wait_cycles.n--;
      end

      // put back the semaphore
      req_served.put();
      // we waited for a random number of cycles, let's give the rvalid
      core_rdata_o  = mem_acc.rdata;
      core_rvalid_o = 1'b1;
    end
  end

  // platform request side
  // Waits for requests from the core and then performs the request on the
  // platform immediately
  // Simulates a "virtual" core
  initial begin
    stall_mem_t mem_acc;

    forever begin
      @(posedge clk_i);
      data_req_o   = 1'b0;
      data_addr_o  = '0;
      data_we_o    = 1'b0;
      data_be_o    = 4'b0;
      data_wdata_o = 'x;

      core_reqs.get(mem_acc);

      data_req_o   = 1'b1;
      data_addr_o  = mem_acc.addr;
      data_we_o    = mem_acc.we;
      data_be_o    = mem_acc.be;
      data_wdata_o = mem_acc.wdata;

      #1;
      while(!data_gnt_i) begin
        @(posedge clk_i);
        #1;
      end

      platform_transfers.put(mem_acc);
    end
  end

  // platform response side
  // Waits for rvalids and puts the responses into the core response mailbox
  initial begin
    stall_mem_t mem_acc;

    forever begin
      @(posedge clk_i);

      platform_transfers.get(mem_acc);

      while(!data_rvalid_i) begin
        @(posedge clk_i);
      end

      mem_acc.rdata = data_rdata_i;

      core_resps.put(mem_acc);
    end
  end
endmodule

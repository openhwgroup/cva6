// Copyright 2017 Embecosm Limited <www.embecosm.com>
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// RAM and MM wrapper for RI5CY
// Contributor: Jeremy Bennett <jeremy.bennett@embecosm.com>
//              Robert Balas <balasr@student.ethz.ch>
//
// This maps the dp_ram module to the instruction and data ports of the RI5CY
// processor core and some pseudo peripherals

// DVT LINTER waivers are fine because this is not a UVM component.
//@DVT_LINTER_WAIVER_START "MT20210811_1" disable SVTB.29.1.3.1, SVTB.29.1.7

module mm_ram
`ifndef VERILATOR
  import uvm_pkg::*;
  `include "uvm_macros.svh"
`endif
 #(
     parameter RAM_ADDR_WIDTH    =  16,
               INSTR_RDATA_WIDTH = 128, // width of read_data on instruction bus
               DATA_RDATA_WIDTH  =  32, // width of read_data on data bus
               DBG_ADDR_WIDTH    =  14, // POT ammount of memory allocated for debugger
                                        // physically located at end of memory
               IRQ_WIDTH         =  32  // IRQ vector width
  )
  (
     input logic                          clk_i,
     input logic                          rst_ni,
     input logic [31:0]                   dm_halt_addr_i,

     input logic                          instr_req_i,
     input logic [31:0]                   instr_addr_i,
     output logic [INSTR_RDATA_WIDTH-1:0] instr_rdata_o,
     output logic                         instr_rvalid_o,
     output logic                         instr_gnt_o,

     input logic                          data_req_i,
     input logic [31:0]                   data_addr_i,
     input logic                          data_we_i,
     input logic [3:0]                    data_be_i,
     input logic [31:0]                   data_wdata_i,
     output logic [31:0]                  data_rdata_o,
     output logic                         data_rvalid_o,
     output logic                         data_gnt_o,

     input logic [4:0]                    irq_id_i,
     input logic                          irq_ack_i,
     output logic [IRQ_WIDTH-1:0]         irq_o,

     input logic [31:0]                   pc_core_id_i,

     output logic                         debug_req_o,

     output logic                         tests_passed_o,
     output logic                         tests_failed_o,
     output logic                         exit_valid_o,
     output logic [31:0]                  exit_value_o);

    localparam int                        RND_STALL_REGS        = 16;
    localparam int                        RND_STALL_INSTR_EN    = 0;
    localparam int                        RND_STALL_INSTR_MODE  = 2;
    localparam int                        RND_STALL_INSTR_MAX   = 4;
    localparam int                        RND_STALL_INSTR_GNT   = 6;
    localparam int                        RND_STALL_INSTR_VALID = 8;
    localparam int                        RND_STALL_DATA_EN     = 1;
    localparam int                        RND_STALL_DATA_MODE   = 3;
    localparam int                        RND_STALL_DATA_MAX    = 5;
    localparam int                        RND_STALL_DATA_GNT    = 7;
    localparam int                        RND_STALL_DATA_VALID  = 9;

    localparam int                        RND_IRQ_ID     = 31;

    localparam int                        MMADDR_PRINT      = 32'h1000_0000;
    localparam int                        MMADDR_TESTSTATUS = 32'h2000_0000;
    localparam int                        MMADDR_EXIT       = 32'h2000_0004;
    localparam int                        MMADDR_SIGBEGIN   = 32'h2000_0008;
    localparam int                        MMADDR_SIGEND     = 32'h2000_000C;
    localparam int                        MMADDR_SIGDUMP    = 32'h2000_0010;
    localparam int                        MMADDR_TIMERREG   = 32'h1500_0000;
    localparam int                        MMADDR_TIMERVAL   = 32'h1500_0004;
    localparam int                        MMADDR_DBG        = 32'h1500_0008;
    localparam int                        MMADDR_RNDSTALL   = 16'h1600;
    localparam int                        MMADDR_RNDNUM     = 32'h1500_1000;
    localparam int                        MMADDR_TICKS      = 32'h1500_1004;

    // UVM info tags
    localparam string                     MM_RAM_TAG = "MM_RAM";
    localparam string                     RNDSTALL_TAG = "RNDSTALL";

    // mux for read and writes
    enum logic [2:0]{RAM, MM, RND_STALL, ERR, RND_NUM, TICKS} select_rdata_d, select_rdata_q;

    enum logic {T_RAM, T_PER} transaction;


    int                            i;

    logic [31:0]                   data_addr_aligned;

    // signals for handshake
    logic                          data_rvalid_q;
    logic                          instr_rvalid_q;
    logic [INSTR_RDATA_WIDTH-1:0]  core_instr_rdata;
    logic [31:0]                   core_data_rdata;

    // signals to ram
    logic                          ram_data_req;
    logic [RAM_ADDR_WIDTH-1:0]     ram_data_addr;
    logic [31:0]                   ram_data_wdata;
    logic [31:0]                   ram_data_rdata;
    logic                          ram_data_we;
    logic [3:0]                    ram_data_be;
    logic                          ram_data_gnt;
    logic                          ram_data_valid;

    logic                          data_req_dec;
    logic [31:0]                   data_wdata_dec;
    logic [RAM_ADDR_WIDTH-1:0]     data_addr_dec;
    logic                          data_we_dec;
    logic [3:0]                    data_be_dec;

    logic [INSTR_RDATA_WIDTH-1:0]  ram_instr_rdata;
    logic                          ram_instr_req;
    logic [RAM_ADDR_WIDTH-1:0]     ram_instr_addr;
    logic                          ram_instr_gnt;
    logic                          ram_instr_valid;
    logic [RAM_ADDR_WIDTH-1:0]     instr_addr_remap;

    // signals to print peripheral
    logic [31:0]                   print_wdata;
    logic                          print_valid;

    // signature data
    logic [31:0]                   sig_end_d, sig_end_q;
    logic [31:0]                   sig_begin_d, sig_begin_q;

    // signals to timer
    logic [IRQ_WIDTH-1:0]          timer_irq_mask_q;
    logic [31:0]                   timer_cnt_q;
    logic [IRQ_WIDTH-1:0]          irq_q;
    logic                          timer_reg_valid;
    logic                          timer_val_valid;
    logic [31:0]                   timer_wdata;

            // cycle counting
    logic [31:0]                   cycle_count_q;
    logic                          cycle_count_overflow_q;
    logic                          cycle_count_clear;

    // debugger control signals
    logic [31:0]                   debugger_wdata;
    logic                          debugger_valid;

    // signals to rnd_stall
    logic [31:0]                   rnd_stall_regs [0:RND_STALL_REGS-1];

    logic                          rnd_stall_req;
    logic [31:0]                   rnd_stall_addr;
    logic [31:0]                   rnd_stall_wdata;
    logic                          rnd_stall_we;
    logic [31:0]                   rnd_stall_rdata;

    //signal delayed by random stall
    logic                          rnd_stall_instr_req;
    logic                          rnd_stall_instr_gnt;

    logic                          rnd_stall_data_req;
    logic                          rnd_stall_data_gnt;

    // random number generation
    logic                          rnd_num_req;
    logic [31:0]                   rnd_num;

    //random or monitor interrupt request
    logic                          rnd_irq;

    // used by dump_signature methods
    string                         sig_file;
    string                         sig_string;
    bit                            use_sig_file;
    int                            sig_fd;
    int                            errno;
    string                         error_str;

    // Common code used by both reads and writes
    function void setup_transaction();

       data_req_dec = data_req_i;
       if ( (data_addr_i >= dm_halt_addr_i) &&
            (data_addr_i < (dm_halt_addr_i + (2 ** DBG_ADDR_WIDTH)) )
          ) begin
          // remap debug code to end of memory
          data_addr_dec  = (data_addr_i[RAM_ADDR_WIDTH-1:0] - dm_halt_addr_i[RAM_ADDR_WIDTH-1:0]) +
                            2**RAM_ADDR_WIDTH - 2**DBG_ADDR_WIDTH;
       end
       else begin
          data_addr_dec  = data_addr_i[RAM_ADDR_WIDTH-1:0];
       end

       data_wdata_dec = data_wdata_i;
       data_we_dec    = data_we_i;
       data_be_dec    = data_be_i;
       transaction    = T_RAM;

    endfunction: setup_transaction

    // uhh, align?
    always_comb data_addr_aligned = {data_addr_i[31:2], 2'b0};

    always @(negedge rst_ni) begin : configure_stalls
        for (i = 0; i < RND_STALL_REGS; i=i+1) begin
            rnd_stall_regs[i] = 0;
        end
`ifndef VERILATOR
        if (!$test$plusargs("rand_stall_obi_disable")) begin
            if ($test$plusargs("max_data_zero_instr_stall")) begin
                `uvm_info(RNDSTALL_TAG, "Max data stall, zero instruction stall configuration", UVM_LOW)
                // This "knob" creates maximum stalls on data loads/stores, and
                // no stalls on instruction fetches.  Used for fence.i testing.
                rnd_stall_regs[RND_STALL_DATA_EN]     = 1;
                rnd_stall_regs[RND_STALL_DATA_MODE]   = 2;
                rnd_stall_regs[RND_STALL_DATA_GNT]    = 2;
                rnd_stall_regs[RND_STALL_DATA_VALID]  = 2;
                rnd_stall_regs[RND_STALL_DATA_MAX]    = 8;
            end
            else begin
                randcase
                    2: begin
                        // No delays
                    end
                    1: begin
                        // Create RAM stall delays
                        rnd_stall_regs[RND_STALL_INSTR_EN]    = 1;
                        rnd_stall_regs[RND_STALL_INSTR_MODE]  = $urandom_range(2,1);
                        rnd_stall_regs[RND_STALL_INSTR_GNT]   = $urandom_range(3,0);
                        rnd_stall_regs[RND_STALL_INSTR_VALID] = $urandom_range(3,0);
                        rnd_stall_regs[RND_STALL_INSTR_MAX]   = $urandom_range(3,0);
                    end
                endcase

                randcase
                    2: begin
                        // No delays
                    end
                    1: begin
                        // Create RAM stall delays
                        rnd_stall_regs[RND_STALL_DATA_EN]     = 1;
                        rnd_stall_regs[RND_STALL_DATA_MODE]   = $urandom_range(2,1);
                        rnd_stall_regs[RND_STALL_DATA_GNT]    = $urandom_range(2,0);
                        rnd_stall_regs[RND_STALL_DATA_VALID]  = $urandom_range(2,0);
                        rnd_stall_regs[RND_STALL_DATA_MAX]    = $urandom_range(3,0);
                    end
                endcase
            end
        end

        `uvm_info(RNDSTALL_TAG, $sformatf("INSTR OBI stall enable: %0d", rnd_stall_regs[RND_STALL_INSTR_EN]), UVM_LOW)
        `uvm_info(RNDSTALL_TAG, $sformatf("INSTR OBI stall mode:   %0d", rnd_stall_regs[RND_STALL_INSTR_MODE]), UVM_LOW)
        `uvm_info(RNDSTALL_TAG, $sformatf("INSTR OBI stall gnt:    %0d", rnd_stall_regs[RND_STALL_INSTR_GNT]), UVM_LOW)
        `uvm_info(RNDSTALL_TAG, $sformatf("INSTR OBI stall valid:  %0d", rnd_stall_regs[RND_STALL_INSTR_VALID]), UVM_LOW)
        `uvm_info(RNDSTALL_TAG, $sformatf("INSTR OBI stall max:    %0d", rnd_stall_regs[RND_STALL_INSTR_MAX]), UVM_LOW)
        `uvm_info(RNDSTALL_TAG, $sformatf("DATA  OBI stall enable: %0d", rnd_stall_regs[RND_STALL_DATA_EN]), UVM_LOW)
        `uvm_info(RNDSTALL_TAG, $sformatf("DATA  OBI stall mode:   %0d", rnd_stall_regs[RND_STALL_DATA_MODE]), UVM_LOW)
        `uvm_info(RNDSTALL_TAG, $sformatf("DATA  OBI stall gnt:    %0d", rnd_stall_regs[RND_STALL_DATA_GNT]), UVM_LOW)
        `uvm_info(RNDSTALL_TAG, $sformatf("DATA  OBI stall valid:  %0d", rnd_stall_regs[RND_STALL_DATA_VALID]), UVM_LOW)
        `uvm_info(RNDSTALL_TAG, $sformatf("DATA  OBI stall max:    %0d", rnd_stall_regs[RND_STALL_DATA_MAX]), UVM_LOW)
`endif
    end : configure_stalls

`ifndef VERILATOR
    function bit is_stall_sim();
        return rnd_stall_regs[RND_STALL_DATA_EN] || rnd_stall_regs[RND_STALL_INSTR_EN];
    endfunction : is_stall_sim
`endif

    // handle the mapping of read and writes to either memory or pseudo
    // peripherals (currently just a redirection of writes to stdout)
    always_comb begin
        tests_passed_o      = '0;
        tests_failed_o      = '0;
        exit_value_o        =  0;
        exit_valid_o        = '0;
        data_req_dec        = '0;
        data_addr_dec       = '0;
        data_wdata_dec      = '0;
        data_we_dec         = '0;
        data_be_dec         = '0;
        print_wdata         = '0;
        print_valid         = '0;
        timer_wdata         = '0;
        timer_reg_valid     = '0;
        timer_val_valid     = '0;
        debugger_wdata      = '0;
        debugger_valid      = '0;
        sig_end_d           = sig_end_q;
        sig_begin_d         = sig_begin_q;
        rnd_stall_req       = '0;
        rnd_stall_addr      = '0;
        rnd_stall_wdata     = '0;
        rnd_stall_we        = '0;
        rnd_num_req         = '0;
        cycle_count_clear   = '0;
        select_rdata_d      = RAM;
        transaction         = T_PER;

        if (data_req_i & data_gnt_o) begin
            if (data_we_i) begin // handle writes
                if (data_addr_i < 2 ** RAM_ADDR_WIDTH ||
                    ( (data_addr_i >= dm_halt_addr_i) &&
                    (data_addr_i < (dm_halt_addr_i + (2 ** DBG_ADDR_WIDTH)) ))
                   )
                begin
                    setup_transaction();
                end else if (data_addr_i == MMADDR_PRINT) begin
                    print_wdata = data_wdata_i;
                    print_valid = '1;

                end else if (data_addr_i == MMADDR_TESTSTATUS) begin
                    if (data_wdata_i == 123456789)
                        tests_passed_o = '1;
                    else if (data_wdata_i == 1)
                        tests_failed_o = '1;

                end else if (data_addr_i == MMADDR_EXIT) begin
                    exit_valid_o = '1;
                    exit_value_o = data_wdata_i;

                end else if (data_addr_i == MMADDR_SIGBEGIN) begin
                    // sets signature begin
                    sig_begin_d = data_wdata_i;

                end else if (data_addr_i == MMADDR_SIGEND) begin
                    // sets signature end
                    sig_end_d = data_wdata_i;

                end else if (data_addr_i == MMADDR_SIGDUMP) begin
                    // dump signature and halt
`ifndef VERILATOR
                    if ($value$plusargs("signature=%s", sig_file)) begin
                        sig_fd = $fopen(sig_file, "w");
                        if (sig_fd == 0) begin
                            errno = $ferror(sig_fd, error_str);
                            `uvm_error(MM_RAM_TAG, $sformatf("Cannot open signature file %s for writing (error_str: %s).", sig_file, error_str))
                            use_sig_file = 1'b0;
                        end else begin
                            use_sig_file = 1'b1;
                        end
                    end

                    sig_string = "";
                    for (logic [31:0] addr = sig_begin_q; addr < sig_end_q; addr +=4) begin
                        sig_string = {sig_string, $sformatf("%x%x%x%x\n", dp_ram_i.mem[addr+3], dp_ram_i.mem[addr+2],
                                                                          dp_ram_i.mem[addr+1], dp_ram_i.mem[addr+0])};
                        if (use_sig_file) begin
                            $fdisplay(sig_fd, "%x%x%x%x", dp_ram_i.mem[addr+3], dp_ram_i.mem[addr+2],
                                                          dp_ram_i.mem[addr+1], dp_ram_i.mem[addr+0]);
                        end
                    end
                    `uvm_info(MM_RAM_TAG, $sformatf("Dumping signature:\n%s", sig_string), UVM_LOW)
`else
                    if ($value$plusargs("signature=%s", sig_file)) begin
                        sig_fd = $fopen(sig_file, "w");
                        if (sig_fd == 0) begin
                            $error("can't open file");
                            use_sig_file = 1'b0;
                        end else begin
                            use_sig_file = 1'b1;
                        end
                    end

                    $display("%m @ %0t: Dumping signature", $time);
                    for (logic [31:0] addr = sig_begin_q; addr < sig_end_q; addr +=4) begin
                        $display("%x%x%x%x", dp_ram_i.mem[addr+3], dp_ram_i.mem[addr+2],
                                             dp_ram_i.mem[addr+1], dp_ram_i.mem[addr+0]);
                        if (use_sig_file) begin
                            $fdisplay(sig_fd, "%x%x%x%x", dp_ram_i.mem[addr+3], dp_ram_i.mem[addr+2],
                                                          dp_ram_i.mem[addr+1], dp_ram_i.mem[addr+0]);
                        end
                    end
`endif // ifndef VERILATOR
                    exit_valid_o = '1; // signal halt to testbench
                    exit_value_o = '0;

                end else if (data_addr_i == MMADDR_TIMERREG) begin
                    timer_wdata = data_wdata_i;
                    timer_reg_valid = '1;

                end else if (data_addr_i == MMADDR_TIMERVAL) begin
                    timer_wdata = data_wdata_i;
                    timer_val_valid = '1;

                end else if (data_addr_i == MMADDR_DBG) begin
                    debugger_wdata = data_wdata_i;
                    debugger_valid = '1;

                end else if (data_addr_i[31:16] == MMADDR_RNDSTALL) begin
                    rnd_stall_req   = data_req_i;
                    rnd_stall_wdata = data_wdata_i;
                    rnd_stall_addr  = data_addr_i;
                    rnd_stall_we    = data_we_i;
                end else if (data_addr_i == MMADDR_TICKS) begin
                    cycle_count_clear = 1;
                end else begin
                    // out of bounds write
                end

            end else begin // handle reads
                if (data_addr_i < 2 ** RAM_ADDR_WIDTH ||
                    ( (data_addr_i >= dm_halt_addr_i) &&
                    (data_addr_i < (dm_halt_addr_i + (2 ** DBG_ADDR_WIDTH)) ))
                   )
                begin
                    select_rdata_d = RAM;

                    setup_transaction();
                end else if (data_addr_i[31:16] == MMADDR_RNDSTALL) begin
                    select_rdata_d = RND_STALL;

                    rnd_stall_req      = data_req_i;
                    rnd_stall_wdata    = data_wdata_i;
                    rnd_stall_addr     = data_addr_i;
                    rnd_stall_we       = data_we_i;
                end else if (data_addr_i[31:0] == MMADDR_RNDNUM) begin
                    rnd_num_req = 1'b1;
                    select_rdata_d = RND_NUM;
                end else if (data_addr_i == MMADDR_TICKS) begin
                    select_rdata_d = TICKS;
                end else
                    select_rdata_d = ERR;

            end
        end
    end

`ifndef VERILATOR
    // signal out of bound writes
    out_of_bounds_write: assert property
    (@(posedge clk_i) disable iff (~rst_ni)
     (data_req_i && data_we_i |-> data_addr_i < 2 ** RAM_ADDR_WIDTH
      || ( (data_addr_i >= dm_halt_addr_i) &&
           (data_addr_i < (dm_halt_addr_i + (2 ** DBG_ADDR_WIDTH)) )
         )
         || data_addr_i == MMADDR_PRINT
         || data_addr_i == MMADDR_TIMERREG
         || data_addr_i == MMADDR_TIMERVAL
         || data_addr_i == MMADDR_DBG
         || data_addr_i == MMADDR_TESTSTATUS
         || data_addr_i == MMADDR_EXIT
         || data_addr_i == MMADDR_SIGBEGIN
         || data_addr_i == MMADDR_SIGEND
         || data_addr_i == MMADDR_SIGDUMP
         || data_addr_i == MMADDR_TICKS
         || data_addr_i[31:16] == MMADDR_RNDSTALL))
           else `uvm_fatal(MM_RAM_TAG, $sformatf("out of bounds write to %08x with %08x", data_addr_i, data_wdata_i))
`endif

    logic[31:0] data_rdata_mux;

    // make sure we select the proper read data
    always_comb begin: read_mux
        data_rdata_mux = '0;

        if(select_rdata_q == RAM) begin
            data_rdata_mux = core_data_rdata;
        end else if(select_rdata_q == RND_STALL) begin
            data_rdata_mux = rnd_stall_rdata;
`ifndef VERILATOR
            `uvm_fatal(MM_RAM_TAG, $sformatf("out of bounds read from %08x\nRandom stall generator is not supported with Verilator", data_addr_i));
`endif
        end else if (select_rdata_q == RND_NUM) begin
            data_rdata_mux = rnd_num;
        end else if (select_rdata_q == TICKS) begin
            data_rdata_mux = cycle_count_q;
`ifndef VERILATOR
            if (cycle_count_overflow_q) begin
                `uvm_fatal(MM_RAM_TAG, "cycle counter read after overflow");
            end
        end else if (select_rdata_q == ERR) begin
            `uvm_error(MM_RAM_TAG, $sformatf("out of bounds read from %08x (RAM_ADDR_WIDTH=%0d; dm_halt_addri=%08x, DBG_ADDR_WIDTH=%0d)",
                                             data_addr_i, RAM_ADDR_WIDTH, dm_halt_addr_i, DBG_ADDR_WIDTH))
`endif
        end
    end

    // print to stdout pseudo peripheral
    always_ff @(posedge clk_i, negedge rst_ni) begin: print_peripheral
        if(print_valid) begin
            if ($test$plusargs("verbose")) begin
                if (32 <= print_wdata && print_wdata < 128)
                    $display("OUT: '%c'", print_wdata[7:0]);
                else
                    $display("OUT: %3d", print_wdata);

            end else begin
                $write("%c", print_wdata[7:0]);
`ifndef VERILATOR
                $fflush();
`endif
            end
        end
    end

    assign irq_o    = irq_q | rnd_irq << RND_IRQ_ID;

    // Set irq vector to timer_irq_mask_q when timer counts down
    // irq bit cleared when acknowledged
    always_ff @(posedge clk_i, negedge rst_ni) begin: tb_irq_timer
        if(~rst_ni) begin
            timer_irq_mask_q <= '0;
            timer_cnt_q      <= '0;
            irq_q            <= '0;
        end else begin
          // set timer irq mask
          if(timer_reg_valid)
            timer_irq_mask_q <= timer_wdata;

          // write timer value
          if(timer_val_valid)
            timer_cnt_q <= timer_wdata;
          else if(timer_cnt_q > 0)
            timer_cnt_q <= timer_cnt_q - 1;

          // set/clear irq
          if(timer_cnt_q == 1)
            irq_q <= timer_irq_mask_q ;
          else if(irq_ack_i)
            irq_q[irq_id_i] <= 1'b0;

        end // else: !if(~rst_ni)
    end // block: tb_irq_timer

    // Count cycles
    always_ff @(posedge clk_i, negedge rst_ni) begin: tb_cycle_counter
        if (~rst_ni) begin
            cycle_count_q <= '0;
            cycle_count_overflow_q <= 0;
        end else begin
            if (cycle_count_clear) begin
                cycle_count_q <= '0;
            end else begin
                cycle_count_q <= cycle_count_q + 1;
            end

            if (cycle_count_q + 1 == 0) begin
                cycle_count_overflow_q <= 1;
            end
        end
    end

    // Update random stall control
    always @(posedge clk_i, negedge rst_ni) begin: tb_stall
        if(~rst_ni) begin
          rnd_stall_rdata  <= '0;
        end else begin
          if(rnd_stall_req) begin
            if(rnd_stall_we)
              rnd_stall_regs[rnd_stall_addr[5:2]] <= rnd_stall_wdata;
            else
              rnd_stall_rdata <= rnd_stall_regs[rnd_stall_addr[5:2]];
          end
        end
    end // block: tb_stall

   // -------------------------------------------------------------
   // Generate a random number using the SystemVerilog random number function
   always_ff @(posedge clk_i, negedge rst_ni) begin : rnd_num_gen
        if (!rst_ni)
            rnd_num <= 32'h0;
        else if (rnd_num_req)
`ifndef VERILATOR
            rnd_num <= $urandom();
`else
            rnd_num <= 32'h0;
`endif
   end

   // -------------------------------------------------------------
   // Control debug_req. Writing to this alias will change or create
   // a debug_req pulse. The debug_req can be a pulse or level change,
   // can have a delay when to assert, and also have pulse duration
   // determined by the values in the wdata field:
   //
   // wdata[31]    = debug_req signal value
   // wdata[30]    = debug request mode, 0= level, 1= pulse
   // wdata[29]    = debug pulse duration random
   // wdata[28:16] = debug pulse duration or pulse random max range
   // wdata[15]    = random start
   // wdata[14:0]  = start delay or start random max range

   logic [14:0] debugger_start_cnt_q;
   logic        debug_req_value_q;
   logic [12:0] debug_req_duration_q;
    always_ff @(posedge clk_i, negedge rst_ni) begin: tb_debugger
        if(~rst_ni) begin
           debugger_start_cnt_q <= '0;
           debug_req_value_q    <= '0;
           debug_req_duration_q <= '0;
           debug_req_o          <= '0;
       end else begin

            if(debugger_valid && (debugger_start_cnt_q==0) && (debug_req_duration_q==0)) begin
               if(debugger_wdata[15]) //If random start
                 // then set max random delay range to wdata[14:0]
                 // note, if wdata[14:0] == 0, then assign max random range to 128
`ifndef VERILATOR
                 debugger_start_cnt_q <= $urandom_range(1,~|debugger_wdata[14:0] ? 128 : debugger_wdata[14:0]);
`else
                 debugger_start_cnt_q <= 1;
`endif
               else
                 // else, the delay is determined by wdata[14:0]
                 //  note, if wdata[14:0] == 0, then assign value to 1
                 debugger_start_cnt_q <= ~|debugger_wdata[14:0] ? 1 : debugger_wdata[14:0];

               debug_req_value_q <= debugger_wdata[31]; // value to be applied to debug_req

               if(!debugger_wdata[30]) // If mode is level then set duration to 0
                 debug_req_duration_q <= 'b0;
               else // Else mode is pulse
                 if(debugger_wdata[29]) // If random pulse width
                   // then set max random pulse width to wdata[28:16]
                   //  note, if wdata[28:16] ==0, then assign max to 128
`ifndef VERILATOR
                   debug_req_duration_q <= $urandom_range(1,~|debugger_wdata[28:16] ? 128 : debugger_wdata[28:16]);
`else
                   debugger_start_cnt_q <= 1;
`endif
                else
                   // else, the pulse is determined by wdata[28:16]
                   //  note, if wdata[28:16]==0, then set pulse width to 1
                   debug_req_duration_q <= ~|debugger_wdata[28:16] ? 1 : debugger_wdata[28:16];

            end else begin
                // Count down the delay to start
                if(debugger_start_cnt_q > 0)begin
                    debugger_start_cnt_q <= debugger_start_cnt_q - 1;
                   // At count == 1, then assert the debug_req
                   if(debugger_start_cnt_q == 1)
                     debug_req_o <= debug_req_value_q;
                end
                // Count down debug_req pulse duration
                else if(debug_req_duration_q > 0)begin
                   debug_req_duration_q <= debug_req_duration_q - 1;
                   // At count == 1, then de-assert debug_req
                   if(debug_req_duration_q == 1)
                     debug_req_o <= !debug_req_value_q;
                end
            end
        end
    end

    // -------------------------------------------------------------
    // show writes if requested
    always_ff @(posedge clk_i, negedge rst_ni) begin: verbose_writes
        if ($test$plusargs("verbose") && data_req_i && data_we_i)
            $display("write addr=0x%08x: data=0x%08x",
                     data_addr_i, data_wdata_i);
    end

    // instantiate the ram
    dp_ram
        #(.ADDR_WIDTH (RAM_ADDR_WIDTH),
          .INSTR_RDATA_WIDTH(INSTR_RDATA_WIDTH))
    dp_ram_i
        (
         .clk_i     ( clk_i           ),

         .en_a_i    ( ram_instr_req   ),
         .addr_a_i  ( ram_instr_addr  ),
         .wdata_a_i ( '0              ), // Not writing so ignored
         .rdata_a_o ( ram_instr_rdata ),
         .we_a_i    ( '0              ),
         .be_a_i    ( 4'b1111         ), // Always want 32-bits

         .en_b_i    ( ram_data_req    ),
         .addr_b_i  ( ram_data_addr   ),
         .wdata_b_i ( ram_data_wdata  ),
         .rdata_b_o ( ram_data_rdata  ),
         .we_b_i    ( ram_data_we     ),
         .be_b_i    ( ram_data_be     ));

    riscv_rvalid_stall instr_rvalid_stall_i (
        .clk_i      ( clk_i           ),
        .rst_ni     ( rst_ni          ),
        .req_i      ( instr_req_i     ),
        .gnt_i      ( instr_gnt_o     ),
        .we_i       ( 1'b0            ),
        .rdata_i    ( ram_instr_rdata ),
        .rdata_o    ( instr_rdata_o   ),
        .rvalid_o   ( instr_rvalid_o  ),
        .en_stall_i   ( rnd_stall_regs[RND_STALL_INSTR_EN][0]),
        .stall_mode_i ( rnd_stall_regs[RND_STALL_INSTR_MODE] ),
        .max_stall_i  ( rnd_stall_regs[RND_STALL_INSTR_MAX]  ),
        .valid_stall_i( rnd_stall_regs[RND_STALL_INSTR_VALID]));

    riscv_rvalid_stall data_rvalid_stall_i (
        .clk_i      ( clk_i           ),
        .rst_ni     ( rst_ni          ),
        .req_i      ( data_req_i      ),
        .gnt_i      ( data_gnt_o      ),
        .we_i       ( data_we_i       ),
        .rdata_i    ( data_rdata_mux  ),
        .rdata_o    ( data_rdata_o    ),
        .rvalid_o   ( data_rvalid_o   ),
        .en_stall_i   ( rnd_stall_regs[RND_STALL_DATA_EN][0]),
        .stall_mode_i ( rnd_stall_regs[RND_STALL_DATA_MODE] ),
        .max_stall_i  ( rnd_stall_regs[RND_STALL_DATA_MAX]  ),
        .valid_stall_i( rnd_stall_regs[RND_STALL_DATA_VALID]));

    // signature range
    always @(posedge clk_i, negedge rst_ni) begin
        if (~rst_ni) begin
            sig_end_q   <= '0;
            sig_begin_q <= '0;
        end else begin
            sig_end_q   <= sig_end_d;
            sig_begin_q <= sig_begin_d;
        end
    end

    always_ff @(posedge clk_i, negedge rst_ni) begin
        if (~rst_ni) begin
            select_rdata_q <= RAM;
        end else begin
            select_rdata_q <= select_rdata_d;
        end
    end

    assign instr_gnt_o    = ram_instr_gnt;
    assign data_gnt_o     = ram_data_gnt;

    // remap debug code to end of memory
    assign instr_addr_remap =  ( (instr_addr_i >= dm_halt_addr_i) &&
                               (instr_addr_i < (dm_halt_addr_i + (2 ** DBG_ADDR_WIDTH)) ) ) ?
                                   (instr_addr_i - dm_halt_addr_i) +  2**RAM_ADDR_WIDTH - 2**DBG_ADDR_WIDTH :
                                   instr_addr_i ;

  always_comb
  begin
    ram_instr_req    = instr_req_i;
    ram_instr_addr   = instr_addr_remap;
    ram_instr_gnt    = instr_req_i ? 1'b1 : $urandom;
    core_instr_rdata = ram_instr_rdata;

    ram_data_req     = data_req_dec;
    ram_data_addr    = data_addr_dec;
    ram_data_gnt     = data_req_i ? 1'b1 : $urandom;
    core_data_rdata  = ram_data_rdata;
    ram_data_wdata   = data_wdata_dec;
    ram_data_we      = data_we_dec;
    ram_data_be      = data_be_dec;

    if(rnd_stall_regs[RND_STALL_INSTR_EN]) begin
        ram_instr_req    = rnd_stall_instr_req;
        ram_instr_gnt    = rnd_stall_instr_gnt;
    end
    if(rnd_stall_regs[RND_STALL_DATA_EN]) begin
        ram_data_req     = rnd_stall_data_req;
        ram_data_gnt     = rnd_stall_data_gnt;
    end
  end

  riscv_gnt_stall
  #(
    .DATA_WIDTH     (INSTR_RDATA_WIDTH),
    .RAM_ADDR_WIDTH (RAM_ADDR_WIDTH   )
   )
  instr_gnt_stall_i
  (
    .clk_i              ( clk_i                  ),
    .rst_ni             ( rst_ni                 ),

    .grant_mem_i        ( rnd_stall_instr_req    ),
    .grant_core_o       ( rnd_stall_instr_gnt    ),

    .req_core_i         ( instr_req_i            ),
    .req_mem_o          ( rnd_stall_instr_req    ),

    .en_stall_i         ( rnd_stall_regs[RND_STALL_INSTR_EN][0]),
    .stall_mode_i       ( rnd_stall_regs[RND_STALL_INSTR_MODE] ),
    .max_stall_i        ( rnd_stall_regs[RND_STALL_INSTR_MAX]  ),
    .gnt_stall_i        ( rnd_stall_regs[RND_STALL_INSTR_GNT]  )
    );

  riscv_gnt_stall
  #(
    .DATA_WIDTH     (DATA_RDATA_WIDTH),
    .RAM_ADDR_WIDTH (RAM_ADDR_WIDTH  )
   )
  data_gnt_stall_i
  (
    .clk_i              ( clk_i                  ),
    .rst_ni             ( rst_ni                 ),

    .grant_mem_i        ( rnd_stall_data_req     ),
    .grant_core_o       ( rnd_stall_data_gnt     ),

    .req_core_i         ( data_req_i             ),
    .req_mem_o          ( rnd_stall_data_req     ),

    .en_stall_i         ( rnd_stall_regs[RND_STALL_DATA_EN][0]),
    .stall_mode_i       ( rnd_stall_regs[RND_STALL_DATA_MODE] ),
    .max_stall_i        ( rnd_stall_regs[RND_STALL_DATA_MAX]  ),
    .gnt_stall_i        ( rnd_stall_regs[RND_STALL_DATA_GNT]  )
    );

`ifndef VERILATOR
    riscv_random_interrupt_generator
    random_interrupt_generator_i
    (
      .rst_ni            ( rst_ni                                       ),
      .clk_i             ( clk_i                                        ),
      .irq_i             ( 1'b0                                         ),
      .irq_id_i          ( '0                                           ),
      .irq_ack_i         ( irq_ack_i == 1'b1 && irq_id_i == RND_IRQ_ID  ),
      .irq_ack_o         (                                              ),
      .irq_o             ( rnd_irq                                      ),
      .irq_id_o          ( /*disconnected, always generate RND_IRQ_ID*/ ),
      .irq_mode_i        ( rnd_stall_regs[10]                           ),
      .irq_min_cycles_i  ( rnd_stall_regs[11]                           ),
      .irq_max_cycles_i  ( rnd_stall_regs[12]                           ),
      .irq_min_id_i      ( RND_IRQ_ID                                   ),
      .irq_max_id_i      ( RND_IRQ_ID                                   ),
      .irq_act_id_o      (                                              ),
      .irq_id_we_o       (                                              ),
      .irq_pc_id_i       ( pc_core_id_i                                 ),
      .irq_pc_trig_i     ( rnd_stall_regs[13]                           )
    );
`endif

endmodule // ram

//@DVT_LINTER_WAIVER_END "MT20210811_1"

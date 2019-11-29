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

module mm_ram
    #(parameter RAM_ADDR_WIDTH = 16,
      parameter INSTR_RDATA_WIDTH = 128)
    (input logic                          clk_i,
     input logic                          rst_ni,

     input logic                          instr_req_i,
     input logic [RAM_ADDR_WIDTH-1:0]     instr_addr_i,
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
     output logic [4:0]                   irq_id_o,
     output logic                         irq_o,

     input logic [31:0]                   pc_core_id_i,

     output logic                         tests_passed_o,
     output logic                         tests_failed_o,
     output logic                         exit_valid_o,
     output logic [31:0]                  exit_value_o);

    localparam int                        TIMER_IRQ_ID   = 3;
    localparam int                        RND_STALL_REGS = 16;
    localparam int                        RND_IRQ_ID     = 31;

    // mux for read and writes
    enum logic [1:0]{RAM, MM, RND_STALL, ERR} select_rdata_d, select_rdata_q;

    enum logic {T_RAM, T_PER} transaction;

    enum logic [1:0] {IDLE, PERIPHEARL_VALID, WAIT_RAM_GNT, WAIT_RAM_VALID} state_valid_n, state_valid_q;



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

    // signals to print peripheral
    logic [31:0]                   print_wdata;
    logic                          print_valid;

    // signature data
    logic [31:0]                   sig_end_d, sig_end_q;
    logic [31:0]                   sig_begin_d, sig_begin_q;

    // signals to timer
    logic [31:0]                   timer_irq_mask_q;
    logic [31:0]                   timer_cnt_q;
    logic                          irq_q;
    logic                          timer_reg_valid;
    logic                          timer_val_valid;
    logic [31:0]                   timer_wdata;

    // signals to rnd_stall
    logic [31:0]                   rnd_stall_regs [0:RND_STALL_REGS-1];

    logic                          rnd_stall_req;
    logic [31:0]                   rnd_stall_addr;
    logic [31:0]                   rnd_stall_wdata;
    logic                          rnd_stall_we;
    logic [31:0]                   rnd_stall_rdata;

    //signal delayed by random stall
    logic                          rnd_stall_instr_req;
    logic [RAM_ADDR_WIDTH-1:0]     rnd_stall_instr_addr;
    logic                          rnd_stall_instr_gnt;
    logic                          rnd_stall_instr_valid;
    logic [INSTR_RDATA_WIDTH-1:0]  rnd_stall_instr_rdata;

    logic                          rnd_stall_data_req;
    logic [RAM_ADDR_WIDTH-1:0]     rnd_stall_data_addr;
    logic                          rnd_stall_data_gnt;
    logic                          rnd_stall_data_valid;
    logic [31:0]                   rnd_stall_data_rdata;
    logic [31:0]                   rnd_stall_data_wdata;
    logic                          rnd_stall_data_we;
    logic [3:0]                    rnd_stall_data_be;

    //random or monitor interrupt request
    logic rnd_irq;

    // uhh, align?
    always_comb data_addr_aligned = {data_addr_i[31:2], 2'b0};

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
        sig_end_d           = sig_end_q;
        sig_begin_d         = sig_begin_q;
        rnd_stall_req       = '0;
        rnd_stall_addr      = '0;
        rnd_stall_wdata     = '0;
        rnd_stall_we        = '0;
        select_rdata_d      = RAM;
        transaction         = T_PER;

        if (data_req_i) begin
            if (data_we_i) begin // handle writes
                if (data_addr_i < 2 ** RAM_ADDR_WIDTH) begin
                    data_req_dec   = data_req_i;
                    data_addr_dec  = data_addr_i[RAM_ADDR_WIDTH-1:0];
                    data_wdata_dec = data_wdata_i;
                    data_we_dec    = data_we_i;
                    data_be_dec    = data_be_i;
                    transaction    = T_RAM;
                end else if (data_addr_i == 32'h1000_0000) begin
                    print_wdata = data_wdata_i;
                    print_valid = '1;

                end else if (data_addr_i == 32'h2000_0000) begin
                    if (data_wdata_i == 123456789)
                        tests_passed_o = '1;
                    else if (data_wdata_i == 1)
                        tests_failed_o = '1;

                end else if (data_addr_i == 32'h2000_0004) begin
                    exit_valid_o = '1;
                    exit_value_o = data_wdata_i;

                end else if (data_addr_i == 32'h2000_0008) begin
                    // sets signature begin
                    sig_begin_d = data_wdata_i;

                end else if (data_addr_i == 32'h2000_000C) begin
                    // sets signature end
                    sig_end_d = data_wdata_i;

                end else if (data_addr_i == 32'h2000_0010) begin
                    // halt and dump signature
                    automatic string sig_file;
                    automatic bit use_sig_file;
                    automatic integer sig_fd;
                    automatic integer errno;
                    automatic string error_str;

                    if ($value$plusargs("signature=%s", sig_file)) begin
                        sig_fd = $fopen(sig_file, "w");
                        if (sig_fd == 0) begin
`ifndef VERILATOR
                            errno = $ferror(sig_fd, error_str);
                            $error(error_str);
`else
                            $error("can't open file");
`endif
                            use_sig_file = 1'b0;
                        end else begin
                            use_sig_file = 1'b1;
                        end
                    end

                    $display("Dumping signature");
                    for (logic [31:0] addr = sig_begin_q; addr < sig_end_q; addr +=4) begin
                        $display("%x%x%x%x",
                            dp_ram_i.mem[addr+3],
                            dp_ram_i.mem[addr+2],
                            dp_ram_i.mem[addr+1],
                            dp_ram_i.mem[addr+0]);
                        if (use_sig_file) begin
                            $fdisplay(sig_fd, "%x%x%x%x",
                                dp_ram_i.mem[addr+3],
                                dp_ram_i.mem[addr+2],
                                dp_ram_i.mem[addr+1],
                                dp_ram_i.mem[addr+0]);
                        end
                    end
                    // end simulation
                    exit_valid_o = '1;
                    exit_value_o = '0;

                end else if (data_addr_i == 32'h1500_0000) begin
                    timer_wdata = data_wdata_i;
                    timer_reg_valid = '1;

                end else if (data_addr_i == 32'h1500_0004) begin
                    timer_wdata = data_wdata_i;
                    timer_val_valid = '1;

                end else if (data_addr_i[31:16] == 16'h1600) begin
                    rnd_stall_req   = data_req_i;
                    rnd_stall_wdata = data_wdata_i;
                    rnd_stall_addr  = data_addr_i;
                    rnd_stall_we    = data_we_i;
                end else begin
                    // out of bounds write
                end

            end else begin // handle reads
                if (data_addr_i < 2 ** RAM_ADDR_WIDTH) begin
                    select_rdata_d = RAM;

                    data_req_dec   = data_req_i;
                    data_addr_dec  = data_addr_i[RAM_ADDR_WIDTH-1:0];
                    data_wdata_dec = data_wdata_i;
                    data_we_dec    = data_we_i;
                    data_be_dec    = data_be_i;
                    transaction    = T_RAM;
                end else if (data_addr_i[31:16] == 16'h1600) begin
                    select_rdata_d = RND_STALL;

                    rnd_stall_req      = data_req_i;
                    rnd_stall_wdata    = data_wdata_i;
                    rnd_stall_addr     = data_addr_i;
                    rnd_stall_we       = data_we_i;
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
      || data_addr_i == 32'h1000_0000
      || data_addr_i == 32'h1500_0000
      || data_addr_i == 32'h1500_0004
      || data_addr_i == 32'h2000_0000
      || data_addr_i == 32'h2000_0004
      || data_addr_i == 32'h2000_0008
      || data_addr_i == 32'h2000_000c
      || data_addr_i == 32'h2000_0010
      || data_addr_i[31:16] == 16'h1600))
        else $fatal("out of bounds write to %08x with %08x",
                    data_addr_i, data_wdata_i);
`endif

    // make sure we select the proper read data
    always_comb begin: read_mux
        data_rdata_o = '0;

        if(select_rdata_q == RAM) begin
            data_rdata_o = core_data_rdata;
        end else if(select_rdata_q == RND_STALL) begin
`ifndef VERILATOR
            data_rdata_o = rnd_stall_rdata;
`else
            $display("out of bounds read from %08x\nRandom stall generator is not supported with Verilator", data_addr_i);
            $fatal(2);
`endif
        end else if (select_rdata_q == ERR) begin
            $display("out of bounds read from %08x", data_addr_i);
            $fatal(2);
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


    assign irq_id_o = irq_q ? TIMER_IRQ_ID : RND_IRQ_ID;
    assign irq_o    = irq_q | rnd_irq;

    // Control timer. We need one to have some kind of timeout for tests that
    // get stuck in some loop. The riscv-tests also mandate that. Enable timer
    // interrupt by writing 1 to timer_irq_mask_q. Write initial value to
    // timer_cnt_q which gets counted down each cycle. When it transitions from
    // 1 to 0, and interrupt request (irq_q) is made (masked by timer_irq_mask_q).
    always_ff @(posedge clk_i, negedge rst_ni) begin: tb_timer
        if(~rst_ni) begin
            timer_irq_mask_q <= '0;
            timer_cnt_q      <= '0;
            irq_q            <= '0;
            for(int i=0; i<RND_STALL_REGS; i++) begin
                rnd_stall_regs[i] <= '0;
            end
            rnd_stall_rdata  <= '0;
        end else begin
            // set timer irq mask
            if(timer_reg_valid) begin
                timer_irq_mask_q <= timer_wdata;

            // write timer value
            end else if(timer_val_valid) begin
                timer_cnt_q <= timer_wdata;

            end else if(rnd_stall_req) begin
                if(rnd_stall_we)
                    rnd_stall_regs[rnd_stall_addr[5:2]] <= rnd_stall_wdata;
                else
                    rnd_stall_rdata <= rnd_stall_regs[rnd_stall_addr[5:2]];
            end else begin
                if(timer_cnt_q > 0)
                    timer_cnt_q <= timer_cnt_q - 1;

                if(timer_cnt_q == 1)
                    irq_q <= 1'b1 && timer_irq_mask_q[TIMER_IRQ_ID];

                if(irq_ack_i == 1'b1 && irq_id_i == TIMER_IRQ_ID)
                    irq_q <= '0;

            end
        end
    end

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
         .wdata_a_i ( '0              ),	// Not writing so ignored
         .rdata_a_o ( ram_instr_rdata ),
         .we_a_i    ( '0              ),
         .be_a_i    ( 4'b1111         ),	// Always want 32-bits

         .en_b_i    ( ram_data_req    ),
         .addr_b_i  ( ram_data_addr   ),
         .wdata_b_i ( ram_data_wdata  ),
         .rdata_b_o ( ram_data_rdata  ),
         .we_b_i    ( ram_data_we     ),
         .be_b_i    ( ram_data_be     ));


    // signature range
    always_ff @(posedge clk_i, negedge rst_ni) begin
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
            data_rvalid_q  <= '0;
            instr_rvalid_q <= '0;
            state_valid_q  <= IDLE;

        end else begin
            select_rdata_q <= select_rdata_d;
            data_rvalid_q  <= ram_data_req;
            instr_rvalid_q <= ram_instr_req;
            state_valid_q  <= state_valid_n;

        end
    end

    // do the handshacking stuff by assuming we always react in one cycle
    always_comb
    begin
    data_gnt_o    = 1'b0;
    data_rvalid_o = 1'b0;
    state_valid_n = state_valid_q;

        unique case(state_valid_q)

            IDLE:
            begin
                if(data_req_i) begin
                    if(transaction == T_RAM) begin
                        data_gnt_o    = ram_data_gnt;
                        if(ram_data_gnt) begin
                            state_valid_n = WAIT_RAM_VALID;
                        end else begin
                            state_valid_n = WAIT_RAM_GNT;
                        end
                    end else begin
                        state_valid_n = PERIPHEARL_VALID;
                        data_gnt_o    = 1'b1;
                    end
                end
            end

            PERIPHEARL_VALID:
            begin
                data_rvalid_o  = 1'b1;
                if(data_req_i) begin
                    if(transaction == T_RAM) begin
                        data_gnt_o    = ram_data_gnt;
                        if(ram_data_gnt) begin
                            state_valid_n = WAIT_RAM_VALID;
                        end else begin
                            state_valid_n = WAIT_RAM_GNT;
                        end
                    end else begin
                        state_valid_n = PERIPHEARL_VALID;
                        data_gnt_o    = 1'b1;
                    end
                end else state_valid_n = IDLE;
            end

            WAIT_RAM_GNT:
            begin
                data_rvalid_o  = 1'b0;
                if(data_req_i) begin
                    data_gnt_o = ram_data_gnt;
                    if(ram_data_gnt) begin
                        state_valid_n = WAIT_RAM_VALID;
                    end else begin
                        state_valid_n = WAIT_RAM_GNT;
                    end
                end else state_valid_n = IDLE;
            end

            WAIT_RAM_VALID:
            begin
                data_rvalid_o  = ram_data_valid;
                if(ram_data_valid) begin
                    if(data_req_i) begin
                        if(transaction == RAM) begin
                            data_gnt_o    = ram_data_gnt;
                            if(ram_data_gnt) begin
                                state_valid_n = WAIT_RAM_VALID;
                            end else begin
                                state_valid_n = WAIT_RAM_GNT;
                            end
                        end else begin
                            state_valid_n = PERIPHEARL_VALID;
                            data_gnt_o    = 1'b1;
                        end
                    end else state_valid_n = IDLE;
                end
            end

            default: begin
            end
        endcase

    end

    assign instr_gnt_o    = ram_instr_gnt;
    assign instr_rvalid_o = ram_instr_valid;
    assign instr_rdata_o  = core_instr_rdata;


  always_comb
  begin
    ram_instr_req    = instr_req_i;
    ram_instr_addr   = instr_addr_i;
    ram_instr_gnt    = instr_req_i;
    ram_instr_valid  = instr_rvalid_q;
    core_instr_rdata = ram_instr_rdata;

    ram_data_req     = data_req_dec;
    ram_data_addr    = data_addr_dec;
    ram_data_gnt     = data_req_dec;
    ram_data_valid   = data_rvalid_q;
    core_data_rdata  = ram_data_rdata;
    ram_data_wdata   = data_wdata_dec;
    ram_data_we      = data_we_dec;
    ram_data_be      = data_be_dec;

`ifndef VERILATOR
    if(rnd_stall_regs[0]) begin
        ram_instr_req    = rnd_stall_instr_req;
        ram_instr_addr   = rnd_stall_instr_addr;
        ram_instr_gnt    = rnd_stall_instr_gnt;
        ram_instr_valid  = rnd_stall_instr_valid;
        core_instr_rdata = rnd_stall_instr_rdata;
    end
    if(rnd_stall_regs[1]) begin
        ram_data_req     = rnd_stall_data_req;
        ram_data_addr    = rnd_stall_data_addr;
        ram_data_gnt     = rnd_stall_data_gnt;
        ram_data_valid   = rnd_stall_data_valid;
        core_data_rdata  = rnd_stall_data_rdata;
        ram_data_wdata   = rnd_stall_data_wdata;
        ram_data_we      = rnd_stall_data_we;
        ram_data_be      = rnd_stall_data_be;
    end
`endif
  end

`ifndef VERILATOR
  riscv_random_stall
  #(.DATA_WIDTH(INSTR_RDATA_WIDTH))
  instr_random_stalls
  (
    .clk_i              ( clk_i                  ),
    .rst_ni             ( rst_ni                 ),

    .grant_mem_i        ( rnd_stall_instr_req    ),
    .rvalid_mem_i       ( instr_rvalid_q         ),
    .rdata_mem_i        ( ram_instr_rdata        ),

    .grant_core_o       ( rnd_stall_instr_gnt    ),
    .rvalid_core_o      ( rnd_stall_instr_valid  ),
    .rdata_core_o       ( rnd_stall_instr_rdata  ),

    .req_core_i         ( instr_req_i            ),
    .req_mem_o          ( rnd_stall_instr_req    ),

    .addr_core_i        ( instr_addr_i           ),
    .addr_mem_o         ( rnd_stall_instr_addr   ),

    .wdata_core_i       (                        ),
    .wdata_mem_o        (                        ),

    .we_core_i          (                        ),
    .we_mem_o           (                        ),

    .be_core_i          (                        ),
    .be_mem_o           (                        ),

    .stall_mode_i       ( rnd_stall_regs[2]      ),
    .max_stall_i        ( rnd_stall_regs[4]      ),
    .gnt_stall_i        ( rnd_stall_regs[6]      ),
    .valid_stall_i      ( rnd_stall_regs[8]      )
    );

  riscv_random_stall
  #(.DATA_WIDTH(32))
  data_random_stalls
  (
    .clk_i              ( clk_i                  ),
    .rst_ni             ( rst_ni                 ),

    .grant_mem_i        ( rnd_stall_data_req     ),
    .rvalid_mem_i       ( data_rvalid_q          ),
    .rdata_mem_i        ( ram_data_rdata         ),

    .grant_core_o       ( rnd_stall_data_gnt     ),
    .rvalid_core_o      ( rnd_stall_data_valid   ),
    .rdata_core_o       ( rnd_stall_data_rdata   ),

    .req_core_i         ( data_req_dec           ),
    .req_mem_o          ( rnd_stall_data_req     ),

    .addr_core_i        ( data_addr_dec          ),
    .addr_mem_o         ( rnd_stall_data_addr    ),

    .wdata_core_i       ( data_wdata_dec         ),
    .wdata_mem_o        ( rnd_stall_data_wdata   ),

    .we_core_i          ( data_we_dec            ),
    .we_mem_o           ( rnd_stall_data_we      ),

    .be_core_i          ( data_be_dec            ),
    .be_mem_o           ( rnd_stall_data_be      ),

    .stall_mode_i       ( rnd_stall_regs[3]      ),
    .max_stall_i        ( rnd_stall_regs[5]      ),
    .gnt_stall_i        ( rnd_stall_regs[7]      ),
    .valid_stall_i      ( rnd_stall_regs[9]      )
    );

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

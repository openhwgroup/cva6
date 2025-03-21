// Licensed under the Solderpad Hardware License v 2.1 (the “License”); you may not use this file 
// except in compliance with the License, or, at your option, the Apache License version 2.0. You 
// may obtain a copy of the License at

// https://solderpad.org/licenses/SHL-2.1/

// Unless required by applicable law or agreed to in writing, any work distributed under the 
// License is distributed on an “AS IS” BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, 
// either express or implied. See the License for the specific language governing permissions and 
// limitations under the License.

// Author:  Umberto Laghi
// Contact: umberto.laghi@studio.unibo.it
// Github:  @ubolakes
// Contributors: 
// Darshak Sheladiya, SYSGO GmbH
// Maxime COLSON, Thales

/* TOP LEVEL MODULE */

module cva6_te_connector #(
    parameter config_pkg::cva6_cfg_t CVA6Cfg = config_pkg::cva6_cfg_empty,
    parameter N = 2,  // max number of special inst in a cycle
    parameter FIFO_DEPTH = 16  // number of entries in each FIFO
) (
    input logic clk_i,
    input logic rst_ni,

    /* data from the CPU */
    // inputs
    input logic [CVA6Cfg.NrCommitPorts-1:0] valid_i,  // commit_ack in cva6
    // necessary inputs from scoreboard_entry_t
    input logic [CVA6Cfg.NrCommitPorts-1:0][CVA6Cfg.XLEN-1:0] pc_i,
    input ariane_pkg::fu_op [CVA6Cfg.NrCommitPorts-1:0] op_i,
    input logic [CVA6Cfg.NrCommitPorts-1:0] is_compressed_i,
    // necessary inputs from bp_resolve_t
    input logic branch_valid_i,
    input logic is_taken_i,
    // necessary inputs from exception_t
    input logic ex_valid_i,
    input logic [CVA6Cfg.XLEN-1:0] tval_i,
    input logic [CVA6Cfg.XLEN-1:0] cause_i,
    input riscv::priv_lvl_t priv_lvl_i,
    //input logic [connector_pkg::CTX_LEN-1:0]                context_i, // non mandatory
    input logic [63:0] time_i,  // non mandatory
    //input logic [connector_pkg::CTYPE_LEN-1:0]              ctype_i, // non mandatory
    //input logic [CVA6Cfg.NrCommitPorts-1:0][connector_pkg::SIJ_LEN-1]        sijump_i // non mandatory

    // outputs
    /* the output of the module goes directly into the trace_encoder module */
    output logic [N-1:0] valid_o,
    output logic [N-1:0][connector_pkg::IRETIRE_LEN-1:0] iretire_o,
    output logic [N-1:0] ilastsize_o,
    output logic [N-1:0][connector_pkg::ITYPE_LEN-1:0] itype_o,
    output logic [connector_pkg::CAUSE_LEN-1:0] cause_o,
    output logic [CVA6Cfg.XLEN-1:0] tval_o,
    output riscv::priv_lvl_t  priv_o,
    output logic [N-1:0][CVA6Cfg.XLEN-1:0] iaddr_o,
    //output logic [connector_pkg::CTX_LEN-1:0]               context_o, // non mandatory
    output logic [63:0] time_o  // non mandatory
    //output logic [connector_pkg::CTYPE_LEN-1:0]             ctype_o, // non mandatory
    //output logic [connector_pkg::SIJ_LEN-1]                 sijump_o // non mandatory
);
  // struct to store data inside the uop FIFO
  localparam type uop_entry_t = struct packed {
    logic                 valid;
    logic [CVA6Cfg.XLEN-1:0]      pc;
    logic [connector_pkg::ITYPE_LEN-1:0] itype;       // determined in itype detector
    logic                 compressed;
    riscv::priv_lvl_t priv;
  };
  // entries for the FIFOs
  uop_entry_t uop_entry_i[CVA6Cfg.NrCommitPorts-1:0], uop_entry_o[CVA6Cfg.NrCommitPorts-1:0];
  uop_entry_t uop_entry_mux;
  logic [connector_pkg::ITYPE_LEN-1:0] itype[CVA6Cfg.NrCommitPorts];
  // FIFOs management
  logic pop[CVA6Cfg.NrCommitPorts-1:0];  // signal to pop FIFOs
  logic empty[CVA6Cfg.NrCommitPorts-1:0];  // signal used to enable counter
  logic full[CVA6Cfg.NrCommitPorts-1:0];
  logic push_enable[CVA6Cfg.NrCommitPorts-1:0];
  // mux arbiter management
  logic [$clog2(CVA6Cfg.NrCommitPorts-1):0] mux_arb_val;
  logic clear_mux_arb;
  logic enable_mux_arb;
  // demux arbiter management
  logic [$clog2(N):0] demux_arb_val;
  logic clear_demux_arb;
  logic enable_demux_arb;
  // itype_detector
  logic is_taken_d, is_taken_q;
  logic interrupt;
  // block counter management
  logic n_blocks_full;
  logic n_blocks_empty;
  logic [$clog2(N):0] n_blocks_i, n_blocks_o;
  logic n_blocks_push;
  logic n_blocks_pop;
    // struct to store exc and int infos
  localparam type exc_info_t = struct packed {
    logic [connector_pkg::CAUSE_LEN-1:0] cause;
    logic [CVA6Cfg.XLEN-1:0] tval;
  } ;
  // exception signals
  exc_info_t exc_info_i, exc_info_o;
  logic                                                                  exc_info_full;
  logic                                                                  exc_info_empty;
  logic                                                                  exc_info_pop;
  // signals to store blocks
  logic                                                                  valid_fsm;
  logic [                         N-1:0][connector_pkg::IRETIRE_LEN-1:0] iretire_q;
  logic [                         N-1:0]                                 ilastsize_q;
  logic [                         N-1:0][  connector_pkg::ITYPE_LEN-1:0] itype_q;
  logic [  connector_pkg::CAUSE_LEN-1:0]                                 cause_q;
  logic [       CVA6Cfg.XLEN-1:0]                                 tval_q;
  logic [                         N-1:0][       CVA6Cfg.XLEN-1:0] iaddr_q;

  logic [connector_pkg::IRETIRE_LEN-1:0]                                 iretire_d;
  logic                                                                  ilastsize_d;
  logic [  connector_pkg::ITYPE_LEN-1:0]                                 itype_d;
  logic [  connector_pkg::CAUSE_LEN-1:0]                                 cause_d;
  logic [       CVA6Cfg.XLEN-1:0]                                 tval_d;
  logic [       CVA6Cfg.XLEN-1:0]                                 iaddr_d;

  // assignments
  assign pop[0] =    (mux_arb_val == 0 ||
                uop_entry_o[0].itype == 1 ||
                uop_entry_o[0].itype == 2) &&
                !empty[0];
  assign pop[1] =    (mux_arb_val == 1 ||
                uop_entry_o[1].itype == 1 ||
                uop_entry_o[1].itype == 2) &&
                !empty[1];

  assign clear_mux_arb =  (mux_arb_val == CVA6Cfg.NrCommitPorts-1 ||
                        uop_entry_o[0].itype == 1 ||
                        uop_entry_o[0].itype == 2) &&
                        !empty[0];
  assign enable_mux_arb = !empty[0];  // the counter goes on if FIFOs are not empty
  assign is_taken_d = is_taken_i;
  assign n_blocks_push = !n_blocks_full && n_blocks_i > 0;
  assign clear_demux_arb = n_blocks_pop; // demux_arb_val+1 == n_blocks_o && n_blocks_o > 0 && |valid_o;
  assign enable_demux_arb = valid_fsm;  // && n_blocks_o > 1;
  assign exc_info_pop = valid_o[0] && (itype_o[0] == 1 || itype_o[0] == 2) && !exc_info_empty;
  assign exc_info_i.tval = tval_i;
  assign exc_info_i.cause = cause_i[connector_pkg::CAUSE_LEN-1:0];
  assign uop_entry_mux = empty[0] ? '0 : uop_entry_o[mux_arb_val];
  assign interrupt = cause_i[CVA6Cfg.XLEN-1];  // determinated based on the MSB of cause

  /* itype_detectors */
  for (genvar i = 0; i < CVA6Cfg.NrCommitPorts; i++) begin
    itype_detector i_itype_detector (
        .valid_i       (valid_i[i]),
        .exception_i   (ex_valid_i),
        .interrupt_i   (interrupt),
        .op_i          (op_i[i]),
        .branch_taken_i(is_taken_q),
        .itype_o       (itype[i])
    );
  end

  /* FIFOs */
  /* commit ports FIFOs */
  for (genvar i = 0; i < CVA6Cfg.NrCommitPorts; i++) begin
    fifo_v3 #(
        .DEPTH(FIFO_DEPTH),
        .dtype(uop_entry_t)
    ) i_fifo_uop (
        .clk_i     (clk_i),
        .rst_ni    (rst_ni),
        .flush_i   ('0),
        .testmode_i('0),
        .full_o    (full[i]),
        .empty_o   (empty[i]),
        .usage_o   (),
        .data_i    (uop_entry_i[i]),
        .push_i    (push_enable[i] && !full[i]),
        .data_o    (uop_entry_o[i]),
        .pop_i     (pop[i])
    );
  end

  // FIFO to store the n_blocks
  fifo_v3 #(
      .DEPTH(FIFO_DEPTH),
      .dtype(exc_info_t)
  ) i_nblock_fifo (
      .clk_i     (clk_i),
      .rst_ni    (rst_ni),
      .flush_i   ('0),
      .testmode_i('0),
      .full_o    (exc_info_full),
      .empty_o   (exc_info_empty),
      .usage_o   (),
      .data_i    (exc_info_i),
      .push_i    ((ex_valid_i || interrupt) && !exc_info_full),
      .data_o    (exc_info_o),
      .pop_i     (exc_info_pop)
  );

  // FIFO to store exc and int info
  fifo_v3 #(
      .DEPTH(FIFO_DEPTH),
      .DATA_WIDTH($clog2(N) + 1)
  ) i_exc_info_fifo (
      .clk_i     (clk_i),
      .rst_ni    (rst_ni),
      .flush_i   ('0),
      .testmode_i('0),
      .full_o    (n_blocks_full),
      .empty_o   (n_blocks_empty),
      .usage_o   (),
      .data_i    (n_blocks_i),
      .push_i    (n_blocks_push),
      .data_o    (n_blocks_o),
      .pop_i     (n_blocks_pop)
  );

  // mux arbiter for serialization
  counter #(
      .WIDTH($clog2(CVA6Cfg.NrCommitPorts)), //MC: Mentionned $clog2(NRET-1) in arch description but why?
      .STICKY_OVERFLOW('0)
  ) i_mux_arbiter (  // change name?
      .clk_i     (clk_i),
      .rst_ni    (rst_ni),
      .clear_i   (clear_mux_arb),
      .en_i      (enable_mux_arb),
      .load_i    ('0),
      .down_i    ('0),
      .d_i       ('0),
      .q_o       (mux_arb_val),
      .overflow_o()
  );

  // fsm to create blocks instantiation
  fsm #(
      .CVA6Cfg(CVA6Cfg),
      .uop_entry_t(uop_entry_t)
  ) i_fsm (
      .clk_i      (clk_i),
      .rst_ni     (rst_ni),
      .uop_entry_i(uop_entry_mux),
      .cause_i    (exc_info_o.cause),
      .tval_i     (exc_info_o.tval),
      .valid_o    (valid_fsm),
      .iretire_o  (iretire_d),
      .ilastsize_o(ilastsize_d),
      .itype_o    (itype_d),
      .cause_o    (cause_d),
      .tval_o     (tval_d),
      .priv_o     (priv_o),
      .iaddr_o    (iaddr_d)
  );

  // demux arbiter to choose register
  counter #(
      .WIDTH($clog2(N) + 1), //MC: again why $clog2(N)+1 here and not $clog2(N-1) or $clog2(N) as description suggested?
      .STICKY_OVERFLOW('0)
  ) i_demux_arbiter (
      .clk_i     (clk_i),
      .rst_ni    (rst_ni),
      .clear_i   (clear_demux_arb),
      .en_i      (enable_demux_arb),
      .load_i    ('0),
      .down_i    ('0),
      .d_i       ('0),
      .q_o       (demux_arb_val),
      .overflow_o()
  );

  always_comb begin
    // init
    n_blocks_i   = '0;
    n_blocks_pop = '0;
    for (int i = 0; i < N; i++) begin
      // output
      valid_o[i] = '0;
      iretire_o[i] = '0;
      ilastsize_o[i] = '0;
      itype_o[i] = '0;
      cause_o = '0;
      tval_o = '0;
      iaddr_o[i] = '0;
      // uop_entry
      uop_entry_i[i].valid = '0;
      uop_entry_i[i].pc = '0;
      uop_entry_i[i].itype = '0;
      uop_entry_i[i].compressed = '0;
      uop_entry_i[i].priv = riscv::PRIV_LVL_U;
    end


    // populating uop FIFO entries
    for (int i = 0; i < CVA6Cfg.NrCommitPorts; i++) begin
      uop_entry_i[i].valid = valid_i[i];
      uop_entry_i[i].pc = pc_i[i];
      uop_entry_i[i].itype = itype[i];
      uop_entry_i[i].compressed = is_compressed_i[i];
      uop_entry_i[i].priv = priv_lvl_i;
      push_enable[i] = '0;
    end

    // enabling push in input FIFOs
    for (int i = 0; i < CVA6Cfg.NrCommitPorts; i++) begin
      if ((uop_entry_i[i].itype == 1 || uop_entry_i[i].itype == 2) ||
            ((uop_entry_i[i].itype == 0 || uop_entry_i[i].itype > 2) && 
            uop_entry_i[i].valid)) begin
        push_enable[i] = 1;
      end
    end

    // counting the blocks to emit in one cycle
    for (int i = 0; i < CVA6Cfg.NrCommitPorts; i++) begin
      if ((uop_entry_i[i].itype > 2 && uop_entry_i[i].valid)) begin
        n_blocks_i += 1;
      end else if (uop_entry_i[i].itype == 1 || uop_entry_i[i].itype == 2) begin
        /* since the exc and int signal are connected to all itype detectors,
               a int would require CVA6Cfg.NrCommitPorts blocks, but it's not true and breaks all 
               the system downstream.
               That's because it would store CVA6Cfg.NrCommitPorts blocks in the FIFO, but since 
               the MUX allows only one uop_entry with itype == 1, the CVA6Cfg.NrCommitPorts blocks 
               would never be produced, causing a deadlock. */
        n_blocks_i = 1;
      end
    end

    // checking if blocks are ready to output
    // first case: waiting for one block
    // when it outputs one block can be exc or int
    if (n_blocks_o == 1 && valid_fsm && !n_blocks_empty) begin
      valid_o[0] = '1;
      iretire_o[0] = iretire_d;
      ilastsize_o[0] = ilastsize_d;
      itype_o[0] = itype_d;
      iaddr_o[0] = iaddr_d;
      // setting cause and tval for exc or int
      if (itype_o[0] == 1 || itype_o[0] == 2) begin
        cause_o = cause_d;
        tval_o  = tval_d;
      end
      // popping the nblocks FIFO
      n_blocks_pop = '1;
    end

    // second case: waiting for N blocks
    // when more blocks are output they 
    // are not exc or int, but other disc
    if (n_blocks_o > 1 && demux_arb_val == n_blocks_o - 1 && valid_fsm && n_blocks_empty) begin
      // leaving to 0 cause and tval since they are not necessary
      // setting block specific data
      for (int i = 0; i < n_blocks_o; i++) begin
        valid_o[i] = '1;
        if (i == n_blocks_o - 1) begin
          iretire_o[i] = iretire_d;
          ilastsize_o[i] = ilastsize_d;
          itype_o[i] = itype_d;
          iaddr_o[i] = iaddr_d;
        end else begin
          iretire_o[i] = iretire_q[i];
          ilastsize_o[i] = ilastsize_q[i];
          itype_o[i] = itype_q[i];
          iaddr_o[i] = iaddr_q[i];
        end
      end
      // popping the nblocks FIFO
      n_blocks_pop = '1;
    end
  end

  always_ff @(posedge clk_i, negedge rst_ni) begin
    if (!rst_ni) begin
      is_taken_q <= '0;
      for (int i = 0; i < N; i++) begin
        iretire_q[i] <= '0;
        ilastsize_q[i] <= '0;
        itype_q[i] <= '0;
        cause_q <= '0;
        tval_q <= '0;
        iaddr_q[i] <= '0;
      end
    end else begin
      if (branch_valid_i) begin
        is_taken_q <= is_taken_d;
      end
      if (valid_fsm) begin
        iretire_q[demux_arb_val] <= iretire_d;
        ilastsize_q[demux_arb_val] <= ilastsize_d;
        itype_q[demux_arb_val] <= itype_d;
        cause_q <= cause_d;
        tval_q <= tval_d;
        iaddr_q[demux_arb_val] <= iaddr_d;
      end
    end
  end


  assign time_o = time_i;


endmodule

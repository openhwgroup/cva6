// Copyright (c) 2020 ETH Zurich and University of Bologna
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// Authors:
// - Wolfgang Roenninger <wroennin@iis.ee.ethz.ch>
// - Andreas Kurth <akurth@iis.ee.ethz.ch>

// Description: A mailbox with two AXI4-Lite slave ports and associated interrupt requests.
//              See `doc/axi_lite_mailbox.md` for the documentation, including the definition
//              of parameters and ports.

`include "common_cells/registers.svh"

module axi_lite_mailbox #(
  parameter int unsigned MailboxDepth = 32'd0,
  parameter bit unsigned IrqEdgeTrig  = 1'b0,
  parameter bit unsigned IrqActHigh   = 1'b1,
  parameter int unsigned AxiAddrWidth = 32'd0,
  parameter int unsigned AxiDataWidth = 32'd0,
  parameter type         req_lite_t   = logic,
  parameter type         resp_lite_t  = logic,
  // DEPENDENT PARAMETERS, DO NOT OVERRIDE!
  parameter type         addr_t       = logic [AxiAddrWidth-1:0]
) (
  input  logic             clk_i,       // Clock
  input  logic             rst_ni,      // Asynchronous reset active low
  input  logic             test_i,      // Testmode enable
  // slave ports [1:0]
  input  req_lite_t  [1:0] slv_reqs_i,
  output resp_lite_t [1:0] slv_resps_o,
  output logic       [1:0] irq_o,       // interrupt output for each port
  input  addr_t      [1:0] base_addr_i  // base address for each port
);
  localparam int unsigned FifoUsageWidth = $clog2(MailboxDepth);
  typedef logic [AxiDataWidth-1:0] data_t;
  // usage type of the mailbox FIFO, also the type of the threshold comparison
  // is one bit wider, MSB is the fifo_full flag of the respective fifo
  typedef logic [FifoUsageWidth:0] usage_t;

  // signal declaration for the mailbox FIFO's, signal index is the port
  logic   [1:0] mbox_full,    mbox_empty;   // index is the instantiated mailbox FIFO
  logic   [1:0] mbox_push,    mbox_pop;     // index is port
  logic   [1:0] w_mbox_flush, r_mbox_flush; // index is port
  data_t  [1:0] mbox_w_data,  mbox_r_data;  // index is port
  usage_t [1:0] mbox_usage;                 // index is the instantiated mailbox FIFO
  // interrupt request from this slave port, level triggered, active high --> convert
  logic   [1:0] slv_irq;
  logic   [1:0] clear_irq;

  axi_lite_mailbox_slave #(
    .MailboxDepth ( MailboxDepth ),
    .AxiAddrWidth ( AxiAddrWidth ),
    .AxiDataWidth ( AxiDataWidth ),
    .req_lite_t   ( req_lite_t   ),
    .resp_lite_t  ( resp_lite_t  ),
    .addr_t       ( addr_t       ),
    .data_t       ( data_t       ),
    .usage_t      ( usage_t      )  // fill pointer from MBOX FIFO
  ) i_slv_port_0 (
    .clk_i,   // Clock
    .rst_ni,  // Asynchronous reset active low
    // slave port
    .slv_req_i      ( slv_reqs_i[0]   ),
    .slv_resp_o     ( slv_resps_o[0]  ),
    .base_addr_i    ( base_addr_i[0]  ), // base address for the slave port
    // write FIFO port
    .mbox_w_data_o  ( mbox_w_data[0]  ),
    .mbox_w_full_i  ( mbox_full[0]    ),
    .mbox_w_push_o  ( mbox_push[0]    ),
    .mbox_w_flush_o ( w_mbox_flush[0] ),
    .mbox_w_usage_i ( mbox_usage[0]   ),
    // read FIFO port
    .mbox_r_data_i  ( mbox_r_data[0]  ),
    .mbox_r_empty_i ( mbox_empty[1]   ),
    .mbox_r_pop_o   ( mbox_pop[0]     ),
    .mbox_r_flush_o ( r_mbox_flush[0] ),
    .mbox_r_usage_i ( mbox_usage[1]   ),
    // interrupt output, level triggered, active high, conversion in top
    .irq_o          ( slv_irq[0]      ),
    .clear_irq_o    ( clear_irq[0]    )
  );

  axi_lite_mailbox_slave #(
    .MailboxDepth ( MailboxDepth ),
    .AxiAddrWidth ( AxiAddrWidth ),
    .AxiDataWidth ( AxiDataWidth ),
    .req_lite_t   ( req_lite_t   ),
    .resp_lite_t  ( resp_lite_t  ),
    .addr_t       ( addr_t       ),
    .data_t       ( data_t       ),
    .usage_t      ( usage_t      )  // fill pointer from MBOX FIFO
  ) i_slv_port_1 (
    .clk_i,   // Clock
    .rst_ni,  // Asynchronous reset active low
    // slave port
    .slv_req_i      ( slv_reqs_i[1]   ),
    .slv_resp_o     ( slv_resps_o[1]  ),
    .base_addr_i    ( base_addr_i[1]  ), // base address for the slave port
    // write FIFO port
    .mbox_w_data_o  ( mbox_w_data[1]  ),
    .mbox_w_full_i  ( mbox_full[1]    ),
    .mbox_w_push_o  ( mbox_push[1]    ),
    .mbox_w_flush_o ( w_mbox_flush[1] ),
    .mbox_w_usage_i ( mbox_usage[1]   ),
    // read FIFO port
    .mbox_r_data_i  ( mbox_r_data[1]  ),
    .mbox_r_empty_i ( mbox_empty[0]   ),
    .mbox_r_pop_o   ( mbox_pop[1]     ),
    .mbox_r_flush_o ( r_mbox_flush[1] ),
    .mbox_r_usage_i ( mbox_usage[0]   ),
    // interrupt output, level triggered, active high, conversion in top
    .irq_o          ( slv_irq[1]      ),
    .clear_irq_o    ( clear_irq[1]    )
  );

  // the usage gets concatinated with the full flag to have consistent threshold detection
  logic [FifoUsageWidth-1:0] mbox_0_to_1_usage, mbox_1_to_0_usage;
  fifo_v3 #(
    .FALL_THROUGH ( 1'b0         ),
    .DEPTH        ( MailboxDepth ),
    .dtype        ( data_t       )
  ) i_mbox_0_to_1 (
    .clk_i,
    .rst_ni,
    .testmode_i( test_i                            ),
    .flush_i   ( w_mbox_flush[0] | r_mbox_flush[1] ),
    .full_o    ( mbox_full[0]                      ),
    .empty_o   ( mbox_empty[0]                     ),
    .usage_o   ( mbox_0_to_1_usage                 ),
    .data_i    ( mbox_w_data[0]                    ),
    .push_i    ( mbox_push[0]                      ),
    .data_o    ( mbox_r_data[1]                    ),
    .pop_i     ( mbox_pop[1]                       )
  );
  // assign the MSB of the FIFO to the correct usage signal
  assign mbox_usage[0] = {mbox_full[0], mbox_0_to_1_usage};

  fifo_v3 #(
    .FALL_THROUGH ( 1'b0         ),
    .DEPTH        ( MailboxDepth ),
    .dtype        ( data_t       )
  ) i_mbox_1_to_0 (
    .clk_i,
    .rst_ni,
    .testmode_i( test_i                            ),
    .flush_i   ( w_mbox_flush[1] | r_mbox_flush[0] ),
    .full_o    ( mbox_full[1]                      ),
    .empty_o   ( mbox_empty[1]                     ),
    .usage_o   ( mbox_1_to_0_usage                 ),
    .data_i    ( mbox_w_data[1]                    ),
    .push_i    ( mbox_push[1]                      ),
    .data_o    ( mbox_r_data[0]                    ),
    .pop_i     ( mbox_pop[0]                       )
  );
  assign mbox_usage[1] = {mbox_full[1], mbox_1_to_0_usage};

  for (genvar i = 0; i < 2; i++) begin : gen_irq_conversion
    if (IrqEdgeTrig) begin : gen_irq_edge
      logic irq_q, irq_d, update_irq;

      always_comb begin
        // default assignments
        irq_d      = irq_q;
        update_irq = 1'b0;
        // init the irq and pulse only on update
        irq_o[i]   = ~IrqActHigh;
        if (clear_irq[i]) begin
          irq_d      = 1'b0;
          update_irq = 1'b1;
        end else if (!irq_q && slv_irq[i]) begin
          irq_d      = 1'b1;
          update_irq = 1'b1;
          irq_o[i]   = IrqActHigh; // on update of the register pulse the irq signal
        end
      end

      `FFLARN(irq_q, irq_d, update_irq, '0, clk_i, rst_ni)
    end else begin : gen_irq_level
      assign irq_o[i] = (IrqActHigh) ? slv_irq[i] : ~slv_irq[i];
    end
  end

  // pragma translate_off
  `ifndef VERILATOR
  initial begin : proc_check_params
    mailbox_depth:  assert (MailboxDepth > 1) else $fatal(1, "MailboxDepth has to be at least 2");
    axi_addr_width: assert (AxiAddrWidth > 0) else $fatal(1, "AxiAddrWidth has to be > 0");
    axi_data_width: assert (AxiDataWidth > 0) else $fatal(1, "AxiDataWidth has to be > 0");
  end
  `endif
  // pragma translate_on
endmodule

`include "axi/typedef.svh"

// slave port module
module axi_lite_mailbox_slave #(
  parameter int unsigned MailboxDepth = 32'd16,
  parameter int unsigned AxiAddrWidth = 32'd32,
  parameter int unsigned AxiDataWidth = 32'd32,
  parameter type         req_lite_t   = logic,
  parameter type         resp_lite_t  = logic,
  parameter type         addr_t       = logic [AxiAddrWidth-1:0],
  parameter type         data_t       = logic [AxiDataWidth-1:0],
  parameter type         usage_t      = logic                     // fill pointer from MBOX FIFO
) (
  input  logic       clk_i,   // Clock
  input  logic       rst_ni,  // Asynchronous reset active low
  // slave port
  input  req_lite_t  slv_req_i,
  output resp_lite_t slv_resp_o,
  input  addr_t      base_addr_i, // base address for the slave port
  // write FIFO port
  output data_t      mbox_w_data_o,
  input  logic       mbox_w_full_i,
  output logic       mbox_w_push_o,
  output logic       mbox_w_flush_o,
  input  usage_t     mbox_w_usage_i,
  // read FIFO port
  input  data_t      mbox_r_data_i,
  input  logic       mbox_r_empty_i,
  output logic       mbox_r_pop_o,
  output logic       mbox_r_flush_o,
  input  usage_t     mbox_r_usage_i,
  // interrupt output, level triggered, active high, conversion in top
  output logic       irq_o,
  output logic       clear_irq_o // clear the edge trigger irq register in `axi_lite_mailbox`
);

  `AXI_LITE_TYPEDEF_B_CHAN_T(b_chan_lite_t)
  `AXI_LITE_TYPEDEF_R_CHAN_T(r_chan_lite_t, data_t)

  localparam int unsigned NoRegs = 32'd10;
  typedef enum logic [3:0] {
    MBOXW  = 4'd0, // Mailbox write register
    MBOXR  = 4'd1, // Mailbox read register
    STATUS = 4'd2, // Mailbox status register
    ERROR  = 4'd3, // Mailbox error register
    WIRQT  = 4'd4, // Write interrupt request threshold register
    RIRQT  = 4'd5, // Read interrupt request threshold register
    IRQS   = 4'd6, // Interrupt request status register
    IRQEN  = 4'd7, // Interrupt request enable register
    IRQP   = 4'd8, // Interrupt request pending register
    CTRL   = 4'd9  // Mailbox control register
  } reg_e;
  // address map rule struct, as required from `addr_decode` from `common_cells`
  typedef struct packed {
    int unsigned idx;
    addr_t       start_addr;
    addr_t       end_addr;
  } rule_t;
  // output type of the address decoders, to be casted onto the enum type `reg_e`
  typedef logic [$clog2(NoRegs)-1:0] idx_t;

  // LITE response signals, go into the output spill registers to prevent combinational response
  logic         b_valid, b_ready;
  b_chan_lite_t b_chan;
  logic         r_valid, r_ready;
  r_chan_lite_t r_chan;
  // address map generation
  rule_t [NoRegs-1:0] addr_map;
  for (genvar i = 0; i < NoRegs; i++) begin : gen_addr_map
    assign addr_map[i] = '{
        idx:        i,
        start_addr: base_addr_i +  i      * (AxiDataWidth / 8),
        end_addr:   base_addr_i + (i + 1) * (AxiDataWidth / 8),
        default:    '0
    };
  end
  // address decode flags
  idx_t w_reg_idx,   r_reg_idx;
  logic dec_w_valid, dec_r_valid;

  // mailbox register signal declarations, get extended when read, some of these regs
  // are build combinationally, indicated by the absence of the `*_d` signal

  logic [3:0] status_q;           // mailbox status register (read only)
  logic [1:0] error_q,   error_d; // mailbox error register
  data_t      wirqt_q,   wirqt_d; // write interrupt request threshold register
  data_t      rirqt_q,   rirqt_d; // read interrupt request threshold register
  logic [2:0] irqs_q,    irqs_d;  // interrupt request status register
  logic [2:0] irqen_q,   irqen_d; // interrupt request enable register
  logic [2:0] irqp_q;             // interrupt request pending register (read only)
  logic [1:0] ctrl_q;             // mailbox control register
  logic       update_regs;        // register enable signal

  // register instantiation
  `FFLARN(error_q, error_d, update_regs, '0, clk_i, rst_ni)
  `FFLARN(wirqt_q, wirqt_d, update_regs, '0, clk_i, rst_ni)
  `FFLARN(rirqt_q, rirqt_d, update_regs, '0, clk_i, rst_ni)
  `FFLARN(irqs_q, irqs_d, update_regs, '0, clk_i, rst_ni)
  `FFLARN(irqen_q, irqen_d, update_regs, '0, clk_i, rst_ni)

  // Mailbox FIFO data assignments
  for (genvar i = 0; i < (AxiDataWidth/8); i++) begin : gen_w_mbox_data
    assign mbox_w_data_o[i*8+:8] = slv_req_i.w.strb[i] ? slv_req_i.w.data[i*8+:8] : '0;
  end

  // combinational mailbox register assignments, for the read only registers
  assign status_q = { mbox_r_usage_i > usage_t'(rirqt_q),
                      mbox_w_usage_i > usage_t'(wirqt_q),
                      mbox_w_full_i,
                      mbox_r_empty_i };
  assign irqp_q   = irqs_q & irqen_q;                 // interrupt request pending is bit wise and
  assign ctrl_q   = {mbox_r_flush_o, mbox_w_flush_o}; // read ctrl_q is flush signals
  assign irq_o    = |irqp_q;                          // generate an active-high level irq

  always_comb begin
    // slave port channel outputs for the AW, W and R channel, other driven from spill register
    slv_resp_o.aw_ready = 1'b0;
    slv_resp_o.w_ready  = 1'b0;
    b_chan              = '{resp: axi_pkg::RESP_SLVERR};
    b_valid             = 1'b0;
    slv_resp_o.ar_ready = 1'b0;
    r_chan              = '{data: '0, resp: axi_pkg::RESP_SLVERR};
    r_valid             = 1'b0;
    // Default assignments for the internal registers
    error_d     = error_q;   // mailbox error register
    wirqt_d     = wirqt_q;   // write interrupt request threshold register
    rirqt_d     = rirqt_q;   // read interrupt request threshold register
    irqs_d      = irqs_q;    // interrupt request status register
    irqen_d     = irqen_q;   // interrupt request enable register
    update_regs = 1'b0;      // register update enable signal
    // MBOX FIFO control signals
    mbox_w_push_o  = 1'b0;
    mbox_w_flush_o = 1'b0;
    mbox_r_pop_o   = 1'b0;
    mbox_r_flush_o = 1'b0;
    // clear the edge triggered irq register if it is instantiated
    clear_irq_o    = 1'b0;

    // -------------------------------------------
    // Set the read and write interrupt FF (irqs), when the threshold triggers
    // -------------------------------------------
    // strict threshold interrupt these fields get cleared by acknowledge on write onto the register
    // read trigger, see status_q above
    if (!irqs_q[1] && status_q[3]) begin
      irqs_d[1]   = 1'b1;
      update_regs = 1'b1;
    end
    // write trigger, see status_q above
    if (!irqs_q[0] && status_q[2]) begin
      irqs_d[0]   = 1'b1;
      update_regs = 1'b1;
    end

    // -------------------------------------------
    // Read registers
    // -------------------------------------------
    // The logic of the read and write channels have to be in the same `always_comb` block.
    // The reason is that the error register could be cleared in the same cycle as a read from
    // the mailbox FIFO generates a new error. In this case the error is NOT cleared. Instead
    // it will generate a new irq when it is edge triggered, or the level will stay at its
    // active state.

    // Check if there is a pending read request on the slave port.
    if (slv_req_i.ar_valid) begin
      // set the right read channel output depending on the address decoding
      if (dec_r_valid) begin
        // when decode not valid, send the default slaveerror
        // read the right register when the transfer happens and decode is valid
        unique case (reg_e'(r_reg_idx))
          MBOXW: r_chan = '{data: data_t'( 32'hFEEDC0DE ), resp: axi_pkg::RESP_OKAY};
          MBOXR: begin
            if (!mbox_r_empty_i) begin
              r_chan       = '{data: data_t'( mbox_r_data_i ), resp: axi_pkg::RESP_OKAY};
              mbox_r_pop_o = 1'b1;
            end else begin
              // read mailbox is empty, set the read error Flip flop and respond with error
              r_chan      = '{data: data_t'( 32'hFEEDDEAD ), resp: axi_pkg::RESP_SLVERR};
              error_d[0]  = 1'b1;
              irqs_d[2]   = 1'b1;
              update_regs = 1'b1;
            end
          end
          STATUS: r_chan = '{data: data_t'( status_q ), resp: axi_pkg::RESP_OKAY};
          ERROR: begin // clear the error register
            r_chan      = '{data: data_t'( error_q  ), resp: axi_pkg::RESP_OKAY};
            error_d     = '0;
            update_regs = 1'b1;
          end
          WIRQT: r_chan = '{data: data_t'( wirqt_q  ), resp: axi_pkg::RESP_OKAY};
          RIRQT: r_chan = '{data: data_t'( rirqt_q  ), resp: axi_pkg::RESP_OKAY};
          IRQS:  r_chan = '{data: data_t'( irqs_q   ), resp: axi_pkg::RESP_OKAY};
          IRQEN: r_chan = '{data: data_t'( irqen_q  ), resp: axi_pkg::RESP_OKAY};
          IRQP:  r_chan = '{data: data_t'( irqp_q   ), resp: axi_pkg::RESP_OKAY};
          CTRL:  r_chan = '{data: data_t'( ctrl_q   ), resp: axi_pkg::RESP_OKAY};
          default: /*do nothing*/;
        endcase
      end
      r_valid = 1'b1;
      if (r_ready) begin
        slv_resp_o.ar_ready = 1'b1;
      end
    end // read register

    // -------------------------------------------
    // Write registers
    // -------------------------------------------
    // Wait for control and write data to be valid.
    if (slv_req_i.aw_valid && slv_req_i.w_valid) begin
      // Can do the handshake here as the b response goes into a spill register with latency one.
      // Without the B spill register, the B channel would violate the AXI stable requirement.
      b_valid = 1'b1;
      if (b_ready) begin
        // write to the register if required
        if (dec_w_valid) begin
          unique case (reg_e'(w_reg_idx))
            MBOXW:  begin
              if (!mbox_w_full_i) begin
                mbox_w_push_o = 1'b1;
                b_chan        = '{resp: axi_pkg::RESP_OKAY};
              end else begin
                // response with default error and set the error FF
                error_d[1]  = 1'b1;
                irqs_d[2]   = 1'b1;
                update_regs = 1'b1;
              end
            end
            // MBOXR:  read only
            // STATUS: read only
            // ERROR:  read only
            WIRQT:  begin
              for (int unsigned i = 0; i < AxiDataWidth/8; i++) begin
                wirqt_d[i*8+:8] = slv_req_i.w.strb[i] ? slv_req_i.w.data[i*8+:8] : 8'b0000_0000;
              end
              if (wirqt_d >= data_t'(MailboxDepth)) begin
                // the `-1` is to have the interrupt fireing when the FIFO is comletely full
                wirqt_d = data_t'(MailboxDepth) - data_t'(32'd1); // Threshold to maximal value
              end
              update_regs = 1'b1;
              b_chan      = '{resp: axi_pkg::RESP_OKAY};
            end
            RIRQT:  begin
              for (int unsigned i = 0; i < AxiDataWidth/8; i++) begin
                rirqt_d[i*8+:8] = slv_req_i.w.strb[i] ? slv_req_i.w.data[i*8+:8] : 8'b0000_0000;
              end
              if (rirqt_d >= data_t'(MailboxDepth)) begin
              // Threshold to maximal value, minus two to prevent overflow in usage
                rirqt_d = data_t'(MailboxDepth) - data_t'(32'd1);
              end
              update_regs = 1'b1;
              b_chan      = '{resp: axi_pkg::RESP_OKAY};
            end
            IRQS:   begin
              // Acknowledge and clear the register by asserting the respective one
              if (slv_req_i.w.strb[0]) begin
                // *_d signal is set in the beginning of this process, prevent accidental
                // overwrite of not acknowledged irq
                irqs_d[2]   = slv_req_i.w.data[2] ? 1'b0 : irqs_d[2]; // Error irq status
                irqs_d[1]   = slv_req_i.w.data[1] ? 1'b0 : irqs_d[1]; // Read  irq status
                irqs_d[0]   = slv_req_i.w.data[0] ? 1'b0 : irqs_d[0]; // Write irq status
                clear_irq_o = 1'b1;
                update_regs = 1'b1;
              end
              b_chan = '{resp: axi_pkg::RESP_OKAY};
            end
            IRQEN:  begin
              if (slv_req_i.w.strb[0]) begin
                irqen_d[2:0]  = slv_req_i.w.data[2:0]; // set the irq enable bits
                update_regs = 1'b1;
              end
              b_chan = '{resp: axi_pkg::RESP_OKAY};
            end
            // IRQP: read only
            CTRL:   begin
              if (slv_req_i.w.strb[0]) begin
                mbox_r_flush_o = slv_req_i.w.data[1]; // Flush read  FIFO
                mbox_w_flush_o = slv_req_i.w.data[0]; // Flush write FIFO
              end
              b_chan = '{resp: axi_pkg::RESP_OKAY};
            end
            default : /* use default b_chan */;
          endcase
        end
        slv_resp_o.aw_ready = 1'b1;
        slv_resp_o.w_ready  = 1'b1;
      end // if (b_ready): Does not violate AXI spec, because the ready comes from an internal
          // spill register and does not propagate the ready from the b channel.
    end // write register
  end

  // address decoder and response FIFOs for the LITE channel, the port can take a new transaction if
  // these FIFOs are not full, not fall through to prevent combinational paths to the return path
  addr_decode #(
    .NoIndices( NoRegs ),
    .NoRules  ( NoRegs ),
    .addr_t   ( addr_t ),
    .rule_t   ( rule_t )
  ) i_waddr_decode (
    .addr_i           ( slv_req_i.aw.addr ),
    .addr_map_i       ( addr_map          ),
    .idx_o            ( w_reg_idx         ),
    .dec_valid_o      ( dec_w_valid       ),
    .dec_error_o      ( /*not used*/      ),
    .en_default_idx_i ( 1'b0              ),
    .default_idx_i    ( '0                )
  );
  spill_register #(
    .T ( b_chan_lite_t )
  ) i_b_chan_outp (
    .clk_i,
    .rst_ni,
    .valid_i ( b_valid            ),
    .ready_o ( b_ready            ),
    .data_i  ( b_chan             ),
    .valid_o ( slv_resp_o.b_valid ),
    .ready_i ( slv_req_i.b_ready  ),
    .data_o  ( slv_resp_o.b       )
  );
  addr_decode #(
    .NoIndices( NoRegs ),
    .NoRules  ( NoRegs ),
    .addr_t   ( addr_t ),
    .rule_t   ( rule_t )
  ) i_raddr_decode (
    .addr_i           ( slv_req_i.ar.addr ),
    .addr_map_i       ( addr_map          ),
    .idx_o            ( r_reg_idx         ),
    .dec_valid_o      ( dec_r_valid       ),
    .dec_error_o      ( /*not used*/      ),
    .en_default_idx_i ( 1'b0              ),
    .default_idx_i    ( '0                )
  );
  spill_register #(
    .T ( r_chan_lite_t )
  ) i_r_chan_outp (
    .clk_i,
    .rst_ni,
    .valid_i ( r_valid            ),
    .ready_o ( r_ready            ),
    .data_i  ( r_chan             ),
    .valid_o ( slv_resp_o.r_valid ),
    .ready_i ( slv_req_i.r_ready  ),
    .data_o  ( slv_resp_o.r       )
  );
  // pragma translate_off
  `ifndef VERILATOR
  initial begin : proc_check_params
    assert (AxiAddrWidth == $bits(slv_req_i.aw.addr)) else $fatal(1, "AW AxiAddrWidth mismatch");
    assert (AxiDataWidth == $bits(slv_req_i.w.data))  else $fatal(1, " W AxiDataWidth mismatch");
    assert (AxiAddrWidth == $bits(slv_req_i.ar.addr)) else $fatal(1, "AR AxiAddrWidth mismatch");
    assert (AxiDataWidth == $bits(slv_resp_o.r.data)) else $fatal(1, " R AxiDataWidth mismatch");
  end
  `endif
  // pragma translate_on
endmodule

`include "axi/assign.svh"

module axi_lite_mailbox_intf #(
  parameter int unsigned MAILBOX_DEPTH  = 32'd0,
  parameter bit unsigned IRQ_EDGE_TRIG  = 1'b0,
  parameter bit unsigned IRQ_ACT_HIGH   = 1'b1,
  parameter int unsigned AXI_ADDR_WIDTH = 32'd0,
  parameter int unsigned AXI_DATA_WIDTH = 32'd0,
  // DEPENDENT PARAMETERS, DO NOT OVERRIDE!
  parameter type addr_t               = logic [AXI_ADDR_WIDTH-1:0]
) (
  input  logic         clk_i,      // Clock
  input  logic         rst_ni,     // Asynchronous reset active low
  input  logic         test_i,     // Testmode enable
  AXI_LITE.Slave       slv [1:0],  // slave ports [1:0]
  output logic   [1:0] irq_o,      // interrupt output for each port
  input  addr_t  [1:0] base_addr_i // base address for each port
);
  typedef logic [AXI_DATA_WIDTH-1:0]   data_t;
  typedef logic [AXI_DATA_WIDTH/8-1:0] strb_t;
  `AXI_LITE_TYPEDEF_AW_CHAN_T(aw_chan_lite_t, addr_t)
  `AXI_LITE_TYPEDEF_W_CHAN_T(w_chan_lite_t, data_t, strb_t)
  `AXI_LITE_TYPEDEF_B_CHAN_T(b_chan_lite_t)
  `AXI_LITE_TYPEDEF_AR_CHAN_T(ar_chan_lite_t, addr_t)
  `AXI_LITE_TYPEDEF_R_CHAN_T(r_chan_lite_t, data_t)
  `AXI_LITE_TYPEDEF_REQ_T(req_lite_t, aw_chan_lite_t, w_chan_lite_t, ar_chan_lite_t)
  `AXI_LITE_TYPEDEF_RESP_T(resp_lite_t, b_chan_lite_t, r_chan_lite_t)

  req_lite_t  [1:0] slv_reqs;
  resp_lite_t [1:0] slv_resps;

  for (genvar i = 0; i < 2; i++) begin : gen_port_assign
    `AXI_LITE_ASSIGN_TO_REQ(slv_reqs[i], slv[i])
    `AXI_LITE_ASSIGN_FROM_RESP(slv[i], slv_resps[i])
  end

  axi_lite_mailbox #(
    .MailboxDepth ( MAILBOX_DEPTH  ),
    .IrqEdgeTrig  ( IRQ_EDGE_TRIG  ),
    .IrqActHigh   ( IRQ_ACT_HIGH   ),
    .AxiAddrWidth ( AXI_ADDR_WIDTH ),
    .AxiDataWidth ( AXI_DATA_WIDTH ),
    .req_lite_t   ( req_lite_t     ),
    .resp_lite_t  ( resp_lite_t    )
  ) i_axi_lite_mailbox (
    .clk_i,      // Clock
    .rst_ni,     // Asynchronous reset active low
    .test_i,     // Testmode enable
    // slave ports [1:0]
    .slv_reqs_i  ( slv_reqs  ),
    .slv_resps_o ( slv_resps ),
    .irq_o,      // interrupt output for each port
    .base_addr_i // base address for each port
  );

  // pragma translate_off
  `ifndef VERILATOR
  initial begin
    assert (slv[0].AXI_ADDR_WIDTH == AXI_ADDR_WIDTH)
        else $fatal(1, "LITE Interface [0] AXI_ADDR_WIDTH missmatch!");
    assert (slv[1].AXI_ADDR_WIDTH == AXI_ADDR_WIDTH)
        else $fatal(1, "LITE Interface [1] AXI_ADDR_WIDTH missmatch!");
    assert (slv[0].AXI_DATA_WIDTH == AXI_DATA_WIDTH)
        else $fatal(1, "LITE Interface [0] AXI_DATA_WIDTH missmatch!");
    assert (slv[1].AXI_DATA_WIDTH == AXI_DATA_WIDTH)
        else $fatal(1, "LITE Interface [1] AXI_DATA_WIDTH missmatch!");
  end
  `endif
  // pragma translate_on
endmodule

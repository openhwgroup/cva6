module macro_decoder_issue_ack_test;

  localparam config_pkg::cva6_cfg_t CVA6Cfg = build_config_pkg::build_config(
      cva6_config_pkg::cva6_cfg
  );

  // macro_decoder FSM encoding.
  localparam logic [2:0] ST_IDLE = 3'd0;
  localparam logic [2:0] ST_PUSH_ADDI = 3'd2;
  localparam logic [2:0] ST_POPRETZ_1 = 3'd3;
  localparam logic [2:0] ST_MOVE = 3'd4;
  localparam logic [2:0] ST_PUSH_POP_INSTR_2 = 3'd5;

  logic        clk_i;
  logic        rst_ni;
  logic [31:0] instr_i;
  logic        is_macro_instr_i;
  logic        illegal_instr_i;
  logic        is_compressed_i;
  logic        issue_ack_i;

  logic [31:0] instr_o;
  logic        illegal_instr_o;
  logic        is_compressed_o;
  logic        fetch_stall_o;
  logic        is_last_macro_instr_o;
  logic        is_double_rd_macro_instr_o;

  always #5 clk_i = ~clk_i;

  macro_decoder #(
      .CVA6Cfg(CVA6Cfg)
  ) dut (
      .instr_i,
      .clk_i,
      .rst_ni,
      .is_macro_instr_i,
      .illegal_instr_i,
      .is_compressed_i,
      .issue_ack_i,
      .instr_o,
      .illegal_instr_o,
      .is_compressed_o,
      .fetch_stall_o,
      .is_last_macro_instr_o,
      .is_double_rd_macro_instr_o
  );

  task automatic reset_dut;
    begin
      is_macro_instr_i = 1'b0;
      illegal_instr_i  = 1'b0;
      is_compressed_i  = 1'b1;
      issue_ack_i      = 1'b0;
      instr_i          = '0;

      rst_ni           = 1'b0;
      repeat (2) @(posedge clk_i);

      // Deassert reset away from the active clock edge.
      @(negedge clk_i);
      rst_ni = 1'b1;
      #1;

      assert (dut.state_q == ST_IDLE)
      else $fatal(1, "decoder did not reset to IDLE");
    end
  endtask

  task automatic check_stalled_first_uop(
      input logic [15:0] encoding, input logic [2:0] expected_next_state, input string test_name);
    logic [31:0] first_uop;

    begin
      reset_dut();

      // Drive the macro between clock edges and explicitly hold the
      // issue acknowledgement low.
      instr_i          = {16'h0000, encoding};
      is_macro_instr_i = 1'b1;
      issue_ack_i      = 1'b0;

      // Allow combinational decoder outputs to settle before sampling.
      #1;

      assert (!illegal_instr_o)
      else $fatal(1, "%s decoded as illegal", test_name);

      assert (dut.state_q == ST_IDLE)
      else $fatal(1, "%s did not start in IDLE", test_name);

      assert (fetch_stall_o)
      else $fatal(1, "%s did not stall instruction fetch", test_name);

      first_uop = instr_o;

      // Cross exactly one active clock edge with issue_ack_i low.
      @(posedge clk_i);
      @(negedge clk_i);
      #1;

      assert (dut.state_q == ST_IDLE)
      else $fatal(1, "%s left IDLE without issue_ack_i (state=%0d)", test_name, dut.state_q);

      assert (instr_o === first_uop)
      else $fatal(1, "%s changed the first micro-op while issue_ack_i was low", test_name);

      // Acknowledge the first micro-op well before the next positive edge.
      issue_ack_i = 1'b1;
      #1;

      // Cross exactly one active edge and sample before another active edge.
      @(posedge clk_i);
      @(negedge clk_i);
      #1;

      assert (dut.state_q == expected_next_state)
      else
        $fatal(
            1,
            "%s did not advance after issue_ack_i (state=%0d expected=%0d)",
            test_name,
            dut.state_q,
            expected_next_state
        );

      $display("PASS: %s", test_name);
    end
  endtask

  initial begin
    clk_i            = 1'b0;
    rst_ni           = 1'b0;
    instr_i          = '0;
    is_macro_instr_i = 1'b0;
    illegal_instr_i  = 1'b0;
    is_compressed_i  = 1'b1;
    issue_ack_i      = 1'b0;

    // Encodings generated with GNU binutils Zcmp support.
    //
    // Each of these instructions has a special transition directly
    // from IDLE which must occur only after issue_ack_i is asserted.

    check_stalled_first_uop(16'hacaa, ST_MOVE, "cm.mvsa01");

    check_stalled_first_uop(16'hacea, ST_MOVE, "cm.mva01s");

    check_stalled_first_uop(16'hb842, ST_PUSH_ADDI, "cm.push {ra}, -16");

    check_stalled_first_uop(16'hba42, ST_PUSH_ADDI, "cm.pop {ra}, 16");

    check_stalled_first_uop(16'hbe42, ST_PUSH_ADDI, "cm.popret {ra}, 16");

    check_stalled_first_uop(16'hbc42, ST_POPRETZ_1, "cm.popretz {ra}, 16");

    check_stalled_first_uop(16'hb8f2, ST_PUSH_POP_INSTR_2, "cm.push {ra, s0-s11}, -64");

    check_stalled_first_uop(16'hbaf2, ST_PUSH_POP_INSTR_2, "cm.pop {ra, s0-s11}, 64");

    $display("PASS: macro decoder holds every affected first micro-op until issue_ack_i");

    $finish;
  end

endmodule

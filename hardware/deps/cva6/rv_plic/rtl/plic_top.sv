module plic_top #(
  parameter int N_SOURCE    = 30,
  parameter int N_TARGET    = 2,
  parameter int MAX_PRIO    = 7,
  parameter int SRCW        = $clog2(N_SOURCE+1)
) (
  input  logic clk_i,    // Clock
  input  logic rst_ni,  // Asynchronous reset active low
  // Bus Interface
  input  reg_intf::reg_intf_req_a32_d32 req_i,
  output reg_intf::reg_intf_resp_d32    resp_o,
  input logic [N_SOURCE-1:0] le_i, // 0:level 1:edge
  // Interrupt Sources
  input  logic [N_SOURCE-1:0] irq_sources_i,
  // Interrupt notification to targets
  output logic [N_TARGET-1:0] eip_targets_o
);
  localparam PRIOW = $clog2(MAX_PRIO+1);

  logic [N_SOURCE-1:0] ip;

  logic [N_TARGET-1:0][PRIOW-1:0]    threshold_q;

  logic [N_TARGET-1:0]               claim_re; //Target read indicator
  logic [N_TARGET-1:0][SRCW-1:0]     claim_id;
  logic [N_SOURCE-1:0]               claim; //Converted from claim_re/claim_id

  logic [N_TARGET-1:0]               complete_we; //Target write indicator
  logic [N_TARGET-1:0][SRCW-1:0]     complete_id;
  logic [N_SOURCE-1:0]               complete; //Converted from complete_re/complete_id

  logic [N_SOURCE-1:0][PRIOW-1:0]    prio_q;
  logic [N_TARGET-1:0][N_SOURCE-1:0] ie_q;

  always_comb begin
    claim = '0;
    complete = '0;
    for (int i = 0 ; i < N_TARGET ; i++) begin
      if (claim_re[i] && claim_id[i] != 0) claim[claim_id[i]-1] = 1'b1;
      if (complete_we[i] && complete_id[i] != 0) complete[complete_id[i]-1] = 1'b1;
    end
  end

  // Gateways
  rv_plic_gateway #(
    .N_SOURCE (N_SOURCE)
  ) i_rv_plic_gateway (
    .clk_i,
    .rst_ni,
    .src(irq_sources_i),
    .le(le_i),
    .claim(claim),
    .complete(complete),
    .ip(ip)
  );

  // Target interrupt notification
  for (genvar i = 0 ; i < N_TARGET; i++) begin : gen_target
    rv_plic_target #(
      .N_SOURCE  ( N_SOURCE ),
      .MAX_PRIO  ( MAX_PRIO ),
      .ALGORITHM ( "SEQUENTIAL" )
    ) i_target (
      .clk_i,
      .rst_ni,
      .ip(ip),
      .ie(ie_q[i]),
      .prio(prio_q),
      .threshold(threshold_q[i]),
      .irq(eip_targets_o[i]),
      .irq_id(claim_id[i])
    );
  end

  logic [N_TARGET-1:0] threshold_we_o;
  logic [N_TARGET-1:0][PRIOW-1:0] threshold_o;

  logic [N_SOURCE:0][PRIOW-1:0] prio_i, prio_o;
  logic [N_SOURCE:0] prio_we_o;

  // TODO(zarubaf): This needs more graceful handling
  // it will break if the number of sources is larger than 32
  logic [N_TARGET-1:0][N_SOURCE:0] ie_i, ie_o;
  logic [N_TARGET-1:0] ie_we_o;

  plic_regs i_plic_regs (
    .prio_i(prio_i),
    .prio_o(prio_o),
    .prio_we_o(prio_we_o),
    .prio_re_o(), // don't care
    // source zero is always zero
    .ip_i({ip, 1'b0}),
    .ip_re_o(), // don't care
    .ie_i(ie_i),
    .ie_o(ie_o),
    .ie_we_o(ie_we_o),
    .ie_re_o(), // don't care
    .threshold_i(threshold_q),
    .threshold_o(threshold_o),
    .threshold_we_o(threshold_we_o),
    .threshold_re_o(), // don't care
    .cc_i(claim_id),
    .cc_o(complete_id),
    .cc_we_o(complete_we),
    .cc_re_o(claim_re),
    .req_i,
    .resp_o
  );

  assign prio_i[0] = '0;

  for (genvar i = 0; i < N_TARGET; i++) begin
    assign ie_i[i] = {ie_q[i][N_SOURCE-1:0], 1'b0};
  end

  for (genvar i = 1; i < N_SOURCE + 1; i++) begin
    assign prio_i[i] = prio_q[i - 1];
  end

  // registers
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (~rst_ni) begin
      prio_q <= '0;
      ie_q <= '0;
      threshold_q <= '0;
    end else begin
      // source zero is 0
      for (int i = 0; i < N_SOURCE; i++) begin
        prio_q[i] <= prio_we_o[i + 1] ? prio_o[i + 1] : prio_q[i];
      end
      for (int i = 0; i < N_TARGET; i++) begin
        threshold_q[i] <= threshold_we_o[i] ? threshold_o[i] : threshold_q[i];
        ie_q[i] <= ie_we_o[i] ? ie_o[i][N_SOURCE:1] : ie_q[i];
      end

    end
  end
endmodule

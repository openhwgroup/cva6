`include "rvfi_types.svh"

module mstatus_wpri_test;
  import ariane_pkg::*;

  localparam config_pkg::cva6_cfg_t CVA6Cfg = build_config_pkg::build_config(
    cva6_config_pkg::cva6_cfg
  );

  typedef struct packed {
    logic [CVA6Cfg.XLEN-1:0] cause;
    logic [CVA6Cfg.XLEN-1:0] tval;
    logic [CVA6Cfg.GPLEN-1:0] tval2;
    logic [31:0] tinst;
    logic gva;
    logic valid;
    logic timing;
  } exception_t;

  typedef struct packed {
    logic [CVA6Cfg.VLEN-1:0] predict_address;
  } branchpredict_t;

  typedef struct packed {
    logic [CVA6Cfg.VLEN-1:0] pc;
    fu_t fu;
    branchpredict_t bp;
    logic is_compressed;
  } scoreboard_entry_t;

  typedef struct packed {
    logic [CVA6Cfg.XLEN-7:0] base;
    logic [5:0] mode;
  } jvt_t;

  typedef struct packed {
    logic [CVA6Cfg.XLEN-1:0] mie;
    logic [CVA6Cfg.XLEN-1:0] mip;
    logic [CVA6Cfg.XLEN-1:0] mideleg;
    logic [CVA6Cfg.XLEN-1:0] hideleg;
    logic sie;
    logic global_enable;
  } irq_ctrl_t;

  typedef `RVFI_PROBES_CSR_T(CVA6Cfg) rvfi_probes_csr_t;

  logic clk_i;
  logic rst_ni;
  scoreboard_entry_t commit_instr_i;
  logic [CVA6Cfg.NrCommitPorts-1:0] commit_ack_i;
  exception_t ex_i;
  fu_op csr_op_i;
  logic [11:0] csr_addr_i;
  logic [CVA6Cfg.XLEN-1:0] csr_wdata_i;
  logic [CVA6Cfg.XLEN-1:0] csr_rdata_o;
  exception_t csr_exception_o;

  always #1 clk_i = ~clk_i;

  csr_regfile #(
    .CVA6Cfg(CVA6Cfg),
    .exception_t(exception_t),
    .jvt_t(jvt_t),
    .irq_ctrl_t(irq_ctrl_t),
    .scoreboard_entry_t(scoreboard_entry_t),
    .rvfi_probes_csr_t(rvfi_probes_csr_t)
  ) dut (
    .clk_i,
    .rst_ni,
    .commit_instr_i,
    .commit_ack_i,
    .ex_i,
    .csr_op_i,
    .csr_addr_i,
    .csr_wdata_i,
    .csr_rdata_o,
    .csr_exception_o
  );

  initial begin
    clk_i = 1'b0;
    rst_ni = 1'b0;
    commit_instr_i = '0;
    commit_ack_i = '0;
    ex_i = '0;
    csr_op_i = CSR_READ;
    csr_addr_i = riscv::CSR_MSTATUS;
    csr_wdata_i = '0;

    #3;
    rst_ni = 1'b1;
    @(negedge clk_i);

    csr_op_i = CSR_WRITE;
    csr_wdata_i = (64'(1) << 62) | (64'(1) << 50) | (64'(1) << 38);
    @(negedge clk_i);

    csr_op_i = CSR_READ;
    #1;

    assert (!csr_exception_o.valid) else $fatal(1, "mstatus access failed");
    assert ((csr_rdata_o & csr_wdata_i) == '0) else $fatal(1, "reserved mstatus bits are writable");

    $display("PASS: reserved mstatus bits stay zero");
    $finish;
  end
endmodule

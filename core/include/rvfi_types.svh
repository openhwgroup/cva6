`ifndef RVFI_TYPES_SVH
`define RVFI_TYPES_SVH

// RVFI
`define RVFI_INSTR_T(Cfg) struct packed { \
  logic [config_pkg::NRET-1:0]                  valid; \
  logic [config_pkg::NRET*64-1:0]               order; \
  logic [config_pkg::NRET*config_pkg::ILEN-1:0] insn; \
  logic [config_pkg::NRET-1:0]                  trap; \
  logic [config_pkg::NRET*riscv::XLEN-1:0]      cause; \
  logic [config_pkg::NRET-1:0]                  halt; \
  logic [config_pkg::NRET-1:0]                  intr; \
  logic [config_pkg::NRET*2-1:0]                mode; \
  logic [config_pkg::NRET*2-1:0]                ixl; \
  logic [config_pkg::NRET*5-1:0]                rs1_addr; \
  logic [config_pkg::NRET*5-1:0]                rs2_addr; \
  logic [config_pkg::NRET*riscv::XLEN-1:0]      rs1_rdata; \
  logic [config_pkg::NRET*riscv::XLEN-1:0]      rs2_rdata; \
  logic [config_pkg::NRET*5-1:0]                rd_addr; \
  logic [config_pkg::NRET*riscv::XLEN-1:0]      rd_wdata; \
  logic [config_pkg::NRET*riscv::XLEN-1:0]      pc_rdata; \
  logic [config_pkg::NRET*riscv::XLEN-1:0]      pc_wdata; \
  logic [config_pkg::NRET*riscv::VLEN-1:0]      mem_addr; \
  logic [config_pkg::NRET*riscv::PLEN-1:0]      mem_paddr; \
  logic [config_pkg::NRET*(riscv::XLEN/8)-1:0]  mem_rmask; \
  logic [config_pkg::NRET*(riscv::XLEN/8)-1:0]  mem_wmask; \
  logic [config_pkg::NRET*riscv::XLEN-1:0]      mem_rdata; \
  logic [config_pkg::NRET*riscv::XLEN-1:0]      mem_wdata; \
}

`define RVFI_CSR_ELMT_T(Cfg) struct packed { \
  riscv::xlen_t rdata; \
  riscv::xlen_t rmask; \
  riscv::xlen_t wdata; \
  riscv::xlen_t wmask; \
}

`define RVFI_CSR_T(Cfg, rvfi_csr_elmt_t) struct packed { \
  rvfi_csr_elmt_t fflags; \
  rvfi_csr_elmt_t frm; \
  rvfi_csr_elmt_t fcsr; \
  rvfi_csr_elmt_t ftran; \
  rvfi_csr_elmt_t dcsr; \
  rvfi_csr_elmt_t dpc; \
  rvfi_csr_elmt_t dscratch0; \
  rvfi_csr_elmt_t dscratch1; \
  rvfi_csr_elmt_t sstatus; \
  rvfi_csr_elmt_t sie; \
  rvfi_csr_elmt_t sip; \
  rvfi_csr_elmt_t stvec; \
  rvfi_csr_elmt_t scounteren; \
  rvfi_csr_elmt_t sscratch; \
  rvfi_csr_elmt_t sepc; \
  rvfi_csr_elmt_t scause; \
  rvfi_csr_elmt_t stval; \
  rvfi_csr_elmt_t satp; \
  rvfi_csr_elmt_t mstatus; \
  rvfi_csr_elmt_t mstatush; \
  rvfi_csr_elmt_t misa; \
  rvfi_csr_elmt_t medeleg; \
  rvfi_csr_elmt_t mideleg; \
  rvfi_csr_elmt_t mie; \
  rvfi_csr_elmt_t mtvec; \
  rvfi_csr_elmt_t mcounteren; \
  rvfi_csr_elmt_t mscratch; \
  rvfi_csr_elmt_t mepc; \
  rvfi_csr_elmt_t mcause; \
  rvfi_csr_elmt_t mtval; \
  rvfi_csr_elmt_t mip; \
  rvfi_csr_elmt_t menvcfg; \
  rvfi_csr_elmt_t menvcfgh; \
  rvfi_csr_elmt_t mvendorid; \
  rvfi_csr_elmt_t marchid; \
  rvfi_csr_elmt_t mhartid; \
  rvfi_csr_elmt_t mcountinhibit; \
  rvfi_csr_elmt_t mcycle; \
  rvfi_csr_elmt_t mcycleh; \
  rvfi_csr_elmt_t minstret; \
  rvfi_csr_elmt_t minstreth; \
  rvfi_csr_elmt_t cycle; \
  rvfi_csr_elmt_t cycleh; \
  rvfi_csr_elmt_t instret; \
  rvfi_csr_elmt_t instreth; \
  rvfi_csr_elmt_t dcache; \
  rvfi_csr_elmt_t icache; \
  rvfi_csr_elmt_t acc_cons; \
  rvfi_csr_elmt_t pmpcfg0; \
  rvfi_csr_elmt_t pmpcfg1; \
  rvfi_csr_elmt_t pmpcfg2; \
  rvfi_csr_elmt_t pmpcfg3; \
  rvfi_csr_elmt_t [15:0] pmpaddr; \
}

// RVFI PROBES
`define RVFI_PROBES_INSTR_T(Cfg) struct packed { \
  logic [ariane_pkg::TRANS_ID_BITS-1:0] issue_pointer; \
  logic [cva6_config_pkg::CVA6ConfigNrCommitPorts-1:0][ariane_pkg::TRANS_ID_BITS-1:0] commit_pointer; \
  logic flush_unissued_instr; \
  logic decoded_instr_valid; \
  logic decoded_instr_ack; \
  logic flush; \
  logic issue_instr_ack; \
  logic fetch_entry_valid; \
  logic [31:0] instruction; \
  logic is_compressed; \
  riscv::xlen_t rs1_forwarding; \
  riscv::xlen_t rs2_forwarding; \
  logic [cva6_config_pkg::CVA6ConfigNrCommitPorts-1:0][riscv::VLEN-1:0] commit_instr_pc; \
  ariane_pkg::fu_op [cva6_config_pkg::CVA6ConfigNrCommitPorts-1:0][ariane_pkg::TRANS_ID_BITS-1:0] commit_instr_op; \
  logic [cva6_config_pkg::CVA6ConfigNrCommitPorts-1:0][ariane_pkg::REG_ADDR_SIZE-1:0] commit_instr_rs1; \
  logic [cva6_config_pkg::CVA6ConfigNrCommitPorts-1:0][ariane_pkg::REG_ADDR_SIZE-1:0] commit_instr_rs2; \
  logic [cva6_config_pkg::CVA6ConfigNrCommitPorts-1:0][ariane_pkg::REG_ADDR_SIZE-1:0] commit_instr_rd; \
  riscv::xlen_t [cva6_config_pkg::CVA6ConfigNrCommitPorts-1:0] commit_instr_result; \
  logic [cva6_config_pkg::CVA6ConfigNrCommitPorts-1:0][riscv::VLEN-1:0] commit_instr_valid; \
  riscv::xlen_t ex_commit_cause; \
  logic ex_commit_valid; \
  riscv::priv_lvl_t priv_lvl; \
  logic [riscv::VLEN-1:0] lsu_ctrl_vaddr; \
  ariane_pkg::fu_t lsu_ctrl_fu; \
  logic [(riscv::XLEN/8)-1:0] lsu_ctrl_be; \
  logic [ariane_pkg::TRANS_ID_BITS-1:0] lsu_ctrl_trans_id; \
  logic [((cva6_config_pkg::CVA6ConfigCvxifEn || cva6_config_pkg::CVA6ConfigVExtEn) ? 5 : 4)-1:0][riscv::XLEN-1:0] wbdata; \
  logic [cva6_config_pkg::CVA6ConfigNrCommitPorts-1:0] commit_ack; \
  logic [riscv::PLEN-1:0] mem_paddr; \
  logic debug_mode; \
  logic [cva6_config_pkg::CVA6ConfigNrCommitPorts-1:0][riscv::XLEN-1:0] wdata; \
}

`define RVFI_PROBES_CSR_T(Cfg) struct packed { \
  riscv::fcsr_t fcsr_q; \
  riscv::dcsr_t dcsr_q; \
  riscv::xlen_t dpc_q; \
  riscv::xlen_t dscratch0_q; \
  riscv::xlen_t dscratch1_q; \
  riscv::xlen_t mie_q; \
  riscv::xlen_t mip_q; \
  riscv::xlen_t stvec_q; \
  riscv::xlen_t scounteren_q; \
  riscv::xlen_t sscratch_q; \
  riscv::xlen_t sepc_q; \
  riscv::xlen_t scause_q; \
  riscv::xlen_t stval_q; \
  riscv::xlen_t satp_q; \
  riscv::xlen_t mstatus_extended; \
  riscv::xlen_t medeleg_q; \
  riscv::xlen_t mideleg_q; \
  riscv::xlen_t mtvec_q; \
  riscv::xlen_t mcounteren_q; \
  riscv::xlen_t mscratch_q; \
  riscv::xlen_t mepc_q; \
  riscv::xlen_t mcause_q; \
  riscv::xlen_t mtval_q; \
  logic fiom_q; \
  logic [ariane_pkg::MHPMCounterNum+3-1:0] mcountinhibit_q; \
  logic [63:0] cycle_q; \
  logic [63:0] instret_q; \
  riscv::xlen_t dcache_q; \
  riscv::xlen_t icache_q; \
  riscv::xlen_t acc_cons_q; \
  riscv::pmpcfg_t [15:0] pmpcfg_q; \
  logic [15:0][riscv::PLEN-3:0] pmpaddr_q; \
}

`endif // RVFI_TYPES_SVH

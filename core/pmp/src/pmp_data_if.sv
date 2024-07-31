//-----------------------------------------------------------------------------
// Copyright 2024 Robert Bosch GmbH
//
// SPDX-License-Identifier: SHL-0.51
//
// Original Author: Coralie Allioux - Robert Bosch France SAS
//-----------------------------------------------------------------------------

module pmp_data_if
  import ariane_pkg::*;
#(
    parameter config_pkg::cva6_cfg_t CVA6Cfg       = config_pkg::cva6_cfg_empty,
    parameter type                   icache_areq_t = logic,
    parameter type                   icache_arsp_t = logic,
    parameter type                   exception_t   = logic
) (
    input logic clk_i,
    input logic rst_ni,
    input logic enable_translation_i,
    input logic enable_g_translation_i,
    input logic en_ld_st_translation_i,  // enable virtual memory translation for load/stores
    input logic en_ld_st_g_translation_i,  // enable G-Stage translation for load/stores
    // IF interface
    input icache_arsp_t icache_areq_i,
    output icache_areq_t icache_areq_o,
    // LSU interface
    // this is a more minimalistic interface because the actual addressing logic is handled
    // in the LSU as we distinguish load and stores, what we do here is simple address translation
    input exception_t misaligned_ex_i,
    input logic lsu_req_i,  // request address translation
    input logic [CVA6Cfg.VLEN-1:0] lsu_vaddr_i,  // virtual address in
    input logic [31:0] lsu_tinst_i,  // transformed instruction in
    input logic lsu_is_store_i,  // the translation is requested by a store
    // Cycle 1
    output logic lsu_valid_o,  // translation is valid
    output logic [CVA6Cfg.PLEN-1:0] lsu_paddr_o,  // translated address
    output exception_t lsu_exception_o,  // address translation threw an exception
    // General control signals
    input riscv::priv_lvl_t priv_lvl_i,
    input logic v_i,
    input riscv::priv_lvl_t ld_st_priv_lvl_i,
    input logic ld_st_v_i,
    // PMP
    input riscv::pmpcfg_t [CVA6Cfg.NrPMPEntries:0] pmpcfg_i,
    input logic [CVA6Cfg.NrPMPEntries:0][CVA6Cfg.PLEN-3:0] pmpaddr_i,
    output logic data_allow_o,
    output logic instr_allow_o,
    output logic match_any_execute_region_o,
    output exception_t misaligned_ex_o
);

  exception_t misaligned_ex_n, misaligned_ex_q;
  logic lsu_req_n, lsu_req_q;
  logic lsu_is_store_n, lsu_is_store_q;

  // Wires to PMP checks
  riscv::pmp_access_t pmp_access_type;

  logic [CVA6Cfg.PLEN-1:0] mmu_vaddr_plen, fetch_vaddr_plen;
  logic [CVA6Cfg.VLEN-1:0] lsu_vaddr_q;
  logic [31:0] lsu_tinst_q;

  always_comb begin : vaddr_plen
    if (CVA6Cfg.VLEN >= CVA6Cfg.PLEN) begin
      mmu_vaddr_plen   = lsu_vaddr_q[CVA6Cfg.PLEN-1:0];
      fetch_vaddr_plen = icache_areq_i.fetch_vaddr[CVA6Cfg.PLEN-1:0];
    end else begin
      mmu_vaddr_plen   = CVA6Cfg.PLEN'(lsu_vaddr_q);
      fetch_vaddr_plen = CVA6Cfg.PLEN'(icache_areq_i.fetch_vaddr);
    end
  end

  assign misaligned_ex_o = misaligned_ex_q;

  //-----------------------
  // Instruction Interface
  //-----------------------

  // check for execute flag on memory
  assign match_any_execute_region_o = config_pkg::is_inside_execute_regions(
      CVA6Cfg, {{64 - CVA6Cfg.PLEN{1'b0}}, icache_areq_o.fetch_paddr}
  );

  // The instruction interface is a simple request response interface
  always_comb begin : instr_interface
    icache_areq_o.fetch_valid     = icache_areq_i.fetch_req;
    icache_areq_o.fetch_paddr     = fetch_vaddr_plen;
    icache_areq_o.fetch_exception = '0;

    // if it didn't match any execute region throw an `Instruction Access Fault`
    // or: if we are not translating, check PMPs immediately on the paddr
    if (!match_any_execute_region_o || !instr_allow_o) begin
      icache_areq_o.fetch_exception.cause = riscv::INSTR_ACCESS_FAULT;
      icache_areq_o.fetch_exception.valid = 1'b1;

      if (CVA6Cfg.TvalEn) begin
        if (enable_translation_i || enable_g_translation_i) begin
          icache_areq_o.fetch_exception.tval = CVA6Cfg.XLEN'(icache_areq_i.fetch_vaddr);
        end else begin
          icache_areq_o.fetch_exception.tval=CVA6Cfg.XLEN'(icache_areq_o.fetch_paddr[CVA6Cfg.PLEN-1:(CVA6Cfg.PLEN > CVA6Cfg.VLEN) ? (CVA6Cfg.PLEN - CVA6Cfg.VLEN) : 0]);
        end
      end
      if (CVA6Cfg.RVH) begin
        icache_areq_o.fetch_exception.tval2 = '0;
        icache_areq_o.fetch_exception.tinst = '0;
        icache_areq_o.fetch_exception.gva   = v_i;
      end
    end
  end

  // Instruction fetch
  pmp #(
      .CVA6Cfg   (CVA6Cfg),
      .PLEN      (CVA6Cfg.PLEN),
      .PMP_LEN   (CVA6Cfg.PLEN - 2),
      .NR_ENTRIES(CVA6Cfg.NrPMPEntries)
  ) i_pmp_if (
      .addr_i       (icache_areq_o.fetch_paddr),
      .priv_lvl_i   (priv_lvl_i),
      // we will always execute on the instruction fetch port
      .access_type_i(riscv::ACCESS_EXEC),
      // Configuration
      .conf_addr_i  (pmpaddr_i),
      .conf_i       (pmpcfg_i),
      .allow_o      (instr_allow_o)
  );

  //-----------------------
  // Data Interface
  //-----------------------
  // The data interface is simpler and only consists of a request/response interface
  always_comb begin : data_interface
    // save request and DTLB response
    lsu_req_n             = lsu_req_i;
    misaligned_ex_n       = misaligned_ex_i;
    lsu_is_store_n        = lsu_is_store_i;

    lsu_paddr_o           = mmu_vaddr_plen;
    lsu_valid_o           = lsu_req_q;
    lsu_exception_o       = misaligned_ex_q;
    pmp_access_type       = lsu_is_store_q ? riscv::ACCESS_WRITE : riscv::ACCESS_READ;

    // mute misaligned exceptions if there is no request otherwise they will throw accidental exceptions
    misaligned_ex_n.valid = misaligned_ex_i.valid & lsu_req_i;

    // If translation is not enabled, check the paddr immediately against PMPs
    if (lsu_req_q && !misaligned_ex_q.valid && !data_allow_o) begin
      lsu_exception_o.valid = 1'b1;

      if (CVA6Cfg.TvalEn) begin
        if (en_ld_st_translation_i || en_ld_st_g_translation_i) begin
          lsu_exception_o.tval = {
            {CVA6Cfg.XLEN - CVA6Cfg.VLEN{lsu_vaddr_q[CVA6Cfg.VLEN-1]}}, lsu_vaddr_q
          };
        end else begin
          lsu_exception_o.tval = CVA6Cfg.XLEN'(lsu_paddr_o[CVA6Cfg.PLEN-1:(CVA6Cfg.PLEN>CVA6Cfg.VLEN)?(CVA6Cfg.PLEN-CVA6Cfg.VLEN) : 0]);

        end
      end

      if (CVA6Cfg.RVH) begin
        lsu_exception_o.tval2 = '0;
        lsu_exception_o.tinst = lsu_tinst_q;
        lsu_exception_o.gva   = ld_st_v_i;
      end

      if (lsu_is_store_q) begin
        lsu_exception_o.cause = riscv::ST_ACCESS_FAULT;
      end else begin
        lsu_exception_o.cause = riscv::LD_ACCESS_FAULT;
      end
    end
  end

  // Load/store PMP check
  pmp #(
      .CVA6Cfg   (CVA6Cfg),
      .PLEN      (CVA6Cfg.PLEN),
      .PMP_LEN   (CVA6Cfg.PLEN - 2),
      .NR_ENTRIES(CVA6Cfg.NrPMPEntries)
  ) i_pmp_data (
      .addr_i       (lsu_paddr_o),
      .priv_lvl_i   (ld_st_priv_lvl_i),
      .access_type_i(pmp_access_type),
      // Configuration
      .conf_addr_i  (pmpaddr_i),
      .conf_i       (pmpcfg_i),
      .allow_o      (data_allow_o)
  );

  // ----------
  // Registers
  // ----------
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (~rst_ni) begin
      lsu_req_q       <= '0;
      misaligned_ex_q <= '0;
      lsu_is_store_q  <= '0;
      lsu_vaddr_q     <= '0;
      lsu_tinst_q     <= '0;
    end else begin
      lsu_req_q       <= lsu_req_n;
      misaligned_ex_q <= misaligned_ex_n;
      lsu_is_store_q  <= lsu_is_store_n;
      lsu_vaddr_q     <= lsu_vaddr_i;

      if (CVA6Cfg.RVH) begin
        lsu_tinst_q <= lsu_tinst_i;
      end
    end
  end
endmodule

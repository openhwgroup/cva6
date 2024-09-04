// Copyright 2017-2019 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// Author: Florian Zaruba, ETH Zurich
// Date: 19.03.2017
// Description: CVA6 Top-level module

`include "rvfi_types.svh"
`include "cvxif_types.svh"

module cva6
  import ariane_pkg::*;
#(
    // CVA6 config
    parameter config_pkg::cva6_cfg_t CVA6Cfg = build_config_pkg::build_config(
        cva6_config_pkg::cva6_cfg
    ),

    // RVFI PROBES
    parameter type rvfi_probes_instr_t = `RVFI_PROBES_INSTR_T(CVA6Cfg),
    parameter type rvfi_probes_csr_t = `RVFI_PROBES_CSR_T(CVA6Cfg),
    parameter type rvfi_probes_t = struct packed {
      logic csr;
      rvfi_probes_instr_t instr;
    },

    // branchpredict scoreboard entry
    // this is the struct which we will inject into the pipeline to guide the various
    // units towards the correct branch decision and resolve
    localparam type branchpredict_sbe_t = struct packed {
      cf_t                     cf;               // type of control flow prediction
      logic [CVA6Cfg.VLEN-1:0] predict_address;  // target address at which to jump, or not
    },

    localparam type exception_t = struct packed {
      logic [CVA6Cfg.XLEN-1:0] cause;  // cause of exception
      logic [CVA6Cfg.XLEN-1:0] tval;  // additional information of causing exception (e.g.: instruction causing it),
      // address of LD/ST fault
      logic [CVA6Cfg.GPLEN-1:0] tval2;  // additional information when the causing exception in a guest exception
      logic [31:0] tinst;  // transformed instruction information
      logic gva;  // signals when a guest virtual address is written to tval
      logic valid;
    },

    // cache request ports
    // I$ address translation requests
    localparam type icache_areq_t = struct packed {
      logic                    fetch_valid;      // address translation valid
      logic [CVA6Cfg.PLEN-1:0] fetch_paddr;      // physical address in
      exception_t              fetch_exception;  // exception occurred during fetch
    },
    localparam type icache_arsp_t = struct packed {
      logic                    fetch_req;    // address translation request
      logic [CVA6Cfg.VLEN-1:0] fetch_vaddr;  // virtual address out
    },

    // I$ data requests
    localparam type icache_dreq_t = struct packed {
      logic                    req;      // we request a new word
      logic                    kill_s1;  // kill the current request
      logic                    kill_s2;  // kill the last request
      logic                    spec;     // request is speculative
      logic [CVA6Cfg.VLEN-1:0] vaddr;    // 1st cycle: 12 bit index is taken for lookup
    },
    localparam type icache_drsp_t = struct packed {
      logic                                ready;  // icache is ready
      logic                                valid;  // signals a valid read
      logic [CVA6Cfg.FETCH_WIDTH-1:0]      data;   // 2+ cycle out: tag
      logic [CVA6Cfg.FETCH_USER_WIDTH-1:0] user;   // User bits
      logic [CVA6Cfg.VLEN-1:0]             vaddr;  // virtual address out
      exception_t                          ex;     // we've encountered an exception
    },

    // IF/ID Stage
    // store the decompressed instruction
    localparam type fetch_entry_t = struct packed {
      logic [CVA6Cfg.VLEN-1:0] address;  // the address of the instructions from below
      logic [31:0] instruction;  // instruction word
      branchpredict_sbe_t     branch_predict; // this field contains branch prediction information regarding the forward branch path
      exception_t             ex;             // this field contains exceptions which might have happened earlier, e.g.: fetch exceptions
    },

    // ID/EX/WB Stage
    localparam type scoreboard_entry_t = struct packed {
      logic [CVA6Cfg.VLEN-1:0] pc;  // PC of instruction
      logic [CVA6Cfg.TRANS_ID_BITS-1:0] trans_id;      // this can potentially be simplified, we could index the scoreboard entry
      // with the transaction id in any case make the width more generic
      fu_t fu;  // functional unit to use
      fu_op op;  // operation to perform in each functional unit
      logic [REG_ADDR_SIZE-1:0] rs1;  // register source address 1
      logic [REG_ADDR_SIZE-1:0] rs2;  // register source address 2
      logic [REG_ADDR_SIZE-1:0] rd;  // register destination address
      logic [CVA6Cfg.XLEN-1:0] result;  // for unfinished instructions this field also holds the immediate,
      // for unfinished floating-point that are partly encoded in rs2, this field also holds rs2
      // for unfinished floating-point fused operations (FMADD, FMSUB, FNMADD, FNMSUB)
      // this field holds the address of the third operand from the floating-point register file
      logic valid;  // is the result valid
      logic use_imm;  // should we use the immediate as operand b?
      logic use_zimm;  // use zimm as operand a
      logic use_pc;  // set if we need to use the PC as operand a, PC from exception
      exception_t ex;  // exception has occurred
      branchpredict_sbe_t bp;  // branch predict scoreboard data structure
      logic                     is_compressed; // signals a compressed instructions, we need this information at the commit stage if
                                               // we want jump accordingly e.g.: +4, +2
      logic is_macro_instr;  // is an instruction executed as predefined sequence of instructions called macro definition
      logic is_last_macro_instr;  // is last decoded 32bit instruction of macro definition
      logic is_double_rd_macro_instr;  // is double move decoded 32bit instruction of macro definition
      logic vfp;  // is this a vector floating-point instruction?
    },

    // branch-predict
    // this is the struct we get back from ex stage and we will use it to update
    // all the necessary data structures
    // bp_resolve_t
    localparam type bp_resolve_t = struct packed {
      logic                    valid;           // prediction with all its values is valid
      logic [CVA6Cfg.VLEN-1:0] pc;              // PC of predict or mis-predict
      logic [CVA6Cfg.VLEN-1:0] target_address;  // target address at which to jump, or not
      logic                    is_mispredict;   // set if this was a mis-predict
      logic                    is_taken;        // branch is taken
      cf_t                     cf_type;         // Type of control flow change
    },

    // All information needed to determine whether we need to associate an interrupt
    // with the corresponding instruction or not.
    localparam type irq_ctrl_t = struct packed {
      logic [CVA6Cfg.XLEN-1:0] mie;
      logic [CVA6Cfg.XLEN-1:0] mip;
      logic [CVA6Cfg.XLEN-1:0] mideleg;
      logic [CVA6Cfg.XLEN-1:0] hideleg;
      logic                    sie;
      logic                    global_enable;
    },

    localparam type lsu_ctrl_t = struct packed {
      logic                             valid;
      logic [CVA6Cfg.VLEN-1:0]          vaddr;
      logic [31:0]                      tinst;
      logic                             hs_ld_st_inst;
      logic                             hlvx_inst;
      logic                             overflow;
      logic                             g_overflow;
      logic [CVA6Cfg.XLEN-1:0]          data;
      logic [(CVA6Cfg.XLEN/8)-1:0]      be;
      fu_t                              fu;
      fu_op                             operation;
      logic [CVA6Cfg.TRANS_ID_BITS-1:0] trans_id;
    },

    localparam type fu_data_t = struct packed {
      fu_t                              fu;
      fu_op                             operation;
      logic [CVA6Cfg.XLEN-1:0]          operand_a;
      logic [CVA6Cfg.XLEN-1:0]          operand_b;
      logic [CVA6Cfg.XLEN-1:0]          imm;
      logic [CVA6Cfg.TRANS_ID_BITS-1:0] trans_id;
    },

    localparam type icache_req_t = struct packed {
      logic [CVA6Cfg.ICACHE_SET_ASSOC_WIDTH-1:0] way;  // way to replace
      logic [CVA6Cfg.PLEN-1:0] paddr;  // physical address
      logic nc;  // noncacheable
      logic [CVA6Cfg.MEM_TID_WIDTH-1:0] tid;  // threadi id (used as transaction id in Ariane)
    },
    localparam type icache_rtrn_t = struct packed {
      wt_cache_pkg::icache_in_t rtype;  // see definitions above
      logic [CVA6Cfg.ICACHE_LINE_WIDTH-1:0] data;  // full cache line width
      logic [CVA6Cfg.ICACHE_USER_LINE_WIDTH-1:0] user;  // user bits
      struct packed {
        logic                                      vld;  // invalidate only affected way
        logic                                      all;  // invalidate all ways
        logic [CVA6Cfg.ICACHE_INDEX_WIDTH-1:0]     idx;  // physical address to invalidate
        logic [CVA6Cfg.ICACHE_SET_ASSOC_WIDTH-1:0] way;  // way to invalidate
      } inv;  // invalidation vector
      logic [CVA6Cfg.MEM_TID_WIDTH-1:0] tid;  // threadi id (used as transaction id in Ariane)
    },

    // D$ data requests
    localparam type dcache_req_i_t = struct packed {
      logic [CVA6Cfg.DCACHE_INDEX_WIDTH-1:0] address_index;
      logic [CVA6Cfg.DCACHE_TAG_WIDTH-1:0]   address_tag;
      logic [CVA6Cfg.XLEN-1:0]               data_wdata;
      logic [CVA6Cfg.DCACHE_USER_WIDTH-1:0]  data_wuser;
      logic                                  data_req;
      logic                                  data_we;
      logic [(CVA6Cfg.XLEN/8)-1:0]           data_be;
      logic [1:0]                            data_size;
      logic [CVA6Cfg.DcacheIdWidth-1:0]      data_id;
      logic                                  kill_req;
      logic                                  tag_valid;
    },

    localparam type dcache_req_o_t = struct packed {
      logic                                 data_gnt;
      logic                                 data_rvalid;
      logic [CVA6Cfg.DcacheIdWidth-1:0]     data_rid;
      logic [CVA6Cfg.XLEN-1:0]              data_rdata;
      logic [CVA6Cfg.DCACHE_USER_WIDTH-1:0] data_ruser;
    },

    // AXI types
    parameter type axi_ar_chan_t = struct packed {
      logic [CVA6Cfg.AxiIdWidth-1:0]   id;
      logic [CVA6Cfg.AxiAddrWidth-1:0] addr;
      axi_pkg::len_t                   len;
      axi_pkg::size_t                  size;
      axi_pkg::burst_t                 burst;
      logic                            lock;
      axi_pkg::cache_t                 cache;
      axi_pkg::prot_t                  prot;
      axi_pkg::qos_t                   qos;
      axi_pkg::region_t                region;
      logic [CVA6Cfg.AxiUserWidth-1:0] user;
    },
    parameter type axi_aw_chan_t = struct packed {
      logic [CVA6Cfg.AxiIdWidth-1:0]   id;
      logic [CVA6Cfg.AxiAddrWidth-1:0] addr;
      axi_pkg::len_t                   len;
      axi_pkg::size_t                  size;
      axi_pkg::burst_t                 burst;
      logic                            lock;
      axi_pkg::cache_t                 cache;
      axi_pkg::prot_t                  prot;
      axi_pkg::qos_t                   qos;
      axi_pkg::region_t                region;
      axi_pkg::atop_t                  atop;
      logic [CVA6Cfg.AxiUserWidth-1:0] user;
    },
    parameter type axi_w_chan_t = struct packed {
      logic [CVA6Cfg.AxiDataWidth-1:0]     data;
      logic [(CVA6Cfg.AxiDataWidth/8)-1:0] strb;
      logic                                last;
      logic [CVA6Cfg.AxiUserWidth-1:0]     user;
    },
    parameter type b_chan_t = struct packed {
      logic [CVA6Cfg.AxiIdWidth-1:0]   id;
      axi_pkg::resp_t                  resp;
      logic [CVA6Cfg.AxiUserWidth-1:0] user;
    },
    parameter type r_chan_t = struct packed {
      logic [CVA6Cfg.AxiIdWidth-1:0]   id;
      logic [CVA6Cfg.AxiDataWidth-1:0] data;
      axi_pkg::resp_t                  resp;
      logic                            last;
      logic [CVA6Cfg.AxiUserWidth-1:0] user;
    },
    parameter type noc_req_t = struct packed {
      axi_aw_chan_t aw;
      logic         aw_valid;
      axi_w_chan_t  w;
      logic         w_valid;
      logic         b_ready;
      axi_ar_chan_t ar;
      logic         ar_valid;
      logic         r_ready;
    },
    parameter type noc_resp_t = struct packed {
      logic    aw_ready;
      logic    ar_ready;
      logic    w_ready;
      logic    b_valid;
      b_chan_t b;
      logic    r_valid;
      r_chan_t r;
    },
    localparam NumPorts = 4,
    //
    parameter type acc_cfg_t = logic,
    parameter acc_cfg_t AccCfg = '0,
    // CVXIF Types
    parameter type readregflags_t = `READREGFLAGS_T(CVA6Cfg),
    parameter type writeregflags_t = `WRITEREGFLAGS_T(CVA6Cfg),
    parameter type id_t = `ID_T(CVA6Cfg),
    parameter type hartid_t = `HARTID_T(CVA6Cfg),
    parameter type x_compressed_req_t = `X_COMPRESSED_REQ_T(CVA6Cfg, hartid_t),
    parameter type x_compressed_resp_t = `X_COMPRESSED_RESP_T(CVA6Cfg),
    parameter type x_issue_req_t = `X_ISSUE_REQ_T(CVA6Cfg, hartit_t, id_t),
    parameter type x_issue_resp_t = `X_ISSUE_RESP_T(CVA6Cfg, writeregflags_t, readregflags_t),
    parameter type x_register_t = `X_REGISTER_T(CVA6Cfg, hartid_t, id_t, readregflags_t),
    parameter type x_commit_t = `X_COMMIT_T(CVA6Cfg, hartid_t, id_t),
    parameter type x_result_t = `X_RESULT_T(CVA6Cfg, hartid_t, id_t, writeregflags_t),
    parameter type cvxif_req_t =
    `CVXIF_REQ_T(CVA6Cfg, x_compressed_req_t, x_issue_req_t, x_register_req_t, x_commit_t),
    parameter type cvxif_resp_t =
    `CVXIF_RESP_T(CVA6Cfg, x_compressed_resp_t, x_issue_resp_t, x_result_t)
) (
    // Subsystem Clock - SUBSYSTEM
    input logic clk_i,
    // Asynchronous reset active low - SUBSYSTEM
    input logic rst_ni,
    // Reset boot address - SUBSYSTEM
    input logic [CVA6Cfg.VLEN-1:0] boot_addr_i,
    // Hard ID reflected as CSR - SUBSYSTEM
    input logic [CVA6Cfg.XLEN-1:0] hart_id_i,
    // Level sensitive (async) interrupts - SUBSYSTEM
    input logic [1:0] irq_i,
    // Inter-processor (async) interrupt - SUBSYSTEM
    input logic ipi_i,
    // Timer (async) interrupt - SUBSYSTEM
    input logic time_irq_i,
    // Debug (async) request - SUBSYSTEM
    input logic debug_req_i,
    // Probes to build RVFI, can be left open when not used - RVFI
    output rvfi_probes_t rvfi_probes_o,
    // CVXIF request - SUBSYSTEM
    output cvxif_req_t cvxif_req_o,
    // CVXIF response - SUBSYSTEM
    input cvxif_resp_t cvxif_resp_i,
    // noc request, can be AXI or OpenPiton - SUBSYSTEM
    output noc_req_t noc_req_o,
    // noc response, can be AXI or OpenPiton - SUBSYSTEM
    input noc_resp_t noc_resp_i
);

  riscv::priv_lvl_t priv_lvl;
  logic icache_en;
  logic icache_flush;
  logic icache_miss;
  icache_areq_t icache_areq;
  icache_arsp_t icache_arsp;
  icache_dreq_t icache_dreq;
  icache_drsp_t icache_drsp;
  logic dcache_enable;
  logic dcache_flush;
  logic dcache_flush_ack;
  logic dcache_miss;
  logic [NumPorts-1:0][CVA6Cfg.DCACHE_SET_ASSOC-1:0] miss_vld_bits;
  amo_req_t dcache_amo_req;
  amo_resp_t dcache_amo_resp;
  dcache_req_i_t [NumPorts-1:0] dcache_req_ports;
  dcache_req_o_t [NumPorts-1:0] dcache_rsp_ports;
  logic wbuffer_empty;
  logic wbuffer_not_ni;
  logic [63:0] inval_addr;
  logic inval_valid;
  logic inval_ready;


  cva6_core #(
      // CVA6 config
      .CVA6Cfg(CVA6Cfg),
      // RVFI PROBES
      .rvfi_probes_instr_t(rvfi_probes_instr_t),
      .rvfi_probes_csr_t(rvfi_probes_csr_t),
      .rvfi_probes_t(rvfi_probes_t),
      // cache request ports
      // I$ address translation requests
      .icache_areq_t(icache_areq_t),
      .icache_arsp_t(icache_arsp_t),
      // I$ data requests
      .icache_dreq_t(icache_dreq_t),
      .icache_drsp_t(icache_drsp_t),
      // D$ data requests
      .dcache_req_i_t(dcache_req_i_t),
      .dcache_req_o_t(dcache_req_o_t),
      //
      .NumPorts(NumPorts),
      .acc_cfg_t(acc_cfg_t),
      .AccCfg(AccCfg),
      // CVXIF Types
      .readregflags_t(readregflags_t),
      .writeregflags_t(writeregflags_t),
      .id_t(id_t),
      .hartid_t(hartid_t),
      .x_compressed_req_t(x_compressed_req_t),
      .x_compressed_resp_t(x_compressed_resp_t),
      .x_issue_req_t(x_issue_req_t),
      .x_issue_resp_t(x_issue_resp_t),
      .x_register_t(x_register_t),
      .x_commit_t(x_commit_t),
      .x_result_t(x_result_t),
      .cvxif_req_t(cvxif_req_t),
      .cvxif_resp_t(cvxif_resp_t)
  ) i_cva6_core (
      .clk_i             (clk_i),
      .rst_ni            (rst_ni),
      .boot_addr_i       (boot_addr_i),
      .hart_id_i         (hart_id_i),
      .irq_i             (irq_i),
      .ipi_i             (ipi_i),
      .time_irq_i        (time_irq_i),
      .debug_req_i       (debug_req_i),
      .rvfi_probes_o     (rvfi_probes_o),
      .cvxif_req_o       (cvxif_req_o),
      .cvxif_resp_i      (cvxif_resp_i),
      .priv_lvl_o        (priv_lvl),
      // FROM/TO CACHE SUBSYSTEM
      .icache_en_o       (icache_en),
      .icache_flush_o    (icache_flush),
      .icache_miss_i     (icache_miss),
      .icache_areq_o     (icache_areq),
      .icache_areq_i     (icache_arsp),
      .icache_dreq_o     (icache_dreq),
      .icache_dreq_i     (icache_drsp),
      .dcache_enable_o   (dcache_enable),
      .dcache_flush_o    (dcache_flush),
      .dcache_flush_ack_i(dcache_flush_ack),
      .dcache_miss_i     (dcache_miss),
      .miss_vld_bits_i   (miss_vld_bits),
      .dcache_amo_req_o  (dcache_amo_req),
      .dcache_amo_resp_i (dcache_amo_resp),
      .dcache_req_ports_o(dcache_req_ports),
      .dcache_req_ports_i(dcache_rsp_ports),
      .wbuffer_empty_i   (wbuffer_empty),
      .wbuffer_not_ni_i  (wbuffer_not_ni),
      .inval_addr_o      (inval_addr),
      .inval_valid_o     (inval_valid),
      .inval_ready_i     (inval_ready)
  );



  if (CVA6Cfg.DCacheType == config_pkg::WT) begin : gen_cache_wt
    // this is a cache subsystem that is compatible with OpenPiton
    wt_cache_subsystem #(
        .CVA6Cfg   (CVA6Cfg),
        .icache_areq_t(icache_areq_t),
        .icache_arsp_t(icache_arsp_t),
        .icache_dreq_t(icache_dreq_t),
        .icache_drsp_t(icache_drsp_t),
        .icache_req_t(icache_req_t),
        .icache_rtrn_t(icache_rtrn_t),
        .dcache_req_i_t(dcache_req_i_t),
        .dcache_req_o_t(dcache_req_o_t),
        .NumPorts  (NumPorts),
        .noc_req_t (noc_req_t),
        .noc_resp_t(noc_resp_t)
    ) i_cache_subsystem (
        .clk_i             (clk_i),
        .rst_ni            (rst_ni),
        // I$
        .icache_en_i       (icache_en),
        .icache_flush_i    (icache_flush),
        .icache_miss_o     (icache_miss),
        .icache_areq_i     (icache_areq),
        .icache_areq_o     (icache_arsp),
        .icache_dreq_i     (icache_dreq),
        .icache_dreq_o     (icache_drsp),
        // D$
        .dcache_enable_i   (dcache_enable),
        .dcache_flush_i    (dcache_flush),
        .dcache_flush_ack_o(dcache_flush_ack),
        // to commit stage
        .dcache_amo_req_i  (dcache_amo_req),
        .dcache_amo_resp_o (dcache_amo_resp),
        // from PTW, Load Unit  and Store Unit
        .dcache_miss_o     (dcache_miss),
        .miss_vld_bits_o   (miss_vld_bits),
        .dcache_req_ports_i(dcache_req_ports),
        .dcache_req_ports_o(dcache_rsp_ports),
        // write buffer status
        .wbuffer_empty_o   (wbuffer_empty),
        .wbuffer_not_ni_o  (wbuffer_not_ni),
        // memory side
        .noc_req_o         (noc_req_o),
        .noc_resp_i        (noc_resp_i),
        .inval_addr_i      (inval_addr),
        .inval_valid_i     (inval_valid),
        .inval_ready_o     (inval_ready)
    );
  end else if (CVA6Cfg.DCacheType == config_pkg::HPDCACHE) begin : gen_cache_hpd
    cva6_hpdcache_subsystem #(
        .CVA6Cfg   (CVA6Cfg),
        .icache_areq_t(icache_areq_t),
        .icache_arsp_t(icache_arsp_t),
        .icache_dreq_t(icache_dreq_t),
        .icache_drsp_t(icache_drsp_t),
        .icache_req_t(icache_req_t),
        .icache_rtrn_t(icache_rtrn_t),
        .dcache_req_i_t(dcache_req_i_t),
        .dcache_req_o_t(dcache_req_o_t),
        .NumPorts  (NumPorts),
        .axi_ar_chan_t(axi_ar_chan_t),
        .axi_aw_chan_t(axi_aw_chan_t),
        .axi_w_chan_t (axi_w_chan_t),
        .axi_b_chan_t (b_chan_t),
        .axi_r_chan_t (r_chan_t),
        .noc_req_t (noc_req_t),
        .noc_resp_t(noc_resp_t),
        .cmo_req_t (logic  /*FIXME*/),
        .cmo_rsp_t (logic  /*FIXME*/)
    ) i_cache_subsystem (
        .clk_i (clk_i),
        .rst_ni(rst_ni),

        .icache_en_i   (icache_en),
        .icache_flush_i(icache_flush),
        .icache_miss_o (icache_miss),
        .icache_areq_i (icache_areq),
        .icache_areq_o (icache_arsp),
        .icache_dreq_i (icache_dreq),
        .icache_dreq_o (icache_drsp),

        .dcache_enable_i   (dcache_enable),
        .dcache_flush_i    (dcache_flush),
        .dcache_flush_ack_o(dcache_flush_ack),
        .dcache_miss_o     (dcache_miss),

        .dcache_amo_req_i (dcache_amo_req),
        .dcache_amo_resp_o(dcache_amo_resp),

        .dcache_cmo_req_i ('0  /*FIXME*/),
        .dcache_cmo_resp_o(  /*FIXME*/),

        .dcache_req_ports_i(dcache_req_ports),
        .dcache_req_ports_o(dcache_rsp_ports),

        .wbuffer_empty_o (wbuffer_empty),
        .wbuffer_not_ni_o(wbuffer_not_ni),

        .hwpf_base_set_i    ('0  /*FIXME*/),
        .hwpf_base_i        ('0  /*FIXME*/),
        .hwpf_base_o        (  /*FIXME*/),
        .hwpf_param_set_i   ('0  /*FIXME*/),
        .hwpf_param_i       ('0  /*FIXME*/),
        .hwpf_param_o       (  /*FIXME*/),
        .hwpf_throttle_set_i('0  /*FIXME*/),
        .hwpf_throttle_i    ('0  /*FIXME*/),
        .hwpf_throttle_o    (  /*FIXME*/),
        .hwpf_status_o      (  /*FIXME*/),

        .noc_req_o (noc_req_o),
        .noc_resp_i(noc_resp_i)
    );
    assign inval_ready   = 1'b1;
    assign miss_vld_bits = '0;
  end else begin : gen_cache_wb
    std_cache_subsystem #(
        // note: this only works with one cacheable region
        // not as important since this cache subsystem is about to be
        // deprecated
        .CVA6Cfg       (CVA6Cfg),
        .icache_areq_t (icache_areq_t),
        .icache_arsp_t (icache_arsp_t),
        .icache_dreq_t (icache_dreq_t),
        .icache_drsp_t (icache_drsp_t),
        .icache_req_t  (icache_req_t),
        .icache_rtrn_t (icache_rtrn_t),
        .dcache_req_i_t(dcache_req_i_t),
        .dcache_req_o_t(dcache_req_o_t),
        .NumPorts      (NumPorts),
        .axi_ar_chan_t (axi_ar_chan_t),
        .axi_aw_chan_t (axi_aw_chan_t),
        .axi_w_chan_t  (axi_w_chan_t),
        .axi_req_t     (noc_req_t),
        .axi_rsp_t     (noc_resp_t)
    ) i_cache_subsystem (
        // to D$
        .clk_i             (clk_i),
        .rst_ni            (rst_ni),
        .priv_lvl_i        (priv_lvl),
        // I$
        .icache_en_i       (icache_en),
        .icache_flush_i    (icache_flush),
        .icache_miss_o     (icache_miss),
        .icache_areq_i     (icache_areq),
        .icache_areq_o     (icache_arsp),
        .icache_dreq_i     (icache_dreq),
        .icache_dreq_o     (icache_drsp),
        // D$
        .dcache_enable_i   (dcache_enable),
        .dcache_flush_i    (dcache_flush),
        .dcache_flush_ack_o(dcache_flush_ack),
        // to commit stage
        .amo_req_i         (dcache_amo_req),
        .amo_resp_o        (dcache_amo_resp),
        .dcache_miss_o     (dcache_miss),
        // this is statically set to 1 as the std_cache does not have a wbuffer
        .wbuffer_empty_o   (wbuffer_empty),
        // from PTW, Load Unit  and Store Unit
        .dcache_req_ports_i(dcache_req_ports),
        .dcache_req_ports_o(dcache_rsp_ports),
        // memory side
        .axi_req_o         (noc_req_o),
        .axi_resp_i        (noc_resp_i)
    );
    assign wbuffer_not_ni = 1'b1;
    assign inval_ready    = 1'b1;
    assign miss_vld_bits  = '0;
  end



endmodule  // ariane

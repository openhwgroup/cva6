/* Copyright 2018 ETH Zurich and University of Bologna.
 * Copyright and related rights are licensed under the Solderpad Hardware
 * License, Version 0.51 (the “License”); you may not use this file except in
 * compliance with the License.  You may obtain a copy of the License at
 * http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
 * or agreed to in writing, software, hardware and materials distributed under
 * this License is distributed on an “AS IS” BASIS, WITHOUT WARRANTIES OR
 * CONDITIONS OF ANY KIND, either express or implied. See the License for the
 * specific language governing permissions and limitations under the License.
 *
 * File:   ariane_pkg.sv
 * Author: Florian Zaruba <zarubaf@iis.ee.ethz.ch>
 * Date:   8.4.2017
 *
 * Description: Contains all the necessary defines for Ariane
 *              in one package.
 */

// this is needed to propagate the
// configuration in case Ariane is
// instantiated in OpenPiton
`ifdef PITON_ARIANE
`include "l15.tmp.h"
`endif

/// This package contains `functions` and global defines for CVA6.
/// *Note*: There are some parameters here as well which will eventually be
/// moved out to favour a fully parameterizable core.
package ariane_pkg;

  // TODO: Slowly move those parameters to the new system.
  localparam BITS_SATURATION_COUNTER = 2;

  // depth of store-buffers, this needs to be a power of two
  localparam logic [2:0] DEPTH_SPEC = 'd4;

  // if CVA6Cfg.DCacheType = cva6_config_pkg::WT
  // we can use a small commit queue since we have a write buffer in the dcache
  // we could in principle do without the commit queue in this case, but the timing degrades if we do that due
  // to longer paths into the commit stage
  // if CVA6Cfg.DCacheType = cva6_config_pkg::WB
  // allocate more space for the commit buffer to be on the save side, this needs to be a power of two
  localparam logic [2:0] DEPTH_COMMIT = 'd4;

  // Transprecision float unit
  localparam int unsigned LAT_COMP_FP32 = 'd2;
  localparam int unsigned LAT_COMP_FP64 = 'd3;
  localparam int unsigned LAT_COMP_FP16 = 'd1;
  localparam int unsigned LAT_COMP_FP16ALT = 'd1;
  localparam int unsigned LAT_COMP_FP8 = 'd1;
  localparam int unsigned LAT_DIVSQRT = 'd2;
  localparam int unsigned LAT_NONCOMP = 'd1;
  localparam int unsigned LAT_CONV = 'd2;

  localparam logic [31:0] OPENHWGROUP_MVENDORID = 32'h0602;
  localparam logic [31:0] ARIANE_MARCHID = 32'd3;

  // 32 registers
  localparam REG_ADDR_SIZE = 5;

  // Read ports for general purpose register files
  localparam NR_RGPR_PORTS = 2;

  // static debug hartinfo
  // debug causes
  localparam logic [2:0] CauseBreakpoint = 3'h1;
  localparam logic [2:0] CauseTrigger = 3'h2;
  localparam logic [2:0] CauseRequest = 3'h3;
  localparam logic [2:0] CauseSingleStep = 3'h4;
  // amount of data count registers implemented
  localparam logic [3:0] DataCount = 4'h2;

  // address where data0-15 is shadowed or if shadowed in a CSR
  // address of the first CSR used for shadowing the data
  localparam logic [11:0] DataAddr = 12'h380;  // we are aligned with Rocket here
  typedef struct packed {
    logic [31:24] zero1;
    logic [23:20] nscratch;
    logic [19:17] zero0;
    logic         dataaccess;
    logic [15:12] datasize;
    logic [11:0]  dataaddr;
  } hartinfo_t;

  localparam hartinfo_t DebugHartInfo = '{
      zero1: '0,
      nscratch: 2,  // Debug module needs at least two scratch regs
      zero0: '0,
      dataaccess: 1'b1,  // data registers are memory mapped in the debugger
      datasize: DataCount,
      dataaddr: DataAddr
  };

  // enables a commit log which matches spikes commit log format for easier trace comparison
  localparam bit ENABLE_SPIKE_COMMIT_LOG = 1'b1;

  // ------------- Dangerous -------------
  // if set to zero a flush will not invalidate the cache-lines, in a single core environment
  // where coherence is not necessary this can improve performance. This needs to be switched on
  // when more than one core is in a system
  localparam logic INVALIDATE_ON_FLUSH = 1'b1;

`ifdef SPIKE_TANDEM
  // Spike still places 0 in TVAL for ENV_CALL_* exceptions.
  // This may eventually go away when Spike starts to handle TVAL for *all* exceptions.
  localparam bit ZERO_TVAL = 1'b1;
`else
  localparam bit ZERO_TVAL = 1'b0;
`endif

  // read mask for SSTATUS over MMSTATUS
  function automatic logic [63:0] smode_status_read_mask(config_pkg::cva6_cfg_t Cfg);
    return riscv::SSTATUS_UIE
    | riscv::SSTATUS_SIE
    | riscv::SSTATUS_SPIE
    | riscv::SSTATUS_SPP
    | riscv::SSTATUS_FS
    | riscv::SSTATUS_XS
    | riscv::SSTATUS_SUM
    | riscv::SSTATUS_MXR
    | riscv::SSTATUS_UPIE
    | riscv::SSTATUS_SPIE
    | riscv::SSTATUS_UXL
    | riscv::sstatus_sd(Cfg.IS_XLEN64);
  endfunction

  localparam logic [63:0] SMODE_STATUS_WRITE_MASK = riscv::SSTATUS_SIE
                                                    | riscv::SSTATUS_SPIE
                                                    | riscv::SSTATUS_SPP
                                                    | riscv::SSTATUS_FS
                                                    | riscv::SSTATUS_SUM
                                                    | riscv::SSTATUS_MXR;

  localparam logic [63:0] HSTATUS_WRITE_MASK      = riscv::HSTATUS_VSBE
                                                    | riscv::HSTATUS_GVA
                                                    | riscv::HSTATUS_SPV
                                                    | riscv::HSTATUS_SPVP
                                                    | riscv::HSTATUS_HU
                                                    | riscv::HSTATUS_VTVM
                                                    | riscv::HSTATUS_VTW
                                                    | riscv::HSTATUS_VTSR;

  // hypervisor delegable interrupts
  function automatic logic [31:0] hs_deleg_interrupts(config_pkg::cva6_cfg_t Cfg);
    return riscv::MIP_VSSIP | riscv::MIP_VSTIP | riscv::MIP_VSEIP;
  endfunction

  // virtual supervisor delegable interrupts
  function automatic logic [31:0] vs_deleg_interrupts(config_pkg::cva6_cfg_t Cfg);
    return riscv::MIP_VSSIP | riscv::MIP_VSTIP | riscv::MIP_VSEIP;
  endfunction

  // ---------------
  // AXI
  // ---------------

  typedef enum logic {
    SINGLE_REQ,
    CACHE_LINE_REQ
  } ad_req_t;

  // ---------------
  // Fetch Stage
  // ---------------

  // leave as is (fails with >8 entries and wider fetch width)
  localparam int unsigned FETCH_FIFO_DEPTH = 4;
  localparam int unsigned FETCH_ADDR_FIFO_DEPTH = 2;

  typedef enum logic [2:0] {
    NoCF,    // No control flow prediction
    Branch,  // Branch
    Jump,    // Jump to address from immediate
    JumpR,   // Jump to address from registers
    Return   // Return Address Prediction
  } cf_t;

  typedef struct packed {
    logic valid;
    logic taken;
  } bht_prediction_t;

  typedef struct packed {
    logic       valid;
    logic [1:0] saturation_counter;
  } bht_t;

  typedef enum logic [3:0] {
    NONE,       // 0
    LOAD,       // 1
    STORE,      // 2
    ALU,        // 3
    CTRL_FLOW,  // 4
    MULT,       // 5
    CSR,        // 6
    FPU,        // 7
    FPU_VEC,    // 8
    CVXIF,      // 9
    ACCEL       // 10
  } fu_t;

  // Index of writeback ports
  localparam FLU_WB = 0;
  localparam STORE_WB = 1;
  localparam LOAD_WB = 2;
  localparam FPU_WB = 3;
  localparam ACC_WB = 4;
  localparam X_WB = 4;

  localparam EXC_OFF_RST = 8'h80;

  localparam SupervisorIrq = 1;
  localparam MachineIrq = 0;

  // ---------------
  // Cache config
  // ---------------

  // for usage in OpenPiton we have to propagate the openpiton L15 configuration from l15.h
`ifdef PITON_ARIANE

`ifndef CONFIG_L1I_CACHELINE_WIDTH
  `define CONFIG_L1I_CACHELINE_WIDTH 128
`endif

`ifndef CONFIG_L1I_ASSOCIATIVITY
  `define CONFIG_L1I_ASSOCIATIVITY 4
`endif

`ifndef CONFIG_L1I_SIZE
  `define CONFIG_L1I_SIZE 16*1024
`endif

`ifndef CONFIG_L1D_CACHELINE_WIDTH
  `define CONFIG_L1D_CACHELINE_WIDTH 128
`endif

`ifndef CONFIG_L1D_ASSOCIATIVITY
  `define CONFIG_L1D_ASSOCIATIVITY 8
`endif

`ifndef CONFIG_L1D_SIZE
  `define CONFIG_L1D_SIZE 32*1024
`endif

`ifndef L15_THREADID_WIDTH
  `define L15_THREADID_WIDTH 3
`endif

  // I$
  localparam int unsigned ICACHE_LINE_WIDTH = `CONFIG_L1I_CACHELINE_WIDTH;
  localparam int unsigned ICACHE_SET_ASSOC = `CONFIG_L1I_ASSOCIATIVITY;
  localparam int unsigned ICACHE_INDEX_WIDTH = $clog2(`CONFIG_L1I_SIZE / ICACHE_SET_ASSOC);
  localparam int unsigned ICACHE_TAG_WIDTH = riscv::PLEN - ICACHE_INDEX_WIDTH;
  localparam int unsigned ICACHE_USER_LINE_WIDTH = (AXI_USER_WIDTH == 1) ? 4 : 128;  // in bit
  // D$
  localparam int unsigned DCACHE_LINE_WIDTH = `CONFIG_L1D_CACHELINE_WIDTH;
  localparam int unsigned DCACHE_SET_ASSOC = `CONFIG_L1D_ASSOCIATIVITY;
  localparam int unsigned DCACHE_INDEX_WIDTH = $clog2(`CONFIG_L1D_SIZE / DCACHE_SET_ASSOC);
  localparam int unsigned DCACHE_TAG_WIDTH = riscv::PLEN - DCACHE_INDEX_WIDTH;
  localparam int unsigned DCACHE_USER_LINE_WIDTH = (AXI_USER_WIDTH == 1) ? 4 : 128;  // in bit
  localparam int unsigned DCACHE_USER_WIDTH = cva6_config_pkg::CVA6ConfigDataUserWidth;

  localparam int unsigned MEM_TID_WIDTH = `L15_THREADID_WIDTH;
`endif

  // ---------------
  // EX Stage
  // ---------------

  typedef enum logic [7:0] {  // basic ALU op
    ADD,
    SUB,
    ADDW,
    SUBW,
    // logic operations
    XORL,
    ORL,
    ANDL,
    // shifts
    SRA,
    SRL,
    SLL,
    SRLW,
    SLLW,
    SRAW,
    // comparisons
    LTS,
    LTU,
    GES,
    GEU,
    EQ,
    NE,
    // jumps
    JALR,
    BRANCH,
    // set lower than operations
    SLTS,
    SLTU,
    // CSR functions
    MRET,
    SRET,
    DRET,
    ECALL,
    WFI,
    FENCE,
    FENCE_I,
    SFENCE_VMA,
    HFENCE_VVMA,
    HFENCE_GVMA,
    CSR_WRITE,
    CSR_READ,
    CSR_SET,
    CSR_CLEAR,
    // LSU functions
    LD,
    SD,
    LW,
    LWU,
    SW,
    LH,
    LHU,
    SH,
    LB,
    SB,
    LBU,
    // Hypervisor Virtual-Machine Load and Store Instructions
    HLV_B,
    HLV_BU,
    HLV_H,
    HLV_HU,
    HLVX_HU,
    HLV_W,
    HLVX_WU,
    HSV_B,
    HSV_H,
    HSV_W,
    HLV_WU,
    HLV_D,
    HSV_D,
    // Atomic Memory Operations
    AMO_LRW,
    AMO_LRD,
    AMO_SCW,
    AMO_SCD,
    AMO_SWAPW,
    AMO_ADDW,
    AMO_ANDW,
    AMO_ORW,
    AMO_XORW,
    AMO_MAXW,
    AMO_MAXWU,
    AMO_MINW,
    AMO_MINWU,
    AMO_SWAPD,
    AMO_ADDD,
    AMO_ANDD,
    AMO_ORD,
    AMO_XORD,
    AMO_MAXD,
    AMO_MAXDU,
    AMO_MIND,
    AMO_MINDU,
    // Multiplications
    MUL,
    MULH,
    MULHU,
    MULHSU,
    MULW,
    // Divisions
    DIV,
    DIVU,
    DIVW,
    DIVUW,
    REM,
    REMU,
    REMW,
    REMUW,
    // Floating-Point Load and Store Instructions
    FLD,
    FLW,
    FLH,
    FLB,
    FSD,
    FSW,
    FSH,
    FSB,
    // Floating-Point Computational Instructions
    FADD,
    FSUB,
    FMUL,
    FDIV,
    FMIN_MAX,
    FSQRT,
    FMADD,
    FMSUB,
    FNMSUB,
    FNMADD,
    // Floating-Point Conversion and Move Instructions
    FCVT_F2I,
    FCVT_I2F,
    FCVT_F2F,
    FSGNJ,
    FMV_F2X,
    FMV_X2F,
    // Floating-Point Compare Instructions
    FCMP,
    // Floating-Point Classify Instruction
    FCLASS,
    // Vectorial Floating-Point Instructions that don't directly map onto the scalar ones
    VFMIN,
    VFMAX,
    VFSGNJ,
    VFSGNJN,
    VFSGNJX,
    VFEQ,
    VFNE,
    VFLT,
    VFGE,
    VFLE,
    VFGT,
    VFCPKAB_S,
    VFCPKCD_S,
    VFCPKAB_D,
    VFCPKCD_D,
    // Offload Instructions to be directed into cv_x_if
    OFFLOAD,
    // Or-Combine and REV8
    ORCB,
    REV8,
    // Bitwise Rotation
    ROL,
    ROLW,
    ROR,
    RORI,
    RORIW,
    RORW,
    // Sign and Zero Extend
    SEXTB,
    SEXTH,
    ZEXTH,
    // Count population
    CPOP,
    CPOPW,
    // Count Leading/Training Zeros
    CLZ,
    CLZW,
    CTZ,
    CTZW,
    // Carry less multiplication Op's
    CLMUL,
    CLMULH,
    CLMULR,
    // Single bit instructions Op's
    BCLR,
    BCLRI,
    BEXT,
    BEXTI,
    BINV,
    BINVI,
    BSET,
    BSETI,
    // Integer minimum/maximum
    MAX,
    MAXU,
    MIN,
    MINU,
    // Shift with Add Unsigned Word and Unsigned Word Op's (Bitmanip)
    SH1ADDUW,
    SH2ADDUW,
    SH3ADDUW,
    ADDUW,
    SLLIUW,
    // Shift with Add (Bitmanip)
    SH1ADD,
    SH2ADD,
    SH3ADD,
    // Bitmanip Logical with negate op (Bitmanip)
    ANDN,
    ORN,
    XNOR,
    // Accelerator operations
    ACCEL_OP,
    ACCEL_OP_FS1,
    ACCEL_OP_FD,
    ACCEL_OP_LOAD,
    ACCEL_OP_STORE,
    // Zicond instruction
    CZERO_EQZ,
    CZERO_NEZ,
    // Pack instructions
    PACK,
    PACK_H,
    PACK_W,
    // Brev8 instruction
    BREV8,
    // Zip instructions
    UNZIP,
    ZIP,
    // Xperm instructions
    XPERM8,
    XPERM4,
    // AES Encryption instructions
    AES32ESI,
    AES32ESMI,
    AES64ES,
    AES64ESM,
    // AES Decryption instructions
    AES32DSI,
    AES32DSMI,
    AES64DS,
    AES64DSM,
    AES64IM,
    // AES Key-Schedule instructions
    //AES64KS1I,
    AES64KS2
  } fu_op;

  function automatic logic op_is_branch(input fu_op op);
    unique case (op) inside
      EQ, NE, LTS, GES, LTU, GEU: return 1'b1;
      default:                    return 1'b0;  // all other ops
    endcase
  endfunction

  // -------------------------------
  // Extract Src/Dst FP Reg from Op
  // -------------------------------
  // function used in instr_trace svh
  // is_rs1_fpr function is kept to allow cva6 compilation with instr_trace feature
  function automatic logic is_rs1_fpr(input fu_op op);
    unique case (op) inside
      [FMUL : FNMADD],  // Computational Operations (except ADD/SUB)
      FCVT_F2I,  // Float-Int Casts
      FCVT_F2F,  // Float-Float Casts
      FSGNJ,  // Sign Injections
      FMV_F2X,  // FPR-GPR Moves
      FCMP,  // Comparisons
      FCLASS,  // Classifications
      [VFMIN : VFCPKCD_D],  // Additional Vectorial FP ops
      ACCEL_OP_FS1:
      return 1'b1;  // Accelerator instructions
      default: return 1'b0;  // all other ops
    endcase
  endfunction

  // function used in instr_trace svh
  // is_rs2_fpr function is kept to allow cva6 compilation with instr_trace feature
  function automatic logic is_rs2_fpr(input fu_op op);
    unique case (op) inside
      [FSD : FSB],  // FP Stores
      [FADD : FMIN_MAX],  // Computational Operations (no sqrt)
      [FMADD : FNMADD],  // Fused Computational Operations
      FCVT_F2F,  // Vectorial F2F Conversions requrie target
      [FSGNJ : FMV_F2X],  // Sign Injections and moves mapped to SGNJ
      FCMP,  // Comparisons
      [VFMIN : VFCPKCD_D]:
      return 1'b1;  // Additional Vectorial FP ops
      default: return 1'b0;  // all other ops
    endcase
  endfunction

  // function used in instr_trace svh
  // is_imm_fpr function is kept to allow cva6 compilation with instr_trace feature
  // ternary operations encode the rs3 address in the imm field, also add/sub
  function automatic logic is_imm_fpr(input fu_op op);
    unique case (op) inside
      [FADD : FSUB],  // ADD/SUB need inputs as Operand B/C
      [FMADD : FNMADD],  // Fused Computational Operations
      [VFCPKAB_S : VFCPKCD_D]:
      return 1'b1;  // Vectorial FP cast and pack ops
      default: return 1'b0;  // all other ops
    endcase
  endfunction

  // function used in instr_trace svh
  // is_rd_fpr function is kept to allow cva6 compilation with instr_trace feature
  function automatic logic is_rd_fpr(input fu_op op);
    unique case (op) inside
      [FLD : FLB],  // FP Loads
      [FADD : FNMADD],  // Computational Operations
      FCVT_I2F,  // Int-Float Casts
      FCVT_F2F,  // Float-Float Casts
      FSGNJ,  // Sign Injections
      FMV_X2F,  // GPR-FPR Moves
      [VFMIN : VFSGNJX],  // Vectorial MIN/MAX and SGNJ
      [VFCPKAB_S : VFCPKCD_D],  // Vectorial FP cast and pack ops
      ACCEL_OP_FD:
      return 1'b1;  // Accelerator instructions
      default: return 1'b0;  // all other ops
    endcase
  endfunction

  function automatic logic is_amo(fu_op op);
    case (op) inside
      [AMO_LRW : AMO_MINDU]: begin
        return 1'b1;
      end
      default: return 1'b0;
    endcase
  endfunction

  // -------------------
  // Performance counter
  // -------------------
  localparam int unsigned MHPMCounterNum = 6;

  // --------------------
  // Atomics
  // --------------------
  typedef enum logic [3:0] {
    AMO_NONE = 4'b0000,
    AMO_LR   = 4'b0001,
    AMO_SC   = 4'b0010,
    AMO_SWAP = 4'b0011,
    AMO_ADD  = 4'b0100,
    AMO_AND  = 4'b0101,
    AMO_OR   = 4'b0110,
    AMO_XOR  = 4'b0111,
    AMO_MAX  = 4'b1000,
    AMO_MAXU = 4'b1001,
    AMO_MIN  = 4'b1010,
    AMO_MINU = 4'b1011,
    AMO_CAS1 = 4'b1100,  // unused, not part of riscv spec, but provided in OpenPiton
    AMO_CAS2 = 4'b1101   // unused, not part of riscv spec, but provided in OpenPiton
  } amo_t;

  // Bits required for representation of physical address space as 4K pages
  // (e.g. 27*4K == 39bit address space).
  localparam PPN4K_WIDTH = 38;

  typedef struct packed {
    logic             valid;    // valid flag
    logic             is_4M;    //
    logic [20-1:0]    vpn;      //VPN (32bits) = 20bits + 12bits offset
    logic [9-1:0]     asid;     //ASID length = 9 for Sv32 mmu
    riscv::pte_sv32_t content;
  } tlb_update_sv32_t;

  typedef enum logic [1:0] {
    FE_NONE,
    FE_INSTR_ACCESS_FAULT,
    FE_INSTR_PAGE_FAULT,
    FE_INSTR_GUEST_PAGE_FAULT
  } frontend_exception_t;

  // AMO request going to cache. this request is unconditionally valid as soon
  // as request goes high.
  // Furthermore, those signals are kept stable until the response indicates
  // completion by asserting ack.
  typedef struct packed {
    logic        req;        // this request is valid
    amo_t        amo_op;     // atomic memory operation to perform
    logic [1:0]  size;       // 2'b10 --> word operation, 2'b11 --> double word operation
    logic [63:0] operand_a;  // address
    logic [63:0] operand_b;  // data as layouted in the register
  } amo_req_t;

  // AMO response coming from cache.
  typedef struct packed {
    logic        ack;     // response is valid
    logic [63:0] result;  // sign-extended, result
  } amo_resp_t;

  localparam RVFI = cva6_config_pkg::CVA6ConfigRvfiTrace;

  // ----------------------
  // Arithmetic Functions
  // ----------------------
  function automatic logic [63:0] sext32to64(logic [31:0] operand);
    return {{32{operand[31]}}, operand[31:0]};
  endfunction

  // ----------------------
  // LSU Functions
  // ----------------------
  // generate byte enable mask
  function automatic logic [7:0] be_gen(logic [2:0] addr, logic [1:0] size);
    case (size)
      2'b11: begin
        return 8'b1111_1111;
      end
      2'b10: begin
        case (addr[2:0])
          3'b000:  return 8'b0000_1111;
          3'b001:  return 8'b0001_1110;
          3'b010:  return 8'b0011_1100;
          3'b011:  return 8'b0111_1000;
          3'b100:  return 8'b1111_0000;
          default: ;  // Do nothing
        endcase
      end
      2'b01: begin
        case (addr[2:0])
          3'b000:  return 8'b0000_0011;
          3'b001:  return 8'b0000_0110;
          3'b010:  return 8'b0000_1100;
          3'b011:  return 8'b0001_1000;
          3'b100:  return 8'b0011_0000;
          3'b101:  return 8'b0110_0000;
          3'b110:  return 8'b1100_0000;
          default: ;  // Do nothing
        endcase
      end
      2'b00: begin
        case (addr[2:0])
          3'b000: return 8'b0000_0001;
          3'b001: return 8'b0000_0010;
          3'b010: return 8'b0000_0100;
          3'b011: return 8'b0000_1000;
          3'b100: return 8'b0001_0000;
          3'b101: return 8'b0010_0000;
          3'b110: return 8'b0100_0000;
          3'b111: return 8'b1000_0000;
        endcase
      end
    endcase
    return 8'b0;
  endfunction

  function automatic logic [3:0] be_gen_32(logic [1:0] addr, logic [1:0] size);
    case (size)
      2'b10: begin
        return 4'b1111;
      end
      2'b01: begin
        case (addr[1:0])
          2'b00:   return 4'b0011;
          2'b01:   return 4'b0110;
          2'b10:   return 4'b1100;
          default: ;  // Do nothing
        endcase
      end
      2'b00: begin
        case (addr[1:0])
          2'b00: return 4'b0001;
          2'b01: return 4'b0010;
          2'b10: return 4'b0100;
          2'b11: return 4'b1000;
        endcase
      end
      default: return 4'b0;
    endcase
    return 4'b0;
  endfunction

  // ----------------------
  // Extract Bytes from Op
  // ----------------------
  function automatic logic [1:0] extract_transfer_size(fu_op op);
    case (op)
      LD, HLV_D, SD, HSV_D, FLD, FSD,
            AMO_LRD,   AMO_SCD,
            AMO_SWAPD, AMO_ADDD,
            AMO_ANDD,  AMO_ORD,
            AMO_XORD,  AMO_MAXD,
            AMO_MAXDU, AMO_MIND,
            AMO_MINDU: begin
        return 2'b11;
      end
      LW, LWU, HLV_W, HLV_WU, HLVX_WU,
            SW, HSV_W, FLW, FSW,
            AMO_LRW,   AMO_SCW,
            AMO_SWAPW, AMO_ADDW,
            AMO_ANDW,  AMO_ORW,
            AMO_XORW,  AMO_MAXW,
            AMO_MAXWU, AMO_MINW,
            AMO_MINWU: begin
        return 2'b10;
      end
      LH, LHU, HLV_H, HLV_HU, HLVX_HU, SH, HSV_H, FLH, FSH: return 2'b01;
      LB, LBU, HLV_B, HLV_BU, SB, HSV_B, FLB, FSB:          return 2'b00;
      default:                                              return 2'b11;
    endcase
  endfunction
  // ----------------------
  // MMU Functions
  // ----------------------

  // checks if final translation page size is 1G when H-extension is enabled
  function automatic logic is_trans_1G(input logic s_st_enbl, input logic g_st_enbl,
                                       input logic is_s_1G, input logic is_g_1G);
    return (((is_s_1G && s_st_enbl) || !s_st_enbl) && ((is_g_1G && g_st_enbl) || !g_st_enbl));
  endfunction : is_trans_1G

  // checks if final translation page size is 2M when H-extension is enabled
  function automatic logic is_trans_2M(input logic s_st_enbl, input logic g_st_enbl,
                                       input logic is_s_1G, input logic is_s_2M,
                                       input logic is_g_1G, input logic is_g_2M);
    return  (s_st_enbl && g_st_enbl) ?
                ((is_s_2M && (is_g_1G || is_g_2M)) || (is_g_2M && (is_s_1G || is_s_2M))) :
                ((is_s_2M && s_st_enbl) || (is_g_2M && g_st_enbl));
  endfunction : is_trans_2M

  // computes the paddr based on the page size, ppn and offset
  function automatic logic [40:0] make_gpaddr(input logic s_st_enbl, input logic is_1G,
                                              input logic is_2M, input logic [63:0] vaddr,
                                              input riscv::pte_t pte);
    logic [40:0] gpaddr;
    if (s_st_enbl) begin
      gpaddr = {pte.ppn[28:0], vaddr[11:0]};
      // Giga page
      if (is_1G) gpaddr[29:12] = vaddr[29:12];
      // Mega page
      if (is_2M) gpaddr[20:12] = vaddr[20:12];
    end else begin
      gpaddr = vaddr[40:0];
    end
    return gpaddr;
  endfunction : make_gpaddr

  // computes the final gppn based on the guest physical address
  function automatic logic [28:0] make_gppn(input logic s_st_enbl, input logic is_1G,
                                            input logic is_2M, input logic [28:0] vpn,
                                            input riscv::pte_t pte);
    logic [28:0] gppn;
    if (s_st_enbl) begin
      gppn = pte.ppn[28:0];
      if (is_2M) gppn[8:0] = vpn[8:0];
      if (is_1G) gppn[17:0] = vpn[17:0];
    end else begin
      gppn = vpn;
    end
    return gppn;
  endfunction : make_gppn

  // ----------------------
  // Helper functions
  // ----------------------
  // Avoid negative array slices when defining parametrized sizes
  function automatic int unsigned avoid_neg(int n);
    return (n < 0) ? 0 : n;
  endfunction : avoid_neg

  // AES functions
  // AES MixColumns Forward
    function [31:0] aes_mixcolumn_fwd(input [31:0] x);
      begin        
        aes_mixcolumn_fwd = {(((x[7:0] << 1) ^ ((x[7]) ? 8'h1B : 8'h00)) ^ x[7:0]) ^ x[15:8] ^ x[23:16] ^ ((x[31:24] << 1) ^ ((x[31]) ? 8'h1B : 8'h00)),
                            x[7:0] ^ x[15:8] ^ ((x[23:16] << 1) ^ ((x[23]) ? 8'h1B : 8'h00)) ^ (((x[31:24] << 1) ^ ((x[31]) ? 8'h1B : 8'h00)) ^ x[31:24]),
                            x[7:0] ^ ((x[15:8] << 1) ^ ((x[15]) ? 8'h1B : 8'h00)) ^ (((x[23:16] << 1) ^ ((x[23]) ? 8'h1B : 8'h00)) ^ x[23:16]) ^ x[31:24],
                            ((x[7:0] << 1) ^ ((x[7]) ? 8'h1B : 8'h00)) ^ (((x[15:8] << 1) ^ ((x[15]) ? 8'h1B : 8'h00)) ^ x[15:8]) ^ x[23:16] ^ x[31:24]};
      end
    endfunction
  // AES subword Forward
    function [31:0] aes_subword_fwd(input [31:0] word);
        aes_subword_fwd = {aes_sbox_fwd(word[31:24]),
                           aes_sbox_fwd(word[23:16]),
                           aes_sbox_fwd(word[15:8]),
                           aes_sbox_fwd(word[7:0])};
    endfunction
  // AES Sbox Forward
    function [7:0] aes_sbox_fwd(input [7:0] si);
    case (si)
    8'h00: aes_sbox_fwd = 8'h63; 8'h01: aes_sbox_fwd = 8'h7C; 8'h02: aes_sbox_fwd = 8'h77; 8'h03: aes_sbox_fwd = 8'h7B; 8'h04: aes_sbox_fwd = 8'hF2; 8'h05: aes_sbox_fwd = 8'h6B;
    8'h06: aes_sbox_fwd = 8'h6F; 8'h07: aes_sbox_fwd = 8'hC5; 8'h08: aes_sbox_fwd = 8'h30; 8'h09: aes_sbox_fwd = 8'h01; 8'h0A: aes_sbox_fwd = 8'h67; 8'h0B: aes_sbox_fwd = 8'h2B;
    8'h0C: aes_sbox_fwd = 8'hFE; 8'h0D: aes_sbox_fwd = 8'hD7; 8'h0E: aes_sbox_fwd = 8'hAB; 8'h0F: aes_sbox_fwd = 8'h76; 8'h10: aes_sbox_fwd = 8'hCA; 8'h11: aes_sbox_fwd = 8'h82;
    8'h12: aes_sbox_fwd = 8'hC9; 8'h13: aes_sbox_fwd = 8'h7D; 8'h14: aes_sbox_fwd = 8'hFA; 8'h15: aes_sbox_fwd = 8'h59; 8'h16: aes_sbox_fwd = 8'h47; 8'h17: aes_sbox_fwd = 8'hF0;
    8'h18: aes_sbox_fwd = 8'hAD; 8'h19: aes_sbox_fwd = 8'hD4; 8'h1A: aes_sbox_fwd = 8'hA2; 8'h1B: aes_sbox_fwd = 8'hAF; 8'h1C: aes_sbox_fwd = 8'h9C; 8'h1D: aes_sbox_fwd = 8'hA4;
    8'h1E: aes_sbox_fwd = 8'h72; 8'h1F: aes_sbox_fwd = 8'hC0; 8'h20: aes_sbox_fwd = 8'hB7; 8'h21: aes_sbox_fwd = 8'hFD; 8'h22: aes_sbox_fwd = 8'h93; 8'h23: aes_sbox_fwd = 8'h26;
    8'h24: aes_sbox_fwd = 8'h36; 8'h25: aes_sbox_fwd = 8'h3F; 8'h26: aes_sbox_fwd = 8'hF7; 8'h27: aes_sbox_fwd = 8'hCC; 8'h28: aes_sbox_fwd = 8'h34; 8'h29: aes_sbox_fwd = 8'hA5;
    8'h2A: aes_sbox_fwd = 8'hE5; 8'h2B: aes_sbox_fwd = 8'hF1; 8'h2C: aes_sbox_fwd = 8'h71; 8'h2D: aes_sbox_fwd = 8'hD8; 8'h2E: aes_sbox_fwd = 8'h31; 8'h2F: aes_sbox_fwd = 8'h15;
    8'h30: aes_sbox_fwd = 8'h04; 8'h31: aes_sbox_fwd = 8'hC7; 8'h32: aes_sbox_fwd = 8'h23; 8'h33: aes_sbox_fwd = 8'hC3; 8'h34: aes_sbox_fwd = 8'h18; 8'h35: aes_sbox_fwd = 8'h96;
    8'h36: aes_sbox_fwd = 8'h05; 8'h37: aes_sbox_fwd = 8'h9A; 8'h38: aes_sbox_fwd = 8'h07; 8'h39: aes_sbox_fwd = 8'h12; 8'h3A: aes_sbox_fwd = 8'h80; 8'h3B: aes_sbox_fwd = 8'hE2;
    8'h3C: aes_sbox_fwd = 8'hEB; 8'h3D: aes_sbox_fwd = 8'h27; 8'h3E: aes_sbox_fwd = 8'hB2; 8'h3F: aes_sbox_fwd = 8'h75; 8'h40: aes_sbox_fwd = 8'h09; 8'h41: aes_sbox_fwd = 8'h83;
    8'h42: aes_sbox_fwd = 8'h2C; 8'h43: aes_sbox_fwd = 8'h1A; 8'h44: aes_sbox_fwd = 8'h1B; 8'h45: aes_sbox_fwd = 8'h6E; 8'h46: aes_sbox_fwd = 8'h5A; 8'h47: aes_sbox_fwd = 8'hA0;
    8'h48: aes_sbox_fwd = 8'h52; 8'h49: aes_sbox_fwd = 8'h3B; 8'h4A: aes_sbox_fwd = 8'hD6; 8'h4B: aes_sbox_fwd = 8'hB3; 8'h4C: aes_sbox_fwd = 8'h29; 8'h4D: aes_sbox_fwd = 8'hE3;
    8'h4E: aes_sbox_fwd = 8'h2F; 8'h4F: aes_sbox_fwd = 8'h84; 8'h50: aes_sbox_fwd = 8'h53; 8'h51: aes_sbox_fwd = 8'hD1; 8'h52: aes_sbox_fwd = 8'h00; 8'h53: aes_sbox_fwd = 8'hED;
    8'h54: aes_sbox_fwd = 8'h20; 8'h55: aes_sbox_fwd = 8'hFC; 8'h56: aes_sbox_fwd = 8'hB1; 8'h57: aes_sbox_fwd = 8'h5B; 8'h58: aes_sbox_fwd = 8'h6A; 8'h59: aes_sbox_fwd = 8'hCB;
    8'h5A: aes_sbox_fwd = 8'hBE; 8'h5B: aes_sbox_fwd = 8'h39; 8'h5C: aes_sbox_fwd = 8'h4A; 8'h5D: aes_sbox_fwd = 8'h4C; 8'h5E: aes_sbox_fwd = 8'h58; 8'h5F: aes_sbox_fwd = 8'hCF;
    8'h60: aes_sbox_fwd = 8'hD0; 8'h61: aes_sbox_fwd = 8'hEF; 8'h62: aes_sbox_fwd = 8'hAA; 8'h63: aes_sbox_fwd = 8'hFB; 8'h64: aes_sbox_fwd = 8'h43; 8'h65: aes_sbox_fwd = 8'h4D;
    8'h66: aes_sbox_fwd = 8'h33; 8'h67: aes_sbox_fwd = 8'h85; 8'h68: aes_sbox_fwd = 8'h45; 8'h69: aes_sbox_fwd = 8'hF9; 8'h6A: aes_sbox_fwd = 8'h02; 8'h6B: aes_sbox_fwd = 8'h7F;
    8'h6C: aes_sbox_fwd = 8'h50; 8'h6D: aes_sbox_fwd = 8'h3C; 8'h6E: aes_sbox_fwd = 8'h9F; 8'h6F: aes_sbox_fwd = 8'hA8; 8'h70: aes_sbox_fwd = 8'h51; 8'h71: aes_sbox_fwd = 8'hA3;
    8'h72: aes_sbox_fwd = 8'h40; 8'h73: aes_sbox_fwd = 8'h8F; 8'h74: aes_sbox_fwd = 8'h92; 8'h75: aes_sbox_fwd = 8'h9D; 8'h76: aes_sbox_fwd = 8'h38; 8'h77: aes_sbox_fwd = 8'hF5;
    8'h78: aes_sbox_fwd = 8'hBC; 8'h79: aes_sbox_fwd = 8'hB6; 8'h7A: aes_sbox_fwd = 8'hDA; 8'h7B: aes_sbox_fwd = 8'h21; 8'h7C: aes_sbox_fwd = 8'h10; 8'h7D: aes_sbox_fwd = 8'hFF;
    8'h7E: aes_sbox_fwd = 8'hF3; 8'h7F: aes_sbox_fwd = 8'hD2; 8'h80: aes_sbox_fwd = 8'hCD; 8'h81: aes_sbox_fwd = 8'h0C; 8'h82: aes_sbox_fwd = 8'h13; 8'h83: aes_sbox_fwd = 8'hEC;
    8'h84: aes_sbox_fwd = 8'h5F; 8'h85: aes_sbox_fwd = 8'h97; 8'h86: aes_sbox_fwd = 8'h44; 8'h87: aes_sbox_fwd = 8'h17; 8'h88: aes_sbox_fwd = 8'hC4; 8'h89: aes_sbox_fwd = 8'hA7;
    8'h8A: aes_sbox_fwd = 8'h7E; 8'h8B: aes_sbox_fwd = 8'h3D; 8'h8C: aes_sbox_fwd = 8'h64; 8'h8D: aes_sbox_fwd = 8'h5D; 8'h8E: aes_sbox_fwd = 8'h19; 8'h8F: aes_sbox_fwd = 8'h73;
    8'h90: aes_sbox_fwd = 8'h60; 8'h91: aes_sbox_fwd = 8'h81; 8'h92: aes_sbox_fwd = 8'h4F; 8'h93: aes_sbox_fwd = 8'hDC; 8'h94: aes_sbox_fwd = 8'h22; 8'h95: aes_sbox_fwd = 8'h2A;
    8'h96: aes_sbox_fwd = 8'h90; 8'h97: aes_sbox_fwd = 8'h88; 8'h98: aes_sbox_fwd = 8'h46; 8'h99: aes_sbox_fwd = 8'hEE; 8'h9A: aes_sbox_fwd = 8'hB8; 8'h9B: aes_sbox_fwd = 8'h14;
    8'h9C: aes_sbox_fwd = 8'hDE; 8'h9D: aes_sbox_fwd = 8'h5E; 8'h9E: aes_sbox_fwd = 8'h0B; 8'h9F: aes_sbox_fwd = 8'hDB; 8'hA0: aes_sbox_fwd = 8'hE0; 8'hA1: aes_sbox_fwd = 8'h32;
    8'hA2: aes_sbox_fwd = 8'h3A; 8'hA3: aes_sbox_fwd = 8'h0A; 8'hA4: aes_sbox_fwd = 8'h49; 8'hA5: aes_sbox_fwd = 8'h06; 8'hA6: aes_sbox_fwd = 8'h24; 8'hA7: aes_sbox_fwd = 8'h5C;
    8'hA8: aes_sbox_fwd = 8'hC2; 8'hA9: aes_sbox_fwd = 8'hD3; 8'hAA: aes_sbox_fwd = 8'hAC; 8'hAB: aes_sbox_fwd = 8'h62; 8'hAC: aes_sbox_fwd = 8'h91; 8'hAD: aes_sbox_fwd = 8'h95;
    8'hAE: aes_sbox_fwd = 8'hE4; 8'hAF: aes_sbox_fwd = 8'h79; 8'hB0: aes_sbox_fwd = 8'hE7; 8'hB1: aes_sbox_fwd = 8'hC8; 8'hB2: aes_sbox_fwd = 8'h37; 8'hB3: aes_sbox_fwd = 8'h6D;
    8'hB4: aes_sbox_fwd = 8'h8D; 8'hB5: aes_sbox_fwd = 8'hD5; 8'hB6: aes_sbox_fwd = 8'h4E; 8'hB7: aes_sbox_fwd = 8'hA9; 8'hB8: aes_sbox_fwd = 8'h6C; 8'hB9: aes_sbox_fwd = 8'h56;
    8'hBA: aes_sbox_fwd = 8'hF4; 8'hBB: aes_sbox_fwd = 8'hEA; 8'hBC: aes_sbox_fwd = 8'h65; 8'hBD: aes_sbox_fwd = 8'h7A; 8'hBE: aes_sbox_fwd = 8'hAE; 8'hBF: aes_sbox_fwd = 8'h08;
    8'hC0: aes_sbox_fwd = 8'hBA; 8'hC1: aes_sbox_fwd = 8'h78; 8'hC2: aes_sbox_fwd = 8'h25; 8'hC3: aes_sbox_fwd = 8'h2E; 8'hC4: aes_sbox_fwd = 8'h1C; 8'hC5: aes_sbox_fwd = 8'hA6;
    8'hC6: aes_sbox_fwd = 8'hB4; 8'hC7: aes_sbox_fwd = 8'hC6; 8'hC8: aes_sbox_fwd = 8'hE8; 8'hC9: aes_sbox_fwd = 8'hDD; 8'hCA: aes_sbox_fwd = 8'h74; 8'hCB: aes_sbox_fwd = 8'h1F;
    8'hCC: aes_sbox_fwd = 8'h4B; 8'hCD: aes_sbox_fwd = 8'hBD; 8'hCE: aes_sbox_fwd = 8'h8B; 8'hCF: aes_sbox_fwd = 8'h8A; 8'hD0: aes_sbox_fwd = 8'h70; 8'hD1: aes_sbox_fwd = 8'h3E;
    8'hD2: aes_sbox_fwd = 8'hB5; 8'hD3: aes_sbox_fwd = 8'h66; 8'hD4: aes_sbox_fwd = 8'h48; 8'hD5: aes_sbox_fwd = 8'h03; 8'hD6: aes_sbox_fwd = 8'hF6; 8'hD7: aes_sbox_fwd = 8'h0E;
    8'hD8: aes_sbox_fwd = 8'h61; 8'hD9: aes_sbox_fwd = 8'h35; 8'hDA: aes_sbox_fwd = 8'h57; 8'hDB: aes_sbox_fwd = 8'hB9; 8'hDC: aes_sbox_fwd = 8'h86; 8'hDD: aes_sbox_fwd = 8'hC1;
    8'hDE: aes_sbox_fwd = 8'h1D; 8'hDF: aes_sbox_fwd = 8'h9E; 8'hE0: aes_sbox_fwd = 8'hE1; 8'hE1: aes_sbox_fwd = 8'hF8; 8'hE2: aes_sbox_fwd = 8'h98; 8'hE3: aes_sbox_fwd = 8'h11;
    8'hE4: aes_sbox_fwd = 8'h69; 8'hE5: aes_sbox_fwd = 8'hD9; 8'hE6: aes_sbox_fwd = 8'h8E; 8'hE7: aes_sbox_fwd = 8'h94; 8'hE8: aes_sbox_fwd = 8'h9B; 8'hE9: aes_sbox_fwd = 8'h1E;
    8'hEA: aes_sbox_fwd = 8'h87; 8'hEB: aes_sbox_fwd = 8'hE9; 8'hEC: aes_sbox_fwd = 8'hCE; 8'hED: aes_sbox_fwd = 8'h55; 8'hEE: aes_sbox_fwd = 8'h28; 8'hEF: aes_sbox_fwd = 8'hDF; 8'hF0: aes_sbox_fwd = 8'h8C;
    8'hF1: aes_sbox_fwd = 8'hA1; 8'hF2: aes_sbox_fwd = 8'h89; 8'hF3: aes_sbox_fwd = 8'h0D; 8'hF4: aes_sbox_fwd = 8'hBF; 8'hF5: aes_sbox_fwd = 8'hE6; 8'hF6: aes_sbox_fwd = 8'h42;
    8'hF7: aes_sbox_fwd = 8'h68; 8'hF8: aes_sbox_fwd = 8'h41; 8'hF9: aes_sbox_fwd = 8'h99; 8'hFA: aes_sbox_fwd = 8'h2D; 8'hFB: aes_sbox_fwd = 8'h0F; 8'hFC: aes_sbox_fwd = 8'hB0;
    8'hFD: aes_sbox_fwd = 8'h54; 8'hFE: aes_sbox_fwd = 8'hBB; 8'hFF: aes_sbox_fwd = 8'h16;
    default: aes_sbox_fwd = 8'h00;
    endcase
    endfunction
  // AES Round Constant
    function [31:0] aes_decode_rcon(input [3:0] r);
        case (r)
            4'h0: aes_decode_rcon = 32'h00000001;
            4'h1: aes_decode_rcon = 32'h00000002;
            4'h2: aes_decode_rcon = 32'h00000004;
            4'h3: aes_decode_rcon = 32'h00000008;
            4'h4: aes_decode_rcon = 32'h00000010;
            4'h5: aes_decode_rcon = 32'h00000020;
            4'h6: aes_decode_rcon = 32'h00000040;
            4'h7: aes_decode_rcon = 32'h00000080;
            4'h8: aes_decode_rcon = 32'h0000001b;
            4'h9: aes_decode_rcon = 32'h00000036;
            4'hA: aes_decode_rcon = 32'h00000000;
            4'hB: aes_decode_rcon = 32'h00000000;
            4'hC: aes_decode_rcon = 32'h00000000;
            4'hD: aes_decode_rcon = 32'h00000000;
            4'hE: aes_decode_rcon = 32'h00000000;
            4'hF: aes_decode_rcon = 32'h00000000;
            default: aes_decode_rcon = 32'h00000000;
        endcase
    endfunction
  // AES Sbox Inverse
    function [7:0] aes_sbox_inv(input [7:0] si);
    case (si)
    8'h00: aes_sbox_inv = 8'h52; 8'h01: aes_sbox_inv = 8'h09; 8'h02: aes_sbox_inv = 8'h6a; 8'h03: aes_sbox_inv = 8'hd5; 8'h04: aes_sbox_inv = 8'h30; 8'h05: aes_sbox_inv = 8'h36;
    8'h06: aes_sbox_inv = 8'ha5; 8'h07: aes_sbox_inv = 8'h38; 8'h08: aes_sbox_inv = 8'hbf; 8'h09: aes_sbox_inv = 8'h40; 8'h0a: aes_sbox_inv = 8'ha3; 8'h0b: aes_sbox_inv = 8'h9e;
    8'h0c: aes_sbox_inv = 8'h81; 8'h0d: aes_sbox_inv = 8'hf3; 8'h0e: aes_sbox_inv = 8'hd7; 8'h0f: aes_sbox_inv = 8'hfb; 8'h10: aes_sbox_inv = 8'h7c; 8'h11: aes_sbox_inv = 8'he3;
    8'h12: aes_sbox_inv = 8'h39; 8'h13: aes_sbox_inv = 8'h82; 8'h14: aes_sbox_inv = 8'h9b; 8'h15: aes_sbox_inv = 8'h2f; 8'h16: aes_sbox_inv = 8'hff; 8'h17: aes_sbox_inv = 8'h87;
    8'h18: aes_sbox_inv = 8'h34; 8'h19: aes_sbox_inv = 8'h8e; 8'h1a: aes_sbox_inv = 8'h43; 8'h1b: aes_sbox_inv = 8'h44; 8'h1c: aes_sbox_inv = 8'hc4; 8'h1d: aes_sbox_inv = 8'hde;
    8'h1e: aes_sbox_inv = 8'he9; 8'h1f: aes_sbox_inv = 8'hcb; 8'h20: aes_sbox_inv = 8'h54; 8'h21: aes_sbox_inv = 8'h7b; 8'h22: aes_sbox_inv = 8'h94; 8'h23: aes_sbox_inv = 8'h32;
    8'h24: aes_sbox_inv = 8'ha6; 8'h25: aes_sbox_inv = 8'hc2; 8'h26: aes_sbox_inv = 8'h23; 8'h27: aes_sbox_inv = 8'h3d; 8'h28: aes_sbox_inv = 8'hee; 8'h29: aes_sbox_inv = 8'h4c;
    8'h2a: aes_sbox_inv = 8'h95; 8'h2b: aes_sbox_inv = 8'h0b; 8'h2c: aes_sbox_inv = 8'h42; 8'h2d: aes_sbox_inv = 8'hfa; 8'h2e: aes_sbox_inv = 8'hc3; 8'h2f: aes_sbox_inv = 8'h4e;
    8'h30: aes_sbox_inv = 8'h08; 8'h31: aes_sbox_inv = 8'h2e; 8'h32: aes_sbox_inv = 8'ha1; 8'h33: aes_sbox_inv = 8'h66; 8'h34: aes_sbox_inv = 8'h28; 8'h35: aes_sbox_inv = 8'hd9;
    8'h36: aes_sbox_inv = 8'h24; 8'h37: aes_sbox_inv = 8'hb2; 8'h38: aes_sbox_inv = 8'h76; 8'h39: aes_sbox_inv = 8'h5b; 8'h3a: aes_sbox_inv = 8'ha2; 8'h3b: aes_sbox_inv = 8'h49;
    8'h3c: aes_sbox_inv = 8'h6d; 8'h3d: aes_sbox_inv = 8'h8b; 8'h3e: aes_sbox_inv = 8'hd1; 8'h3f: aes_sbox_inv = 8'h25; 8'h40: aes_sbox_inv = 8'h72; 8'h41: aes_sbox_inv = 8'hf8;
    8'h42: aes_sbox_inv = 8'hf6; 8'h43: aes_sbox_inv = 8'h64; 8'h44: aes_sbox_inv = 8'h86; 8'h45: aes_sbox_inv = 8'h68; 8'h46: aes_sbox_inv = 8'h98; 8'h47: aes_sbox_inv = 8'h16;
    8'h48: aes_sbox_inv = 8'hd4; 8'h49: aes_sbox_inv = 8'ha4; 8'h4a: aes_sbox_inv = 8'h5c; 8'h4b: aes_sbox_inv = 8'hcc; 8'h4c: aes_sbox_inv = 8'h5d; 8'h4d: aes_sbox_inv = 8'h65;
    8'h4e: aes_sbox_inv = 8'hb6; 8'h4f: aes_sbox_inv = 8'h92; 8'h50: aes_sbox_inv = 8'h6c; 8'h51: aes_sbox_inv = 8'h70; 8'h52: aes_sbox_inv = 8'h48; 8'h53: aes_sbox_inv = 8'h50;
    8'h54: aes_sbox_inv = 8'hfd; 8'h55: aes_sbox_inv = 8'hed; 8'h56: aes_sbox_inv = 8'hb9; 8'h57: aes_sbox_inv = 8'hda; 8'h58: aes_sbox_inv = 8'h5e; 8'h59: aes_sbox_inv = 8'h15;
    8'h5a: aes_sbox_inv = 8'h46; 8'h5b: aes_sbox_inv = 8'h57; 8'h5c: aes_sbox_inv = 8'ha7; 8'h5d: aes_sbox_inv = 8'h8d; 8'h5e: aes_sbox_inv = 8'h9d; 8'h5f: aes_sbox_inv = 8'h84;
    8'h60: aes_sbox_inv = 8'h90; 8'h61: aes_sbox_inv = 8'hd8; 8'h62: aes_sbox_inv = 8'hab; 8'h63: aes_sbox_inv = 8'h00; 8'h64: aes_sbox_inv = 8'h8c; 8'h65: aes_sbox_inv = 8'hbc;
    8'h66: aes_sbox_inv = 8'hd3; 8'h67: aes_sbox_inv = 8'h0a; 8'h68: aes_sbox_inv = 8'hf7; 8'h69: aes_sbox_inv = 8'he4; 8'h6a: aes_sbox_inv = 8'h58; 8'h6b: aes_sbox_inv = 8'h05;
    8'h6c: aes_sbox_inv = 8'hb8; 8'h6d: aes_sbox_inv = 8'hb3; 8'h6e: aes_sbox_inv = 8'h45; 8'h6f: aes_sbox_inv = 8'h06; 8'h70: aes_sbox_inv = 8'hd0; 8'h71: aes_sbox_inv = 8'h2c;
    8'h72: aes_sbox_inv = 8'h1e; 8'h73: aes_sbox_inv = 8'h8f; 8'h74: aes_sbox_inv = 8'hca; 8'h75: aes_sbox_inv = 8'h3f; 8'h76: aes_sbox_inv = 8'h0f; 8'h77: aes_sbox_inv = 8'h02;
    8'h78: aes_sbox_inv = 8'hc1; 8'h79: aes_sbox_inv = 8'haf; 8'h7a: aes_sbox_inv = 8'hbd; 8'h7b: aes_sbox_inv = 8'h03; 8'h7c: aes_sbox_inv = 8'h01; 8'h7d: aes_sbox_inv = 8'h13;
    8'h7e: aes_sbox_inv = 8'h8a; 8'h7f: aes_sbox_inv = 8'h6b; 8'h80: aes_sbox_inv = 8'h3a; 8'h81: aes_sbox_inv = 8'h91; 8'h82: aes_sbox_inv = 8'h11; 8'h83: aes_sbox_inv = 8'h41;
    8'h84: aes_sbox_inv = 8'h4f; 8'h85: aes_sbox_inv = 8'h67; 8'h86: aes_sbox_inv = 8'hdc; 8'h87: aes_sbox_inv = 8'hea; 8'h88: aes_sbox_inv = 8'h97; 8'h89: aes_sbox_inv = 8'hf2;
    8'h8a: aes_sbox_inv = 8'hcf; 8'h8b: aes_sbox_inv = 8'hce; 8'h8c: aes_sbox_inv = 8'hf0; 8'h8d: aes_sbox_inv = 8'hb4; 8'h8e: aes_sbox_inv = 8'he6; 8'h8f: aes_sbox_inv = 8'h73;
    8'h90: aes_sbox_inv = 8'h96; 8'h91: aes_sbox_inv = 8'hac; 8'h92: aes_sbox_inv = 8'h74; 8'h93: aes_sbox_inv = 8'h22; 8'h94: aes_sbox_inv = 8'he7; 8'h95: aes_sbox_inv = 8'had; 8'h96: aes_sbox_inv = 8'h35; 8'h97: aes_sbox_inv = 8'h85;
    8'h98: aes_sbox_inv = 8'he2; 8'h99: aes_sbox_inv = 8'hf9; 8'h9a: aes_sbox_inv = 8'h37; 8'h9b: aes_sbox_inv = 8'he8; 8'h9c: aes_sbox_inv = 8'h1c; 8'h9d: aes_sbox_inv = 8'h75;
    8'h9e: aes_sbox_inv = 8'hdf; 8'h9f: aes_sbox_inv = 8'h6e; 8'ha0: aes_sbox_inv = 8'h47; 8'ha1: aes_sbox_inv = 8'hf1; 8'ha2: aes_sbox_inv = 8'h1a; 8'ha3: aes_sbox_inv = 8'h71;
    8'ha4: aes_sbox_inv = 8'h1d; 8'ha5: aes_sbox_inv = 8'h29; 8'ha6: aes_sbox_inv = 8'hc5; 8'ha7: aes_sbox_inv = 8'h89; 8'ha8: aes_sbox_inv = 8'h6f; 8'ha9: aes_sbox_inv = 8'hb7;
    8'haa: aes_sbox_inv = 8'h62; 8'hab: aes_sbox_inv = 8'h0e; 8'hac: aes_sbox_inv = 8'haa; 8'had: aes_sbox_inv = 8'h18; 8'hae: aes_sbox_inv = 8'hbe; 8'haf: aes_sbox_inv = 8'h1b;
    8'hb0: aes_sbox_inv = 8'hfc; 8'hb1: aes_sbox_inv = 8'h56; 8'hb2: aes_sbox_inv = 8'h3e; 8'hb3: aes_sbox_inv = 8'h4b; 8'hb4: aes_sbox_inv = 8'hc6; 8'hb5: aes_sbox_inv = 8'hd2;
    8'hb6: aes_sbox_inv = 8'h79; 8'hb7: aes_sbox_inv = 8'h20; 8'hb8: aes_sbox_inv = 8'h9a; 8'hb9: aes_sbox_inv = 8'hdb; 8'hba: aes_sbox_inv = 8'hc0; 8'hbb: aes_sbox_inv = 8'hfe;
    8'hbc: aes_sbox_inv = 8'h78; 8'hbd: aes_sbox_inv = 8'hcd; 8'hbe: aes_sbox_inv = 8'h5a; 8'hbf: aes_sbox_inv = 8'hf4; 8'hc0: aes_sbox_inv = 8'h1f; 8'hc1: aes_sbox_inv = 8'hdd;
    8'hc2: aes_sbox_inv = 8'ha8; 8'hc3: aes_sbox_inv = 8'h33; 8'hc4: aes_sbox_inv = 8'h88; 8'hc5: aes_sbox_inv = 8'h07; 8'hc6: aes_sbox_inv = 8'hc7; 8'hc7: aes_sbox_inv = 8'h31;
    8'hc8: aes_sbox_inv = 8'hb1; 8'hc9: aes_sbox_inv = 8'h12; 8'hca: aes_sbox_inv = 8'h10; 8'hcb: aes_sbox_inv = 8'h59; 8'hcc: aes_sbox_inv = 8'h27; 8'hcd: aes_sbox_inv = 8'h80;
    8'hce: aes_sbox_inv = 8'hec; 8'hcf: aes_sbox_inv = 8'h5f; 8'hd0: aes_sbox_inv = 8'h60; 8'hd1: aes_sbox_inv = 8'h51; 8'hd2: aes_sbox_inv = 8'h7f; 8'hd3: aes_sbox_inv = 8'ha9;
    8'hd4: aes_sbox_inv = 8'h19; 8'hd5: aes_sbox_inv = 8'hb5; 8'hd6: aes_sbox_inv = 8'h4a; 8'hd7: aes_sbox_inv = 8'h0d; 8'hd8: aes_sbox_inv = 8'h2d; 8'hd9: aes_sbox_inv = 8'he5;
    8'hda: aes_sbox_inv = 8'h7a; 8'hdb: aes_sbox_inv = 8'h9f; 8'hdc: aes_sbox_inv = 8'h93; 8'hdd: aes_sbox_inv = 8'hc9; 8'hde: aes_sbox_inv = 8'h9c; 8'hdf: aes_sbox_inv = 8'hef;
    8'he0: aes_sbox_inv = 8'ha0; 8'he1: aes_sbox_inv = 8'he0; 8'he2: aes_sbox_inv = 8'h3b; 8'he3: aes_sbox_inv = 8'h4d; 8'he4: aes_sbox_inv = 8'hae; 8'he5: aes_sbox_inv = 8'h2a;
    8'he6: aes_sbox_inv = 8'hf5; 8'he7: aes_sbox_inv = 8'hb0; 8'he8: aes_sbox_inv = 8'hc8; 8'he9: aes_sbox_inv = 8'heb; 8'hea: aes_sbox_inv = 8'hbb; 8'heb: aes_sbox_inv = 8'h3c;
    8'hec: aes_sbox_inv = 8'h83; 8'hed: aes_sbox_inv = 8'h53; 8'hee: aes_sbox_inv = 8'h99; 8'hef: aes_sbox_inv = 8'h61; 8'hf0: aes_sbox_inv = 8'h17; 8'hf1: aes_sbox_inv = 8'h2b;
    8'hf2: aes_sbox_inv = 8'h04; 8'hf3: aes_sbox_inv = 8'h7e; 8'hf4: aes_sbox_inv = 8'hba; 8'hf5: aes_sbox_inv = 8'h77; 8'hf6: aes_sbox_inv = 8'hd6; 8'hf7: aes_sbox_inv = 8'h26;
    8'hf8: aes_sbox_inv = 8'he1; 8'hf9: aes_sbox_inv = 8'h69; 8'hfa: aes_sbox_inv = 8'h14; 8'hfb: aes_sbox_inv = 8'h63; 8'hfc: aes_sbox_inv = 8'h55; 8'hfd: aes_sbox_inv = 8'h21;
    8'hfe: aes_sbox_inv = 8'h0c; 8'hff: aes_sbox_inv = 8'h7d;
    default: aes_sbox_inv = 8'h00;
    endcase
    endfunction
  // AES MixColumns Inverse
    function logic [31:0] aes_mixcolumn_inv(input logic [31:0] x);
        aes_mixcolumn_inv = {(gfmul(x[7:0], 4'hB) ^ gfmul(x[15:8], 4'hD) ^ gfmul(x[23:16], 4'h9) ^ gfmul(x[31:24], 4'hE)), 
                            (gfmul(x[7:0], 4'hD) ^ gfmul(x[15:8], 4'h9) ^ gfmul(x[23:16], 4'hE) ^ gfmul(x[31:24], 4'hB)), 
                            (gfmul(x[7:0], 4'h9) ^ gfmul(x[15:8], 4'hE) ^ gfmul(x[23:16], 4'hB) ^ gfmul(x[31:24], 4'hD)), 
                            (gfmul(x[7:0], 4'hE) ^ gfmul(x[15:8], 4'hB) ^ gfmul(x[23:16], 4'hD) ^ gfmul(x[31:24], 4'h9))};
    endfunction
  // GF multiplication
    function logic [7:0] gfmul(input logic [7:0] x, input logic [3:0] y);
    logic [7:0] result, temp;
    result = 8'h00;
    if (y[0]) result ^= x;
    if (y[1]) begin
        temp = (x << 1) ^ ((x[7]) ? 8'h1B : 8'h00);
        result ^= (x << 1) ^ ((x[7]) ? 8'h1B : 8'h00);
    end
    if (y[2]) begin
        temp = (x << 1) ^ ((x[7]) ? 8'h1B : 8'h00);
        temp = (temp << 1) ^ ((temp[7]) ? 8'h1B : 8'h00);
        result ^= temp;
    end
    if (y[3]) begin
        temp = (x << 1) ^ ((x[7]) ? 8'h1B : 8'h00);
        temp = (temp << 1) ^ ((temp[7]) ? 8'h1B : 8'h00);
        temp = (temp << 1) ^ ((temp[7]) ? 8'h1B : 8'h00);
        result ^= temp;
    end
    return result;
    endfunction
endpackage

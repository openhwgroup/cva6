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
 * File:   riscv_pkg.sv
 * Author: Florian Zaruba <zarubaf@iis.ee.ethz.ch>
 * Date:   30.6.2017
 *
 * Description: Common RISC-V definitions.
 */

package riscv;

    // ----------------------
    // Import cva6 config from cva6_config_pkg
    // ----------------------
    localparam XLEN = cva6_config_pkg::CVA6ConfigXlen;
    localparam FPU_EN = cva6_config_pkg::CVA6ConfigFpuEn;

    // ----------------------
    // Data and Address length
    // ----------------------
    typedef enum logic [3:0] {
       ModeOff  = 0,
       ModeSv32 = 1,
       ModeSv39 = 8,
       ModeSv48 = 9,
       ModeSv57 = 10,
       ModeSv64 = 11
    } vm_mode_t;

    // Warning: When using STD_CACHE, configuration must be PLEN=56 and VLEN=64
    // Warning: VLEN must be superior or equal to PLEN
    localparam VLEN             = (XLEN == 32) ? 32 : 64;    // virtual address length
    localparam PLEN             = (XLEN == 32) ? 34 : 56;    // physical address length

    localparam IS_XLEN32        = (XLEN == 32) ? 1'b1 : 1'b0;
    localparam IS_XLEN64        = (XLEN == 32) ? 1'b0 : 1'b1;
    localparam ModeW            = (XLEN == 32) ? 1 : 4;
    localparam ASIDW            = (XLEN == 32) ? 9 : 16;
    localparam PPNW             = (XLEN == 32) ? 22 : 44;
    localparam vm_mode_t        MODE_SV = (XLEN == 32) ? ModeSv32 : ModeSv39;
    localparam SV               = (MODE_SV == ModeSv32) ? 32 : 39;
    localparam VPN2             = (VLEN-31 < 8) ? VLEN-31 : 8;
    localparam XLEN_ALIGN_BYTES = $clog2(XLEN/8);

    typedef logic [XLEN-1:0] xlen_t;

    // --------------------
    // Privilege Spec
    // --------------------
    typedef enum logic[1:0] {
      PRIV_LVL_M = 2'b11,
      PRIV_LVL_S = 2'b01,
      PRIV_LVL_U = 2'b00
    } priv_lvl_t;

    // type which holds xlen
    typedef enum logic [1:0] {
        XLEN_32  = 2'b01,
        XLEN_64  = 2'b10,
        XLEN_128 = 2'b11
    } xlen_e;

    typedef enum logic [1:0] {
        Off     = 2'b00,
        Initial = 2'b01,
        Clean   = 2'b10,
        Dirty   = 2'b11
    } xs_t;

    typedef struct packed {
        logic         sd;     // signal dirty state - read-only
        logic [62:36] wpri4;  // writes preserved reads ignored
        xlen_e        sxl;    // variable supervisor mode xlen - hardwired to zero
        xlen_e        uxl;    // variable user mode xlen - hardwired to zero
        logic [8:0]   wpri3;  // writes preserved reads ignored
        logic         tsr;    // trap sret
        logic         tw;     // time wait
        logic         tvm;    // trap virtual memory
        logic         mxr;    // make executable readable
        logic         sum;    // permit supervisor user memory access
        logic         mprv;   // modify privilege - privilege level for ld/st
        xs_t          xs;     // extension register - hardwired to zero
        xs_t          fs;     // floating point extension register
        priv_lvl_t    mpp;    // holds the previous privilege mode up to machine
        logic [1:0]   wpri2;  // writes preserved reads ignored
        logic         spp;    // holds the previous privilege mode up to supervisor
        logic         mpie;   // machine interrupts enable bit active prior to trap
        logic         wpri1;  // writes preserved reads ignored
        logic         spie;   // supervisor interrupts enable bit active prior to trap
        logic         upie;   // user interrupts enable bit active prior to trap - hardwired to zero
        logic         mie;    // machine interrupts enable
        logic         wpri0;  // writes preserved reads ignored
        logic         sie;    // supervisor interrupts enable
        logic         uie;    // user interrupts enable - hardwired to zero
    } status_rv_t;

    typedef struct packed {
        logic [ModeW-1:0] mode;
        logic [ASIDW-1:0] asid;
        logic [PPNW-1:0]  ppn;
    } satp_t;

    // --------------------
    // Instruction Types
    // --------------------
    typedef struct packed {
        logic [31:25] funct7;
        logic [24:20] rs2;
        logic [19:15] rs1;
        logic [14:12] funct3;
        logic [11:7]  rd;
        logic [6:0]   opcode;
    } rtype_t;

    typedef struct packed {
        logic [31:27] rs3;
        logic [26:25] funct2;
        logic [24:20] rs2;
        logic [19:15] rs1;
        logic [14:12] funct3;
        logic [11:7]  rd;
        logic [6:0]   opcode;
    } r4type_t;

    typedef struct packed {
        logic [31:27] funct5;
        logic [26:25] fmt;
        logic [24:20] rs2;
        logic [19:15] rs1;
        logic [14:12] rm;
        logic [11:7]  rd;
        logic [6:0]   opcode;
    } rftype_t; // floating-point

    typedef struct packed {
        logic [31:30] funct2;
        logic [29:25] vecfltop;
        logic [24:20] rs2;
        logic [19:15] rs1;
        logic [14:14] repl;
        logic [13:12] vfmt;
        logic [11:7]  rd;
        logic [6:0]   opcode;
    } rvftype_t; // vectorial floating-point

    typedef struct packed {
        logic [31:20] imm;
        logic [19:15] rs1;
        logic [14:12] funct3;
        logic [11:7]  rd;
        logic [6:0]   opcode;
    } itype_t;

    typedef struct packed {
        logic [31:25] imm;
        logic [24:20] rs2;
        logic [19:15] rs1;
        logic [14:12] funct3;
        logic [11:7]  imm0;
        logic [6:0]   opcode;
    } stype_t;

    typedef struct packed {
        logic [31:12] imm;
        logic [11:7]  rd;
        logic [6:0]   opcode;
    } utype_t;

    // atomic instructions
    typedef struct packed {
        logic [31:27] funct5;
        logic         aq;
        logic         rl;
        logic [24:20] rs2;
        logic [19:15] rs1;
        logic [14:12] funct3;
        logic [11:7]  rd;
        logic [6:0]   opcode;
    } atype_t;

    typedef union packed {
        logic [31:0]   instr;
        rtype_t        rtype;
        r4type_t       r4type;
        rftype_t       rftype;
        rvftype_t      rvftype;
        itype_t        itype;
        stype_t        stype;
        utype_t        utype;
        atype_t        atype;
    } instruction_t;

    // --------------------
    // Opcodes
    // --------------------
    // RV32/64G listings:
    // Quadrant 0
    localparam OpcodeLoad      = 7'b00_000_11;
    localparam OpcodeLoadFp    = 7'b00_001_11;
    localparam OpcodeCustom0   = 7'b00_010_11;
    localparam OpcodeMiscMem   = 7'b00_011_11;
    localparam OpcodeOpImm     = 7'b00_100_11;
    localparam OpcodeAuipc     = 7'b00_101_11;
    localparam OpcodeOpImm32   = 7'b00_110_11;
    // Quadrant 1
    localparam OpcodeStore     = 7'b01_000_11;
    localparam OpcodeStoreFp   = 7'b01_001_11;
    localparam OpcodeCustom1   = 7'b01_010_11;
    localparam OpcodeAmo       = 7'b01_011_11;
    localparam OpcodeOp        = 7'b01_100_11;
    localparam OpcodeLui       = 7'b01_101_11;
    localparam OpcodeOp32      = 7'b01_110_11;
    // Quadrant 2
    localparam OpcodeMadd      = 7'b10_000_11;
    localparam OpcodeMsub      = 7'b10_001_11;
    localparam OpcodeNmsub     = 7'b10_010_11;
    localparam OpcodeNmadd     = 7'b10_011_11;
    localparam OpcodeOpFp      = 7'b10_100_11;
    localparam OpcodeRsrvd1    = 7'b10_101_11;
    localparam OpcodeCustom2   = 7'b10_110_11;
    // Quadrant 3
    localparam OpcodeBranch    = 7'b11_000_11;
    localparam OpcodeJalr      = 7'b11_001_11;
    localparam OpcodeRsrvd2    = 7'b11_010_11;
    localparam OpcodeJal       = 7'b11_011_11;
    localparam OpcodeSystem    = 7'b11_100_11;
    localparam OpcodeRsrvd3    = 7'b11_101_11;
    localparam OpcodeCustom3   = 7'b11_110_11;

    // RV64C/RV32C listings:
    // Quadrant 0
    localparam OpcodeC0             = 2'b00;
    localparam OpcodeC0Addi4spn     = 3'b000;
    localparam OpcodeC0Fld          = 3'b001;
    localparam OpcodeC0Lw           = 3'b010;
    localparam OpcodeC0Ld           = 3'b011;
    localparam OpcodeC0Rsrvd        = 3'b100;
    localparam OpcodeC0Fsd          = 3'b101;
    localparam OpcodeC0Sw           = 3'b110;
    localparam OpcodeC0Sd           = 3'b111;
    // Quadrant 1
    localparam OpcodeC1             = 2'b01;
    localparam OpcodeC1Addi         = 3'b000;
    localparam OpcodeC1Addiw        = 3'b001; //for RV64I only
    localparam OpcodeC1Jal          = 3'b001; //for RV32I only
    localparam OpcodeC1Li           = 3'b010;
    localparam OpcodeC1LuiAddi16sp  = 3'b011;
    localparam OpcodeC1MiscAlu      = 3'b100;
    localparam OpcodeC1J            = 3'b101;
    localparam OpcodeC1Beqz         = 3'b110;
    localparam OpcodeC1Bnez         = 3'b111;
    // Quadrant 2
    localparam OpcodeC2             = 2'b10;
    localparam OpcodeC2Slli         = 3'b000;
    localparam OpcodeC2Fldsp        = 3'b001;
    localparam OpcodeC2Lwsp         = 3'b010;
    localparam OpcodeC2Ldsp         = 3'b011;
    localparam OpcodeC2JalrMvAdd    = 3'b100;
    localparam OpcodeC2Fsdsp        = 3'b101;
    localparam OpcodeC2Swsp         = 3'b110;
    localparam OpcodeC2Sdsp         = 3'b111;

    // ----------------------
    // Virtual Memory
    // ----------------------
    // memory management, pte for sv39
    typedef struct packed {
        logic [9:0]  reserved;
        logic [44-1:0] ppn; // PPN length for
        logic [1:0]  rsw;
        logic d;
        logic a;
        logic g;
        logic u;
        logic x;
        logic w;
        logic r;
        logic v;
    } pte_t;

    // memory management, pte for sv32
    typedef struct packed {
        logic [22-1:0] ppn; // PPN length for
        logic [1:0]  rsw;
        logic d;
        logic a;
        logic g;
        logic u;
        logic x;
        logic w;
        logic r;
        logic v;
    } pte_sv32_t;

    // ----------------------
    // Exception Cause Codes
    // ----------------------
    localparam logic [XLEN-1:0] INSTR_ADDR_MISALIGNED = 0;
    localparam logic [XLEN-1:0] INSTR_ACCESS_FAULT    = 1;  // Illegal access as governed by PMPs and PMAs
    localparam logic [XLEN-1:0] ILLEGAL_INSTR         = 2;
    localparam logic [XLEN-1:0] BREAKPOINT            = 3;
    localparam logic [XLEN-1:0] LD_ADDR_MISALIGNED    = 4;
    localparam logic [XLEN-1:0] LD_ACCESS_FAULT       = 5;  // Illegal access as governed by PMPs and PMAs
    localparam logic [XLEN-1:0] ST_ADDR_MISALIGNED    = 6;
    localparam logic [XLEN-1:0] ST_ACCESS_FAULT       = 7;  // Illegal access as governed by PMPs and PMAs
    localparam logic [XLEN-1:0] ENV_CALL_UMODE        = 8;  // environment call from user mode
    localparam logic [XLEN-1:0] ENV_CALL_SMODE        = 9;  // environment call from supervisor mode
    localparam logic [XLEN-1:0] ENV_CALL_MMODE        = 11; // environment call from machine mode
    localparam logic [XLEN-1:0] INSTR_PAGE_FAULT      = 12; // Instruction page fault
    localparam logic [XLEN-1:0] LOAD_PAGE_FAULT       = 13; // Load page fault
    localparam logic [XLEN-1:0] STORE_PAGE_FAULT      = 15; // Store page fault
    localparam logic [XLEN-1:0] DEBUG_REQUEST         = 24; // Debug request

    localparam int unsigned IRQ_S_SOFT  = 1;
    localparam int unsigned IRQ_M_SOFT  = 3;
    localparam int unsigned IRQ_S_TIMER = 5;
    localparam int unsigned IRQ_M_TIMER = 7;
    localparam int unsigned IRQ_S_EXT   = 9;
    localparam int unsigned IRQ_M_EXT   = 11;

    localparam logic [XLEN-1:0] MIP_SSIP = 1 << IRQ_S_SOFT;
    localparam logic [XLEN-1:0] MIP_MSIP = 1 << IRQ_M_SOFT;
    localparam logic [XLEN-1:0] MIP_STIP = 1 << IRQ_S_TIMER;
    localparam logic [XLEN-1:0] MIP_MTIP = 1 << IRQ_M_TIMER;
    localparam logic [XLEN-1:0] MIP_SEIP = 1 << IRQ_S_EXT;
    localparam logic [XLEN-1:0] MIP_MEIP = 1 << IRQ_M_EXT;

    localparam logic [XLEN-1:0] S_SW_INTERRUPT    = (1 << (XLEN-1)) | IRQ_S_SOFT;
    localparam logic [XLEN-1:0] M_SW_INTERRUPT    = (1 << (XLEN-1)) | IRQ_M_SOFT;
    localparam logic [XLEN-1:0] S_TIMER_INTERRUPT = (1 << (XLEN-1)) | IRQ_S_TIMER;
    localparam logic [XLEN-1:0] M_TIMER_INTERRUPT = (1 << (XLEN-1)) | IRQ_M_TIMER;
    localparam logic [XLEN-1:0] S_EXT_INTERRUPT   = (1 << (XLEN-1)) | IRQ_S_EXT;
    localparam logic [XLEN-1:0] M_EXT_INTERRUPT   = (1 << (XLEN-1)) | IRQ_M_EXT;

    // -----
    // CSRs
    // -----
    typedef enum logic [11:0] {
        // Floating-Point CSRs
        CSR_FFLAGS         = 12'h001,
        CSR_FRM            = 12'h002,
        CSR_FCSR           = 12'h003,
        CSR_FTRAN          = 12'h800,
        // Supervisor Mode CSRs
        CSR_SSTATUS        = 12'h100,
        CSR_SIE            = 12'h104,
        CSR_STVEC          = 12'h105,
        CSR_SCOUNTEREN     = 12'h106,
        CSR_SSCRATCH       = 12'h140,
        CSR_SEPC           = 12'h141,
        CSR_SCAUSE         = 12'h142,
        CSR_STVAL          = 12'h143,
        CSR_SIP            = 12'h144,
        CSR_SATP           = 12'h180,
        // Machine Mode CSRs
        CSR_MSTATUS        = 12'h300,
        CSR_MISA           = 12'h301,
        CSR_MEDELEG        = 12'h302,
        CSR_MIDELEG        = 12'h303,
        CSR_MIE            = 12'h304,
        CSR_MTVEC          = 12'h305,
        CSR_MCOUNTEREN     = 12'h306,
        CSR_MHPM_EVENT_3   = 12'h323,  //Machine performance monitoring Event Selector
        CSR_MHPM_EVENT_4   = 12'h324,  //Machine performance monitoring Event Selector
        CSR_MHPM_EVENT_5   = 12'h325,  //Machine performance monitoring Event Selector
        CSR_MHPM_EVENT_6   = 12'h326,  //Machine performance monitoring Event Selector
        CSR_MHPM_EVENT_7   = 12'h327,  //Machine performance monitoring Event Selector
        CSR_MHPM_EVENT_8   = 12'h328,  //Machine performance monitoring Event Selector
        CSR_MSCRATCH       = 12'h340,
        CSR_MEPC           = 12'h341,
        CSR_MCAUSE         = 12'h342,
        CSR_MTVAL          = 12'h343,
        CSR_MIP            = 12'h344,
        CSR_PMPCFG0        = 12'h3A0,
        CSR_PMPCFG1        = 12'h3A1,
        CSR_PMPCFG2        = 12'h3A2,
        CSR_PMPCFG3        = 12'h3A3,
        CSR_PMPADDR0       = 12'h3B0,
        CSR_PMPADDR1       = 12'h3B1,
        CSR_PMPADDR2       = 12'h3B2,
        CSR_PMPADDR3       = 12'h3B3,
        CSR_PMPADDR4       = 12'h3B4,
        CSR_PMPADDR5       = 12'h3B5,
        CSR_PMPADDR6       = 12'h3B6,
        CSR_PMPADDR7       = 12'h3B7,
        CSR_PMPADDR8       = 12'h3B8,
        CSR_PMPADDR9       = 12'h3B9,
        CSR_PMPADDR10      = 12'h3BA,
        CSR_PMPADDR11      = 12'h3BB,
        CSR_PMPADDR12      = 12'h3BC,
        CSR_PMPADDR13      = 12'h3BD,
        CSR_PMPADDR14      = 12'h3BE,
        CSR_PMPADDR15      = 12'h3BF,
        CSR_MVENDORID      = 12'hF11,
        CSR_MARCHID        = 12'hF12,
        CSR_MIMPID         = 12'hF13,
        CSR_MHARTID        = 12'hF14,
        CSR_MCYCLE         = 12'hB00,
        CSR_MCYCLEH        = 12'hB80,
        CSR_MINSTRET       = 12'hB02,
        CSR_MINSTRETH      = 12'hB82,
        //Performance Counters
        CSR_MHPM_COUNTER_3 = 12'hB03,
        CSR_MHPM_COUNTER_4 = 12'hB04,
        CSR_MHPM_COUNTER_5 = 12'hB05,
        CSR_MHPM_COUNTER_6 = 12'hB06,
        CSR_MHPM_COUNTER_7 = 12'hB07, 
        CSR_MHPM_COUNTER_8 = 12'hB08, 
        CSR_MHPM_COUNTER_9 = 12'hB09,   // reserved
        CSR_MHPM_COUNTER_10 = 12'hB0A,  // reserved
        CSR_MHPM_COUNTER_11 = 12'hB0B,  // reserved
        CSR_MHPM_COUNTER_12 = 12'hB0C,  // reserved
        CSR_MHPM_COUNTER_13 = 12'hB0D,  // reserved
        CSR_MHPM_COUNTER_14 = 12'hB0E,  // reserved
        CSR_MHPM_COUNTER_15 = 12'hB0F,  // reserved
        CSR_MHPM_COUNTER_16 = 12'hB10,  // reserved
        CSR_MHPM_COUNTER_17 = 12'hB11,  // reserved
        CSR_MHPM_COUNTER_18 = 12'hB12,  // reserved
        CSR_MHPM_COUNTER_19 = 12'hB13,  // reserved
        CSR_MHPM_COUNTER_20 = 12'hB14,  // reserved
        CSR_MHPM_COUNTER_21 = 12'hB15,  // reserved
        CSR_MHPM_COUNTER_22 = 12'hB16,  // reserved
        CSR_MHPM_COUNTER_23 = 12'hB17,  // reserved
        CSR_MHPM_COUNTER_24 = 12'hB18,  // reserved
        CSR_MHPM_COUNTER_25 = 12'hB19,  // reserved
        CSR_MHPM_COUNTER_26 = 12'hB1A,  // reserved
        CSR_MHPM_COUNTER_27 = 12'hB1B,  // reserved
        CSR_MHPM_COUNTER_28 = 12'hB1C,  // reserved
        CSR_MHPM_COUNTER_29 = 12'hB1D,  // reserved
        CSR_MHPM_COUNTER_30 = 12'hB1E,  // reserved
        CSR_MHPM_COUNTER_31 = 12'hB1F,  // reserved        
        CSR_MHPM_COUNTER_3H = 12'hB83,  
        CSR_MHPM_COUNTER_4H = 12'hB84,  
        CSR_MHPM_COUNTER_5H = 12'hB85,  
        CSR_MHPM_COUNTER_6H = 12'hB86, 
        CSR_MHPM_COUNTER_7H = 12'hB87,
        CSR_MHPM_COUNTER_8H = 12'hB88,
        CSR_MHPM_COUNTER_9H = 12'hB89,   // reserved
        CSR_MHPM_COUNTER_10H = 12'hB8A,  // reserved
        CSR_MHPM_COUNTER_11H = 12'hB8B,  // reserved
        CSR_MHPM_COUNTER_12H = 12'hB8C,  // reserved
        CSR_MHPM_COUNTER_13H = 12'hB8D,  // reserved
        CSR_MHPM_COUNTER_14H = 12'hB8E,  // reserved
        CSR_MHPM_COUNTER_15H = 12'hB8F,  // reserved
        CSR_MHPM_COUNTER_16H = 12'hB90,  // reserved
        CSR_MHPM_COUNTER_17H = 12'hB91,  // reserved
        CSR_MHPM_COUNTER_18H = 12'hB92,  // reserved
        CSR_MHPM_COUNTER_19H = 12'hB93,  // reserved
        CSR_MHPM_COUNTER_20H = 12'hB94,  // reserved
        CSR_MHPM_COUNTER_21H = 12'hB95,  // reserved
        CSR_MHPM_COUNTER_22H = 12'hB96,  // reserved
        CSR_MHPM_COUNTER_23H = 12'hB97,  // reserved
        CSR_MHPM_COUNTER_24H = 12'hB98,  // reserved
        CSR_MHPM_COUNTER_25H = 12'hB99,  // reserved
        CSR_MHPM_COUNTER_26H = 12'hB9A,  // reserved
        CSR_MHPM_COUNTER_27H = 12'hB9B,  // reserved
        CSR_MHPM_COUNTER_28H = 12'hB9C,  // reserved
        CSR_MHPM_COUNTER_29H = 12'hB9D,  // reserved
        CSR_MHPM_COUNTER_30H = 12'hB9E,  // reserved
        CSR_MHPM_COUNTER_31H = 12'hB9F,  // reserved
        // Cache Control (platform specifc)
        CSR_DCACHE         = 12'h701,
        CSR_ICACHE         = 12'h700,
        // Triggers
        CSR_TSELECT        = 12'h7A0,
        CSR_TDATA1         = 12'h7A1,
        CSR_TDATA2         = 12'h7A2,
        CSR_TDATA3         = 12'h7A3,
        CSR_TINFO          = 12'h7A4,
        // Debug CSR
        CSR_DCSR           = 12'h7b0,
        CSR_DPC            = 12'h7b1,
        CSR_DSCRATCH0      = 12'h7b2, // optional
        CSR_DSCRATCH1      = 12'h7b3, // optional
        // Counters and Timers (User Mode - R/O Shadows)
        CSR_CYCLE          = 12'hC00,
        CSR_CYCLEH         = 12'hC80,
        CSR_TIME           = 12'hC01,
        CSR_TIMEH          = 12'hC81,
        CSR_INSTRET        = 12'hC02,
        CSR_INSTRETH       = 12'hC82,
        // Performance counters (User Mode - R/O Shadows)
        CSR_L1_ICACHE_MISS = 12'hC03,  // L1 Instr Cache Miss
        CSR_L1_DCACHE_MISS = 12'hC04,  // L1 Data Cache Miss
        CSR_ITLB_MISS      = 12'hC05,  // ITLB Miss
        CSR_DTLB_MISS      = 12'hC06,  // DTLB Miss
        CSR_LOAD           = 12'hC07,  // Loads
        CSR_STORE          = 12'hC08,  // Stores
        CSR_EXCEPTION      = 12'hC09,  // Taken exceptions
        CSR_EXCEPTION_RET  = 12'hC0A,  // Exception return
        CSR_BRANCH_JUMP    = 12'hC0B,  // Software change of PC
        CSR_CALL           = 12'hC0C,  // Procedure call
        CSR_RET            = 12'hC0D,  // Procedure Return
        CSR_MIS_PREDICT    = 12'hC0E,  // Branch mis-predicted
        CSR_SB_FULL        = 12'hC0F,  // Scoreboard full
        CSR_IF_EMPTY       = 12'hC10,  // instruction fetch queue empty
        CSR_HPM_COUNTER_17 = 12'hC11,  // reserved
        CSR_HPM_COUNTER_18 = 12'hC12,  // reserved
        CSR_HPM_COUNTER_19 = 12'hC13,  // reserved
        CSR_HPM_COUNTER_20 = 12'hC14,  // reserved
        CSR_HPM_COUNTER_21 = 12'hC15,  // reserved
        CSR_HPM_COUNTER_22 = 12'hC16,  // reserved
        CSR_HPM_COUNTER_23 = 12'hC17,  // reserved
        CSR_HPM_COUNTER_24 = 12'hC18,  // reserved
        CSR_HPM_COUNTER_25 = 12'hC19,  // reserved
        CSR_HPM_COUNTER_26 = 12'hC1A,  // reserved
        CSR_HPM_COUNTER_27 = 12'hC1B,  // reserved
        CSR_HPM_COUNTER_28 = 12'hC1C,  // reserved
        CSR_HPM_COUNTER_29 = 12'hC1D,  // reserved
        CSR_HPM_COUNTER_30 = 12'hC1E,  // reserved
        CSR_HPM_COUNTER_31 = 12'hC1F  // reserved
    } csr_reg_t;

    localparam logic [63:0] SSTATUS_UIE  = 'h00000001;
    localparam logic [63:0] SSTATUS_SIE  = 'h00000002;
    localparam logic [63:0] SSTATUS_SPIE = 'h00000020;
    localparam logic [63:0] SSTATUS_SPP  = 'h00000100;
    localparam logic [63:0] SSTATUS_FS   = 'h00006000;
    localparam logic [63:0] SSTATUS_XS   = 'h00018000;
    localparam logic [63:0] SSTATUS_SUM  = 'h00040000;
    localparam logic [63:0] SSTATUS_MXR  = 'h00080000;
    localparam logic [63:0] SSTATUS_UPIE = 'h00000010;
    localparam logic [63:0] SSTATUS_UXL  = 64'h0000000300000000;
    localparam logic [63:0] SSTATUS_SD   = {IS_XLEN64, 31'h00000000, ~IS_XLEN64, 31'h00000000};

    localparam logic [63:0] MSTATUS_UIE  = 'h00000001;
    localparam logic [63:0] MSTATUS_SIE  = 'h00000002;
    localparam logic [63:0] MSTATUS_HIE  = 'h00000004;
    localparam logic [63:0] MSTATUS_MIE  = 'h00000008;
    localparam logic [63:0] MSTATUS_UPIE = 'h00000010;
    localparam logic [63:0] MSTATUS_SPIE = 'h00000020;
    localparam logic [63:0] MSTATUS_HPIE = 'h00000040;
    localparam logic [63:0] MSTATUS_MPIE = 'h00000080;
    localparam logic [63:0] MSTATUS_SPP  = 'h00000100;
    localparam logic [63:0] MSTATUS_HPP  = 'h00000600;
    localparam logic [63:0] MSTATUS_MPP  = 'h00001800;
    localparam logic [63:0] MSTATUS_FS   = 'h00006000;
    localparam logic [63:0] MSTATUS_XS   = 'h00018000;
    localparam logic [63:0] MSTATUS_MPRV = 'h00020000;
    localparam logic [63:0] MSTATUS_SUM  = 'h00040000;
    localparam logic [63:0] MSTATUS_MXR  = 'h00080000;
    localparam logic [63:0] MSTATUS_TVM  = 'h00100000;
    localparam logic [63:0] MSTATUS_TW   = 'h00200000;
    localparam logic [63:0] MSTATUS_TSR  = 'h00400000;
    localparam logic [63:0] MSTATUS_UXL  = {30'h0000000, IS_XLEN64, IS_XLEN64, 32'h00000000};
    localparam logic [63:0] MSTATUS_SXL  = {28'h0000000, IS_XLEN64, IS_XLEN64, 34'h00000000};
    localparam logic [63:0] MSTATUS_SD   = {IS_XLEN64, 31'h00000000, ~IS_XLEN64, 31'h00000000};

    typedef enum logic [2:0] {
        CSRRW  = 3'h1,
        CSRRS  = 3'h2,
        CSRRC  = 3'h3,
        CSRRWI = 3'h5,
        CSRRSI = 3'h6,
        CSRRCI = 3'h7
    } csr_op_t;

    // decoded CSR address
    typedef struct packed {
        logic [1:0]  rw;
        priv_lvl_t   priv_lvl;
        logic  [7:0] address;
    } csr_addr_t;

    typedef union packed {
        csr_reg_t   address;
        csr_addr_t  csr_decode;
    } csr_t;

    // Floating-Point control and status register (32-bit!)
    typedef struct packed {
        logic [31:15] reserved;  // reserved for L extension, return 0 otherwise
        logic [6:0]   fprec;     // div/sqrt precision control
        logic [2:0]   frm;       // float rounding mode
        logic [4:0]   fflags;    // float exception flags
    } fcsr_t;

    // PMP
    typedef enum logic [1:0] {
        OFF   = 2'b00,
        TOR   = 2'b01,
        NA4   = 2'b10,
        NAPOT = 2'b11
    } pmp_addr_mode_t;

    // PMP Access Type
    typedef enum logic [2:0] {
        ACCESS_NONE  = 3'b000,
        ACCESS_READ  = 3'b001,
        ACCESS_WRITE = 3'b010,
        ACCESS_EXEC  = 3'b100
    } pmp_access_t;

    typedef struct packed {
        logic           x;
        logic           w;
        logic           r;
    } pmpcfg_access_t;

    // packed struct of a PMP configuration register (8bit)
    typedef struct packed {
        logic           locked;     // lock this configuration
        logic [1:0]     reserved;
        pmp_addr_mode_t addr_mode;  // Off, TOR, NA4, NAPOT
        pmpcfg_access_t access_type;
    } pmpcfg_t;

    // -----
    // Debug
    // -----
    typedef struct packed {
        logic [31:28]     xdebugver;
        logic [27:16]     zero2;
        logic             ebreakm;
        logic             zero1;
        logic             ebreaks;
        logic             ebreaku;
        logic             stepie;
        logic             stopcount;
        logic             stoptime;
        logic [8:6]       cause;
        logic             zero0;
        logic             mprven;
        logic             nmip;
        logic             step;
        priv_lvl_t        prv;
    } dcsr_t;

    // Instruction Generation *incomplete*
    function automatic logic [31:0] jal (logic[4:0] rd, logic [20:0] imm);
        // OpCode Jal
        return {imm[20], imm[10:1], imm[11], imm[19:12], rd, 7'h6f};
    endfunction

    function automatic logic [31:0] jalr (logic[4:0] rd, logic[4:0] rs1, logic [11:0] offset);
        // OpCode Jal
        return {offset[11:0], rs1, 3'b0, rd, 7'h67};
    endfunction

    function automatic logic [31:0] andi (logic[4:0] rd, logic[4:0] rs1, logic [11:0] imm);
        // OpCode andi
        return {imm[11:0], rs1, 3'h7, rd, 7'h13};
    endfunction

    function automatic logic [31:0] slli (logic[4:0] rd, logic[4:0] rs1, logic [5:0] shamt);
        // OpCode slli
        return {6'b0, shamt[5:0], rs1, 3'h1, rd, 7'h13};
    endfunction

    function automatic logic [31:0] srli (logic[4:0] rd, logic[4:0] rs1, logic [5:0] shamt);
        // OpCode srli
        return {6'b0, shamt[5:0], rs1, 3'h5, rd, 7'h13};
    endfunction

    function automatic logic [31:0] load (logic [2:0] size, logic[4:0] dest, logic[4:0] base, logic [11:0] offset);
        // OpCode Load
        return {offset[11:0], base, size, dest, 7'h03};
    endfunction

    function automatic logic [31:0] auipc (logic[4:0] rd, logic [20:0] imm);
        // OpCode Auipc
        return {imm[20], imm[10:1], imm[11], imm[19:12], rd, 7'h17};
    endfunction

    function automatic logic [31:0] store (logic [2:0] size, logic[4:0] src, logic[4:0] base, logic [11:0] offset);
        // OpCode Store
        return {offset[11:5], src, base, size, offset[4:0], 7'h23};
    endfunction

    function automatic logic [31:0] float_load (logic [2:0] size, logic[4:0] dest, logic[4:0] base, logic [11:0] offset);
        // OpCode Load
        return {offset[11:0], base, size, dest, 7'b00_001_11};
    endfunction

    function automatic logic [31:0] float_store (logic [2:0] size, logic[4:0] src, logic[4:0] base, logic [11:0] offset);
        // OpCode Store
        return {offset[11:5], src, base, size, offset[4:0], 7'b01_001_11};
    endfunction

    function automatic logic [31:0] csrw (csr_reg_t csr, logic[4:0] rs1);
                         // CSRRW, rd, OpCode System
        return {csr, rs1, 3'h1, 5'h0, 7'h73};
    endfunction

    function automatic logic [31:0] csrr (csr_reg_t csr, logic [4:0] dest);
                  // rs1, CSRRS, rd, OpCode System
        return {csr, 5'h0, 3'h2, dest, 7'h73};
    endfunction

    function automatic logic [31:0] branch(logic [4:0] src2, logic [4:0] src1, logic [2:0] funct3, logic [11:0] offset);
        // OpCode Branch
        return {offset[11], offset[9:4], src2, src1, funct3, offset[3:0], offset[10], 7'b11_000_11};
    endfunction

    function automatic logic [31:0] ebreak ();
        return 32'h00100073;
    endfunction

    function automatic logic [31:0] wfi ();
        return 32'h10500073;
    endfunction

    function automatic logic [31:0] nop ();
        return 32'h00000013;
    endfunction

    function automatic logic [31:0] illegal ();
        return 32'h00000000;
    endfunction


    // trace log compatible to spikes commit log feature
    // pragma translate_off
    function string spikeCommitLog(logic [63:0] pc, priv_lvl_t priv_lvl, logic [31:0] instr, logic [4:0] rd, logic [63:0] result, logic rd_fpr);
        string rd_s;
        string instr_word;

        automatic string rf_s = rd_fpr ? "f" : "x";

        if (instr[1:0] != 2'b11) begin
          instr_word = $sformatf("(0x%h)", instr[15:0]);
        end else begin
          instr_word = $sformatf("(0x%h)", instr);
        end

        if (rd < 10) rd_s = $sformatf("%s %0d", rf_s, rd);
        else rd_s = $sformatf("%s%0d", rf_s, rd);

        if (rd_fpr || rd != 0) begin
            // 0 0x0000000080000118 (0xeecf8f93) x31 0x0000000080004000
            return $sformatf("%d 0x%h %s %s 0x%h\n", priv_lvl, pc, instr_word, rd_s, result);
        end else begin
            // 0 0x000000008000019c (0x0040006f)
            return $sformatf("%d 0x%h %s\n", priv_lvl, pc, instr_word);
        end
    endfunction

    typedef struct {
        byte priv;
        longint unsigned pc;
        byte is_fp;
        byte rd;
        longint unsigned data;
        int unsigned instr;
        byte was_exception;
    } commit_log_t;
    // pragma translate_on

endpackage

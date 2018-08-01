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
    } xlen_t;

    typedef struct packed {
        logic         sd;     // signal dirty - read-only - hardwired zero
        logic [62:36] wpri4;  // writes preserved reads ignored
        xlen_t        sxl;    // variable supervisor mode xlen - hardwired to zero
        xlen_t        uxl;    // variable user mode xlen - hardwired to zero
        logic [8:0]   wpri3;  // writes preserved reads ignored
        logic         tsr;    // trap sret
        logic         tw;     // time wait
        logic         tvm;    // trap virtual memory
        logic         mxr;    // make executable readable
        logic         sum;    // permit supervisor user memory access
        logic         mprv;   // modify privilege - privilege level for ld/st
        logic [1:0]   xs;     // extension register - hardwired to zero
        logic [1:0]   fs;     // extension register - hardwired to zero
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
    } status_rv64_t;

    typedef struct packed {
        logic         sd;     // signal dirty - read-only - hardwired zero
        logic [7:0]   wpri3;  // writes preserved reads ignored
        logic         tsr;    // trap sret
        logic         tw;     // time wait
        logic         tvm;    // trap virtual memory
        logic         mxr;    // make executable readable
        logic         sum;    // permit supervisor user memory access
        logic         mprv;   // modify privilege - privilege level for ld/st
        logic [1:0]   xs;     // extension register - hardwired to zero
        logic [1:0]   fs;     // extension register - hardwired to zero
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
    } status_rv32_t;

    typedef struct packed {
        logic [3:0]  mode;
        logic [15:0] asid;
        logic [43:0] ppn;
    } satp_t;

    // read mask for SSTATUS over MMSTATUS
    localparam logic [63:0] SMODE_STATUS_MASK = 64'h80000003000DE133;

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
        logic [31:12] funct3;
        logic [11:7]  rd;
        logic [6:0]   opcode;
    } utype_t;

    typedef union packed {
        logic [31:0]   instr;
        rtype_t        rtype;
        itype_t        itype;
        stype_t        stype;
        utype_t        utype;
    } instruction_t;

    // --------------------
    // Opcodes
    // --------------------
    localparam OpcodeSystem    = 7'h73;
    localparam OpcodeFence     = 7'h0f;
    localparam OpcodeOp        = 7'h33;
    localparam OpcodeOp32      = 7'h3B;
    localparam OpcodeOpimm     = 7'h13;
    localparam OpcodeOpimm32   = 7'h1B;
    localparam OpcodeStore     = 7'h23;
    localparam OpcodeStoreFP   = 7'b01_001_11;
    localparam OpcodeLoad      = 7'h03;
    localparam OpcodeLoadFP    = 7'b00_001_11;
    localparam OpcodeBranch    = 7'h63;
    localparam OpcodeJalr      = 7'h67;
    localparam OpcodeJal       = 7'h6f;
    localparam OpcodeAuipc     = 7'h17;
    localparam OpcodeLui       = 7'h37;
    localparam OpcodeAmo       = 7'h2F;

    localparam OpcodeCJ        = 3'b101;
    localparam OpcodeCBeqz     = 3'b110;
    localparam OpcodeCBnez     = 3'b111;

    // ----------------------
    // Performance Counters
    // ----------------------
    localparam logic [11:0] PERF_L1_ICACHE_MISS = 12'h0;     // L1 Instr Cache Miss
    localparam logic [11:0] PERF_L1_DCACHE_MISS = 12'h1;     // L1 Data Cache Miss
    localparam logic [11:0] PERF_ITLB_MISS      = 12'h2;     // ITLB Miss
    localparam logic [11:0] PERF_DTLB_MISS      = 12'h3;     // DTLB Miss
    localparam logic [11:0] PERF_LOAD           = 12'h4;     // Loads
    localparam logic [11:0] PERF_STORE          = 12'h5;     // Stores
    localparam logic [11:0] PERF_EXCEPTION      = 12'h6;     // Taken exceptions
    localparam logic [11:0] PERF_EXCEPTION_RET  = 12'h7;     // Exception return
    localparam logic [11:0] PERF_BRANCH_JUMP    = 12'h8;     // Software change of PC
    localparam logic [11:0] PERF_CALL           = 12'h9;     // Procedure call
    localparam logic [11:0] PERF_RET            = 12'hA;     // Procedure Return
    localparam logic [11:0] PERF_MIS_PREDICT    = 12'hB;     // Branch mis-predicted

    // ----------------------
    // Virtual Memory
    // ----------------------
    // memory management, pte
    typedef struct packed {
        logic [9:0]  reserved;
        logic [43:0] ppn;
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

    // ----------------------
    // Exception Cause Codes
    // ----------------------
    localparam logic [63:0] INSTR_ADDR_MISALIGNED = 0;
    localparam logic [63:0] INSTR_ACCESS_FAULT    = 1;
    localparam logic [63:0] ILLEGAL_INSTR         = 2;
    localparam logic [63:0] BREAKPOINT            = 3;
    localparam logic [63:0] LD_ADDR_MISALIGNED    = 4;
    localparam logic [63:0] LD_ACCESS_FAULT       = 5;
    localparam logic [63:0] ST_ADDR_MISALIGNED    = 6;
    localparam logic [63:0] ST_ACCESS_FAULT       = 7;
    localparam logic [63:0] ENV_CALL_UMODE        = 8;  // environment call from user mode
    localparam logic [63:0] ENV_CALL_SMODE        = 9;  // environment call from supervisor mode
    localparam logic [63:0] ENV_CALL_MMODE        = 11; // environment call from machine mode
    localparam logic [63:0] INSTR_PAGE_FAULT      = 12; // Instruction page fault
    localparam logic [63:0] LOAD_PAGE_FAULT       = 13; // Load page fault
    localparam logic [63:0] STORE_PAGE_FAULT      = 15; // Store page fault

    localparam logic [63:0] S_SW_INTERRUPT        = (1 << 63) | 1;
    localparam logic [63:0] M_SW_INTERRUPT        = (1 << 63) | 3;
    localparam logic [63:0] S_TIMER_INTERRUPT     = (1 << 63) | 5;
    localparam logic [63:0] M_TIMER_INTERRUPT     = (1 << 63) | 7;
    localparam logic [63:0] S_EXT_INTERRUPT       = (1 << 63) | 9;
    localparam logic [63:0] M_EXT_INTERRUPT       = (1 << 63) | 11;

    // -----
    // CSRs
    // -----
    typedef enum logic [11:0] {
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
        CSR_MSCRATCH       = 12'h340,
        CSR_MEPC           = 12'h341,
        CSR_MCAUSE         = 12'h342,
        CSR_MTVAL          = 12'h343,
        CSR_MIP            = 12'h344,
        CSR_PMPCFG0        = 12'h3A0,
        CSR_PMPADDR0       = 12'h3B0,
        CSR_MVENDORID      = 12'hF11,
        CSR_MARCHID        = 12'hF12,
        CSR_MIMPID         = 12'hF13,
        CSR_MHARTID        = 12'hF14,
        CSR_MCYCLE         = 12'hB00,
        CSR_MINSTRET       = 12'hB02,
        CSR_DCACHE         = 12'h701,
        CSR_ICACHE         = 12'h700,

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
        // Counters and Timers
        CSR_CYCLE          = 12'hC00,
        CSR_TIME           = 12'hC01,
        CSR_INSTRET        = 12'hC02,
        // Performance counters
        CSR_L1_ICACHE_MISS = PERF_L1_ICACHE_MISS + 12'hC03,
        CSR_L1_DCACHE_MISS = PERF_L1_DCACHE_MISS + 12'hC03,
        CSR_ITLB_MISS      = PERF_ITLB_MISS      + 12'hC03,
        CSR_DTLB_MISS      = PERF_DTLB_MISS      + 12'hC03,
        CSR_LOAD           = PERF_LOAD           + 12'hC03,
        CSR_STORE          = PERF_STORE          + 12'hC03,
        CSR_EXCEPTION      = PERF_EXCEPTION      + 12'hC03,
        CSR_EXCEPTION_RET  = PERF_EXCEPTION_RET  + 12'hC03,
        CSR_BRANCH_JUMP    = PERF_BRANCH_JUMP    + 12'hC03,
        CSR_CALL           = PERF_CALL           + 12'hC03,
        CSR_RET            = PERF_RET            + 12'hC03,
        CSR_MIS_PREDICT    = PERF_MIS_PREDICT    + 12'hC03
    } csr_reg_t;

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

    function automatic logic [31:0] load (logic [2:0] size, logic[4:0] dest, logic[4:0] base, logic [11:0] offset);
        // OpCode Load
        return {offset[11:0], base, size, dest, 7'h03};
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

    function automatic logic [31:0] ebreak ();
        return 32'h00100073;
    endfunction

    function automatic logic [31:0] nop ();
        return 32'h00000013;
    endfunction

    function automatic logic [31:0] illegal ();
        return 32'h00000000;
    endfunction
endpackage

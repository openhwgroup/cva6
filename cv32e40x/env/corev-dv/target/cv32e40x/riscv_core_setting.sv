/*
 * Copyright 2019 Google LLC
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

//-----------------------------------------------------------------------------
// Processor feature configuration
//-----------------------------------------------------------------------------
// XLEN
parameter int XLEN = 32;

// Parameter for SATP mode, set to BARE if address translation is not supported
parameter satp_mode_t SATP_MODE = BARE;

// Supported Privileged mode
privileged_mode_t supported_privileged_mode[] = {MACHINE_MODE};

// Unsupported instructions
riscv_instr_name_t unsupported_instr[];

// ISA supported by the processor
riscv_instr_group_t supported_isa[$] = {RV32I, RV32M, RV32C, RV32ZBA, RV32ZBB, RV32ZBC, RV32ZBS};

// Interrupt mode support
mtvec_mode_t supported_interrupt_mode[$] = {DIRECT, VECTORED};

// The number of interrupt vectors to be generated, only used if VECTORED interrupt mode is
// supported
int max_interrupt_vector_num = 32;

// Valid CLINT interrupts
bit [31:0] valid_interrupt_mask = 32'hffff_0888;

// Physical memory protection support
bit support_pmp = 0;

// Debug mode support
bit support_debug_mode = 1;

// Support delegate trap to user mode
bit support_umode_trap = 0;

// Support sfence.vma instruction
bit support_sfence = 0;

// Support unaligned load/store
bit support_unaligned_load_store = 1'b1;

// GPR setting
parameter int NUM_FLOAT_GPR = 32;
parameter int NUM_GPR = 32;
parameter int NUM_VEC_GPR = 32;

// ----------------------------------------------------------------------------
// Vector extension configuration
// ----------------------------------------------------------------------------

// Parameter for vector extension
parameter int VECTOR_EXTENSION_ENABLE = 0;

parameter int VLEN = 512;

// Maximum size of a single vector element
parameter int ELEN = 32;

// Minimum size of a sub-element, which must be at most 8-bits.
parameter int SELEN = 8;

// Maximum size of a single vector element (encoded in vsew format)
parameter int VELEN = int'($ln(ELEN)/$ln(2)) - 3;

// Maxium LMUL supported by the core
parameter int MAX_LMUL = 8;

// ----------------------------------------------------------------------------
// Multi-harts configuration
// ----------------------------------------------------------------------------

// Number of harts
parameter int NUM_HARTS = 1;

// ----------------------------------------------------------------------------
// Privileged CSR implementation
// ----------------------------------------------------------------------------

// Implemented privileged CSR list
`ifdef DSIM
privileged_reg_t implemented_csr[] = {
`else
const privileged_reg_t implemented_csr[] = {
`endif
    // Machine mode mode CSR
    MSTATUS,        // Machine status
    MISA,           // ISA and extensions
    MIE,            // Machine interrupt-enable register
    MTVEC,          // Machine trap-handler base address
    //MTVT,           // Machine Trap-Handler Vector Table Base Address (CLIC=1)
    MSTATUSH,       // Machine Status (upper 32 bits).
    MCOUNTINHIBIT,  // Machine Counter-Inhibit Register
    MHPMEVENT3,     // Machine Performance-Monitoring Event Selector 3
    MHPMEVENT4,     // Machine Performance-Monitoring Event Selector 4
    MHPMEVENT5,     // Machine Performance-Monitoring Event Selector 5
    MHPMEVENT6,     // Machine Performance-Monitoring Event Selector 6
    MHPMEVENT7,     // Machine Performance-Monitoring Event Selector 7
    MHPMEVENT8,     // Machine Performance-Monitoring Event Selector 8
    MHPMEVENT9,     // Machine Performance-Monitoring Event Selector 9
    MHPMEVENT10,    // Machine Performance-Monitoring Event Selector 10
    MHPMEVENT11,    // Machine Performance-Monitoring Event Selector 11
    MHPMEVENT12,    // Machine Performance-Monitoring Event Selector 12
    MHPMEVENT13,    // Machine Performance-Monitoring Event Selector 13
    MHPMEVENT14,    // Machine Performance-Monitoring Event Selector 14
    MHPMEVENT15,    // Machine Performance-Monitoring Event Selector 15
    MHPMEVENT16,    // Machine Performance-Monitoring Event Selector 16
    MHPMEVENT17,    // Machine Performance-Monitoring Event Selector 17
    MHPMEVENT18,    // Machine Performance-Monitoring Event Selector 18
    MHPMEVENT19,    // Machine Performance-Monitoring Event Selector 19
    MHPMEVENT20,    // Machine Performance-Monitoring Event Selector 20
    MHPMEVENT21,    // Machine Performance-Monitoring Event Selector 21
    MHPMEVENT22,    // Machine Performance-Monitoring Event Selector 22
    MHPMEVENT23,    // Machine Performance-Monitoring Event Selector 23
    MHPMEVENT24,    // Machine Performance-Monitoring Event Selector 24
    MHPMEVENT25,    // Machine Performance-Monitoring Event Selector 25
    MHPMEVENT26,    // Machine Performance-Monitoring Event Selector 26
    MHPMEVENT27,    // Machine Performance-Monitoring Event Selector 27
    MHPMEVENT28,    // Machine Performance-Monitoring Event Selector 28
    MHPMEVENT29,    // Machine Performance-Monitoring Event Selector 29
    MHPMEVENT30,    // Machine Performance-Monitoring Event Selector 30
    MHPMEVENT31,    // Machine Performance-Monitoring Event Selector 31
    MSCRATCH,       // Scratch register for machine trap handlers
    MEPC,           // Machine exception program counter
    MCAUSE,         // Machine trap cause
    MTVAL,          // Machine bad address or instruction
    MIP,            // Machine interrupt pending
    //MNXTI,          // Interrupt handler address and enable modifier (CLIC=1)
    //MINTSTATUS,     // Current interrupt levels (CLIC=1)
    //MINTTHRESH,     // Interrupt-level threshold (CLIC=1)
    //MSCRATCHCSW,    // Conditional scratch swap on priv mode change (CLIC=1)
    //MSCRATCHCSWL,   // Conditional scratch swap on level change (CLIC=1)
    TSELECT,        // Trigger Select Register
    TDATA1,         // Trigger Data Register 1
    TDATA2,         // Trigger Data Register 2
    TDATA3,         // Trigger Data Register 3
    TINFO,          // Trigger Info
    TCONTROL,       // Trigger Control
    MCONTEXT,       // Machine Context
    MSCONTEXT,      // Machine Supervisor Context
    MCYCLE,         // Machine Instructions-Retired Counter
    MHPMCOUNTER3,   // Machine Performance-Monitoring Counter 3
    MHPMCOUNTER4,   // Machine Performance-Monitoring Counter 4
    MHPMCOUNTER5,   // Machine Performance-Monitoring Counter 5
    MHPMCOUNTER6,   // Machine Performance-Monitoring Counter 6
    MHPMCOUNTER7,   // Machine Performance-Monitoring Counter 7
    MHPMCOUNTER8,   // Machine Performance-Monitoring Counter 8
    MHPMCOUNTER9,   // Machine Performance-Monitoring Counter 9
    MHPMCOUNTER10,  // Machine Performance-Monitoring Counter 10
    MHPMCOUNTER11,  // Machine Performance-Monitoring Counter 11
    MHPMCOUNTER12,  // Machine Performance-Monitoring Counter 12
    MHPMCOUNTER13,  // Machine Performance-Monitoring Counter 13
    MHPMCOUNTER14,  // Machine Performance-Monitoring Counter 14
    MHPMCOUNTER15,  // Machine Performance-Monitoring Counter 15
    MHPMCOUNTER16,  // Machine Performance-Monitoring Counter 16
    MHPMCOUNTER17,  // Machine Performance-Monitoring Counter 17
    MHPMCOUNTER18,  // Machine Performance-Monitoring Counter 18
    MHPMCOUNTER19,  // Machine Performance-Monitoring Counter 19
    MHPMCOUNTER20,  // Machine Performance-Monitoring Counter 20
    MHPMCOUNTER21,  // Machine Performance-Monitoring Counter 21
    MHPMCOUNTER22,  // Machine Performance-Monitoring Counter 22
    MHPMCOUNTER23,  // Machine Performance-Monitoring Counter 23
    MHPMCOUNTER24,  // Machine Performance-Monitoring Counter 24
    MHPMCOUNTER25,  // Machine Performance-Monitoring Counter 25
    MHPMCOUNTER26,  // Machine Performance-Monitoring Counter 26
    MHPMCOUNTER27,  // Machine Performance-Monitoring Counter 27
    MHPMCOUNTER28,  // Machine Performance-Monitoring Counter 28
    MHPMCOUNTER29,  // Machine Performance-Monitoring Counter 29
    MHPMCOUNTER30,  // Machine Performance-Monitoring Counter 30
    MHPMCOUNTER31,  // Machine Performance-Monitoring Counter 31
    MCYCLEH,        // Upper 32 Machine Cycle Counter
    MINSTRETH,      // Upper 32 Machine Instructions-Retired Counter
    MHPMCOUNTER3H,  // Upper Machine Performance-Monitoring Counter 3
    MHPMCOUNTER4H,  // Upper Machine Performance-Monitoring Counter 4
    MHPMCOUNTER5H,  // Upper Machine Performance-Monitoring Counter 5
    MHPMCOUNTER6H,  // Upper Machine Performance-Monitoring Counter 6
    MHPMCOUNTER7H,  // Upper Machine Performance-Monitoring Counter 7
    MHPMCOUNTER8H,  // Upper Machine Performance-Monitoring Counter 8
    MHPMCOUNTER9H,  // Upper Machine Performance-Monitoring Counter 9
    MHPMCOUNTER10H, // Upper Machine Performance-Monitoring Counter 10
    MHPMCOUNTER11H, // Upper Machine Performance-Monitoring Counter 11
    MHPMCOUNTER12H, // Upper Machine Performance-Monitoring Counter 12
    MHPMCOUNTER13H, // Upper Machine Performance-Monitoring Counter 13
    MHPMCOUNTER14H, // Upper Machine Performance-Monitoring Counter 14
    MHPMCOUNTER15H, // Upper Machine Performance-Monitoring Counter 15
    MHPMCOUNTER16H, // Upper Machine Performance-Monitoring Counter 16
    MHPMCOUNTER17H, // Upper Machine Performance-Monitoring Counter 17
    MHPMCOUNTER18H, // Upper Machine Performance-Monitoring Counter 18
    MHPMCOUNTER19H, // Upper Machine Performance-Monitoring Counter 19
    MHPMCOUNTER20H, // Upper Machine Performance-Monitoring Counter 20
    MHPMCOUNTER21H, // Upper Machine Performance-Monitoring Counter 21
    MHPMCOUNTER22H, // Upper Machine Performance-Monitoring Counter 22
    MHPMCOUNTER23H, // Upper Machine Performance-Monitoring Counter 23
    MHPMCOUNTER24H, // Upper Machine Performance-Monitoring Counter 24
    MHPMCOUNTER25H, // Upper Machine Performance-Monitoring Counter 25
    MHPMCOUNTER26H, // Upper Machine Performance-Monitoring Counter 26
    MHPMCOUNTER27H, // Upper Machine Performance-Monitoring Counter 27
    MHPMCOUNTER28H, // Upper Machine Performance-Monitoring Counter 28
    MHPMCOUNTER29H, // Upper Machine Performance-Monitoring Counter 29
    MHPMCOUNTER30H, // Upper Machine Performance-Monitoring Counter 30
    MHPMCOUNTER31H, // Upper Machine Performance-Monitoring Counter 31
    MVENDORID,      // Vendor ID
    MARCHID,        // Architecture ID
    MIMPID,         // Implementation ID
    MHARTID,        // Hardware thread ID
    MCONFIGPTR      // Machine Configuration Pointer
};

`ifdef DSIM
  bit [11:0] custom_csr[] = {
`elsif _VCP
  bit [11:0] custom_csr[] = {
`else
  const bit [11:0] custom_csr[] = {
`endif
};

// ----------------------------------------------------------------------------
// Supported interrupt/exception setting, used for functional coverage
// ----------------------------------------------------------------------------

`ifdef DSIM
interrupt_cause_t implemented_interrupt[] = {
`else
const interrupt_cause_t implemented_interrupt[] = {
`endif
    M_SOFTWARE_INTR,
    M_TIMER_INTR,
    M_EXTERNAL_INTR
};

`ifdef DSIM
exception_cause_t implemented_exception[] = {
`else
const exception_cause_t implemented_exception[] = {
`endif
    INSTRUCTION_ACCESS_FAULT,
    ILLEGAL_INSTRUCTION,
    BREAKPOINT,
    LOAD_ADDRESS_MISALIGNED,
    LOAD_ACCESS_FAULT,
    ECALL_MMODE
};

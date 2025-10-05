
#ifndef RISCV_CSR_ENCODING_H
#define RISCV_CSR_ENCODING_H

#define MSTATUS_UIE         0x00000001
#define MSTATUS_SIE         0x00000002
#define MSTATUS_HIE         0x00000004
#define MSTATUS_MIE         0x00000008
#define MSTATUS_UPIE        0x00000010
#define MSTATUS_SPIE        0x00000020
#define MSTATUS_HPIE        0x00000040
#define MSTATUS_MPIE        0x00000080
#define MSTATUS_SPP         0x00000100
#define MSTATUS_HPP         0x00000600
#define MSTATUS_MPP         0x00001800
#define MSTATUS_FS          0x00006000
#define MSTATUS_XS          0x00018000
#define MSTATUS_MPRV        0x00020000
#define MSTATUS_SUM         0x00040000
#define MSTATUS_MXR         0x00080000
#define MSTATUS_TVM         0x00100000
#define MSTATUS_TW          0x00200000
#define MSTATUS_TSR         0x00400000
#define MSTATUS32_SD        0x80000000
#define MSTATUS64_SD        0x8000000000000000

#define MCAUSE32_CAUSE       0x7FFFFFFF
#define MCAUSE64_CAUSE       0x7FFFFFFFFFFFFFFF
#define MCAUSE32_INT         0x80000000
#define MCAUSE64_INT         0x8000000000000000

#define SSTATUS_UIE         0x00000001
#define SSTATUS_SIE         0x00000002
#define SSTATUS_UPIE        0x00000010
#define SSTATUS_SPIE        0x00000020
#define SSTATUS_SPP         0x00000100
#define SSTATUS_FS          0x00006000
#define SSTATUS_XS          0x00018000
#define SSTATUS_SUM         0x00040000
#define SSTATUS_MXR         0x00080000
#define SSTATUS32_SD        0x80000000
#define SSTATUS64_SD        0x8000000000000000

#define DCSR_XDEBUGVER      (3U<<30)
#define DCSR_NDRESET        (1<<29)
#define DCSR_FULLRESET      (1<<28)
#define DCSR_EBREAKM        (1<<15)
#define DCSR_EBREAKH        (1<<14)
#define DCSR_EBREAKS        (1<<13)
#define DCSR_EBREAKU        (1<<12)
#define DCSR_STOPCYCLE      (1<<10)
#define DCSR_STOPTIME       (1<<9)
#define DCSR_CAUSE          (7<<6)
#define DCSR_DEBUGINT       (1<<5)
#define DCSR_HALT           (1<<3)
#define DCSR_STEP           (1<<2)
#define DCSR_PRV            (3<<0)

#define DCSR_CAUSE_NONE     0
#define DCSR_CAUSE_SWBP     1
#define DCSR_CAUSE_HWBP     2
#define DCSR_CAUSE_DEBUGINT 3
#define DCSR_CAUSE_STEP     4
#define DCSR_CAUSE_HALT     5

#define MCONTROL_TYPE(xlen)    (0xfULL<<((xlen)-4))
#define MCONTROL_DMODE(xlen)   (1ULL<<((xlen)-5))
#define MCONTROL_MASKMAX(xlen) (0x3fULL<<((xlen)-11))

#define MCONTROL_SELECT     (1U<<19)
#define MCONTROL_TIMING     (1U<<18)
#define MCONTROL_ACTION     (0x3fU<<12)
#define MCONTROL_CHAIN      (1U<<11)
#define MCONTROL_MATCH      (0xfU<<7)
#define MCONTROL_M          (1U<<6)
#define MCONTROL_H          (1U<<5)
#define MCONTROL_S          (1U<<4)
#define MCONTROL_U          (1U<<3)
#define MCONTROL_EXECUTE    (1U<<2)
#define MCONTROL_STORE      (1U<<1)
#define MCONTROL_LOAD       (1U<<0)

#define MCONTROL_TYPE_NONE      0
#define MCONTROL_TYPE_MATCH     2

#define MCONTROL_ACTION_DEBUG_EXCEPTION   0
#define MCONTROL_ACTION_DEBUG_MODE        1
#define MCONTROL_ACTION_TRACE_START       2
#define MCONTROL_ACTION_TRACE_STOP        3
#define MCONTROL_ACTION_TRACE_EMIT        4

#define MCONTROL_MATCH_EQUAL     0
#define MCONTROL_MATCH_NAPOT     1
#define MCONTROL_MATCH_GE        2
#define MCONTROL_MATCH_LT        3
#define MCONTROL_MATCH_MASK_LOW  4
#define MCONTROL_MATCH_MASK_HIGH 5

#define MIP_SSIP            (1U << IRQ_S_SOFT)
#define MIP_HSIP            (1U << IRQ_H_SOFT)
#define MIP_MSIP            (1U << IRQ_M_SOFT)
#define MIP_STIP            (1U << IRQ_S_TIMER)
#define MIP_HTIP            (1U << IRQ_H_TIMER)
#define MIP_MTIP            (1U << IRQ_M_TIMER)
#define MIP_SEIP            (1U << IRQ_S_EXT)
#define MIP_HEIP            (1U << IRQ_H_EXT)
#define MIP_MEIP            (1U << IRQ_M_EXT)

#define SIP_SSIP MIP_SSIP
#define SIP_STIP MIP_STIP

#define PRV_U 0
#define PRV_S 1
#define PRV_H 2
#define PRV_M 3

#define SPTBR32_MODE 0x80000000
#define SPTBR32_ASID 0x7FC00000
#define SPTBR32_PPN  0x003FFFFF
#define SPTBR64_MODE 0xF000000000000000
#define SPTBR64_ASID 0x0FFFF00000000000
#define SPTBR64_PPN  0x00000FFFFFFFFFFF

#define SPTBR_MODE_OFF  0
#define SPTBR_MODE_SV32 1
#define SPTBR_MODE_SV39 8
#define SPTBR_MODE_SV48 9
#define SPTBR_MODE_SV57 10
#define SPTBR_MODE_SV64 11

#define PMP_R     0x01
#define PMP_W     0x02
#define PMP_X     0x04
#define PMP_A     0x18
#define PMP_L     0x80
#define PMP_SHIFT 2

#define PMP_TOR   0x08
#define PMP_NA4   0x10
#define PMP_NAPOT 0x18

#define IRQ_S_SOFT   1
#define IRQ_H_SOFT   2
#define IRQ_M_SOFT   3
#define IRQ_S_TIMER  5
#define IRQ_H_TIMER  6
#define IRQ_M_TIMER  7
#define IRQ_S_EXT    9
#define IRQ_H_EXT    10
#define IRQ_M_EXT    11
#define IRQ_COP      12
#define IRQ_HOST     13

#define DEFAULT_RSTVEC     0x00001000
#define CLINT_BASE         0x02000000
#define CLINT_SIZE         0x000c0000
#define EXT_IO_BASE        0x40000000
#define DRAM_BASE          0x80000000

// page table entry (PTE) fields
#define PTE_V     0x001 // Valid
#define PTE_R     0x002 // Read
#define PTE_W     0x004 // Write
#define PTE_X     0x008 // Execute
#define PTE_U     0x010 // User
#define PTE_G     0x020 // Global
#define PTE_A     0x040 // Accessed
#define PTE_D     0x080 // Dirty
#define PTE_SOFT  0x300 // Reserved for Software

#define PTE_PPN_SHIFT 10

#define PTE_TABLE(PTE) (((PTE) & (PTE_V | PTE_R | PTE_W | PTE_X)) == PTE_V)

#ifdef __riscv

#if __riscv_xlen == 64
# define MSTATUS_SD             MSTATUS64_SD
# define SSTATUS_SD             SSTATUS64_SD
# define RISCV_PGLEVEL_BITS     9
# define SPTBR_MODE             SPTBR64_MODE
# define MCAUSE_INT             MCAUSE64_INT                //ML added- should we be using later encoding.h?
# define MCAUSE_CAUSE           MCAUSE64_CAUSE              //ML added- should we be using later encoding.h?
#else
# define MSTATUS_SD MSTATUS32_SD
# define SSTATUS_SD SSTATUS32_SD
# define RISCV_PGLEVEL_BITS 10
# define SPTBR_MODE SPTBR32_MODE
# define MCAUSE_INT             MCAUSE32_INT                //ML added- should we be using later encoding.h?
# define MCAUSE_CAUSE           MCAUSE32_CAUSE              //ML added- should we be using later encoding.h?
#endif
#define RISCV_PGSHIFT 12
#define RISCV_PGSIZE (1 << RISCV_PGSHIFT)

#ifndef __ASSEMBLER__

#ifdef __GNUC__

#define read_reg(reg) ({ unsigned long __tmp; \
  asm volatile ("mv %0, " #reg : "=r"(__tmp)); \
  __tmp; })

#define read_csr(reg) ({ unsigned long __tmp; \
  asm volatile ("csrr %0, " #reg : "=r"(__tmp)); \
  __tmp; })

#define write_csr(reg, val) ({ \
  asm volatile ("csrw " #reg ", %0" :: "rK"(val)); })

#define swap_csr(reg, val) ({ unsigned long __tmp; \
  asm volatile ("csrrw %0, " #reg ", %1" : "=r"(__tmp) : "rK"(val)); \
  __tmp; })

#define set_csr(reg, bit) ({ unsigned long __tmp; \
  asm volatile ("csrrs %0, " #reg ", %1" : "=r"(__tmp) : "rK"(bit)); \
  __tmp; })

#define clear_csr(reg, bit) ({ unsigned long __tmp; \
  asm volatile ("csrrc %0, " #reg ", %1" : "=r"(__tmp) : "rK"(bit)); \
  __tmp; })

#if 0
#define csr_write(csr, val)                 \
({                              \
    unsigned long __v = (unsigned long)(val);       \
    asm volatile ("csrw " __ASM_STR(csr) ", %0" \
                  : : "rK" (__v)            \
                  : "memory");          \
})

#define csr_write(csr, val)                 \
({                              \
    unsigned long __v = (unsigned long)(val);       \
    __asm__ __volatile__ ("csrw " __ASM_STR(csr) ", %0" \
                  : : "rK" (__v)            \
                  : "memory");          \
})
#endif

#define rdtime() read_csr(time)
#define rdcycle() read_csr(cycle)
#define rdinstret() read_csr(instret)

#endif //__GNUC__

#endif //__ASSEMBLER__

#endif //__riscv

#endif // RISCV_CSR_ENCODING_H


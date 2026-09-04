#ifndef HMODE_CSR_H
#define HMODE_CSR_H

// mostly stolen from Linux "arch/riscv/include/asm/csr.h"

#define __ASM_STR(x) #x

/* Status register flags */
#define SR_SIE   0x00000002 /* Supervisor Interrupt Enable */
#define SR_MIE   0x00000008 /* Machine Interrupt Enable */
#define SR_SPIE  0x00000020 /* Previous Supervisor IE */
#define SR_MPIE  0x00000080 /* Previous Machine IE */
#define SR_SPP   0x00000100 /* Previously Supervisor */
#define SR_MPP   0x00001800 /* Previously Machine */
#define SR_MPP_U 0x00000000
#define SR_MPP_S 0x00000800
#define SR_MPP_M 0x00001800
#define SR_SUM   0x00040000 /* Supervisor User Memory Access */

#define SR_FS         0x00006000 /* Floating-point Status */
#define SR_FS_OFF     0x00000000
#define SR_FS_INITIAL 0x00002000
#define SR_FS_CLEAN   0x00004000
#define SR_FS_DIRTY   0x00006000

#define SR_VS         0x00000600 /* Vector Status */
#define SR_VS_OFF     0x00000000
#define SR_VS_INITIAL 0x00000200
#define SR_VS_CLEAN   0x00000400
#define SR_VS_DIRTY   0x00000600

#define SR_XS         0x00018000 /* Extension Status */
#define SR_XS_OFF     0x00000000
#define SR_XS_INITIAL 0x00008000
#define SR_XS_CLEAN   0x00010000
#define SR_XS_DIRTY   0x00018000

#define SR_MPRV 0x00020000 /* M-mode specific */

#define SR_FS_VS (SR_FS | SR_VS) /* Vector and Floating-Point Unit */

#define SR_SD 0x8000000000000000 /* FS/VS/XS dirty */

#define SR_UXL    0x300000000 /* XLEN mask for U-mode */
#define SR_UXL_32 0x100000000 /* XLEN = 32 for U-mode */
#define SR_UXL_64 0x200000000 /* XLEN = 64 for U-mode */
#define SR_SXL    0xc00000000 /* XLEN mask for S-mode */
#define SR_SXL_32 0x400000000 /* XLEN = 32 for S-mode */
#define SR_SXL_64 0x800000000 /* XLEN = 64 for S-mode */

/* SATP flags */
#define SATP_PPN        0x00000FFFFFFFFFFF
#define SATP_MODE_39    0x8000000000000000
#define SATP_MODE_48    0x9000000000000000
#define SATP_MODE_57    0xa000000000000000
#define SATP_MODE_SHIFT 60
#define SATP_ASID_BITS  16
#define SATP_ASID_SHIFT 44
#define SATP_ASID_MASK  0xFFFF

#define MAKE_HGATP(root, mode) ((((root) >> 12) & SATP_PPN) | (mode))
#define MAKE_SATP(root, mode)  ((((root) >> 12) & SATP_PPN) | (mode))

/* Exception cause high bit - is an interrupt if set */
#define CAUSE_IRQ_FLAG (1ul << 63)

/* Interrupt causes (minus the high bit) */
#define IRQ_S_SOFT    1
#define IRQ_VS_SOFT   2
#define IRQ_M_SOFT    3
#define IRQ_S_TIMER   5
#define IRQ_VS_TIMER  6
#define IRQ_M_TIMER   7
#define IRQ_S_EXT     9
#define IRQ_VS_EXT    10
#define IRQ_M_EXT     11
#define IRQ_S_GEXT    12
#define IRQ_PMU_OVF   13
#define IRQ_LOCAL_MAX (IRQ_PMU_OVF + 1)
//#define IRQ_LOCAL_MASK GENMASK((IRQ_LOCAL_MAX - 1), 0)

/* Exception causes */
#define EXC_INST_MISALIGNED        0
#define EXC_INST_ACCESS            1
#define EXC_INST_ILLEGAL           2
#define EXC_BREAKPOINT             3
#define EXC_LOAD_MISALIGNED        4
#define EXC_LOAD_ACCESS            5
#define EXC_STORE_MISALIGNED       6
#define EXC_STORE_ACCESS           7
#define EXC_U_VU_SYSCALL           8
#define EXC_HS_SYSCALL             9
#define EXC_VS_SYSCALL             10
#define EXC_M_SYSCALL              11
#define EXC_INST_PAGE_FAULT        12
#define EXC_LOAD_PAGE_FAULT        13
#define EXC_STORE_PAGE_FAULT       15
#define EXC_INST_GUEST_PAGE_FAULT  20
#define EXC_LOAD_GUEST_PAGE_FAULT  21
#define EXC_VIRTUAL_INST_FAULT     22
#define EXC_STORE_GUEST_PAGE_FAULT 23

/* PMP configuration */
#define PMP_R       0x01
#define PMP_W       0x02
#define PMP_X       0x04
#define PMP_A       0x18
#define PMP_A_TOR   0x08
#define PMP_A_NA4   0x10
#define PMP_A_NAPOT 0x18
#define PMP_L       0x80

/* HSTATUS flags */
#define HSTATUS_VSXL        0x300000000
#define HSTATUS_VSXL_SHIFT  32
#define HSTATUS_VTSR        0x00400000
#define HSTATUS_VTW         0x00200000
#define HSTATUS_VTVM        0x00100000
#define HSTATUS_VGEIN       0x0003f000
#define HSTATUS_VGEIN_SHIFT 12
#define HSTATUS_HU          0x00000200
#define HSTATUS_SPVP        0x00000100
#define HSTATUS_SPV         0x00000080
#define HSTATUS_GVA         0x00000040
#define HSTATUS_VSBE        0x00000020

/* HGATP flags */
#define HGATP_MODE_OFF    0
#define HGATP_MODE_SV32X4 1
#define HGATP_MODE_SV39X4 8
#define HGATP_MODE_SV48X4 9
#define HGATP_MODE_SV57X4 10

#define HGATP32_MODE_SHIFT 31
#define HGATP32_VMID_SHIFT 22
#define HGATP32_VMID       GENMASK(28, 22)
#define HGATP32_PPN        GENMASK(21, 0)

#define HGATP64_MODE_SHIFT 60
#define HGATP64_VMID_SHIFT 44
#define HGATP64_VMID       GENMASK(57, 44)
#define HGATP64_PPN        GENMASK(43, 0)

#define HGATP_PAGE_SHIFT 12

#define HGATP_PPN        HGATP64_PPN
#define HGATP_VMID_SHIFT HGATP64_VMID_SHIFT
#define HGATP_VMID       HGATP64_VMID
#define HGATP_MODE_SHIFT HGATP64_MODE_SHIFT

/* VSIP & HVIP relation */
#define VSIP_TO_HVIP_SHIFT (IRQ_VS_SOFT - IRQ_S_SOFT)
#define VSIP_VALID_MASK    ((1 << IRQ_S_SOFT) | (1 << IRQ_S_TIMER) | (1 << IRQ_S_EXT))

/* AIA CSR bits */
#define TOPI_IID_SHIFT  16
#define TOPI_IID_MASK   GENMASK(11, 0)
#define TOPI_IPRIO_MASK GENMASK(7, 0)
#define TOPI_IPRIO_BITS 8

#define TOPEI_ID_SHIFT  16
#define TOPEI_ID_MASK   GENMASK(10, 0)
#define TOPEI_PRIO_MASK GENMASK(10, 0)

#define ISELECT_IPRIO0  0x30
#define ISELECT_IPRIO15 0x3f
#define ISELECT_MASK    GENMASK(8, 0)

#define HVICTL_VTI       BIT(30)
#define HVICTL_IID       GENMASK(27, 16)
#define HVICTL_IID_SHIFT 16
#define HVICTL_DPR       BIT(9)
#define HVICTL_IPRIOM    BIT(8)
#define HVICTL_IPRIO     GENMASK(7, 0)

/* xENVCFG flags */
#define ENVCFG_STCE       (1 << 63)
#define ENVCFG_PBMTE      (1 << 62)
#define ENVCFG_CBZE       (1 << 7)
#define ENVCFG_CBCFE      (1 << 6)
#define ENVCFG_CBIE_SHIFT 4
#define ENVCFG_CBIE       (0x3 << ENVCFG_CBIE_SHIFT)
#define ENVCFG_CBIE_ILL   0x0
#define ENVCFG_CBIE_FLUSH 0x1
#define ENVCFG_CBIE_INV   0x3
#define ENVCFG_FIOM       0x1

/* symbolic CSR names: */
#define CSR_CYCLE         0xc00
#define CSR_TIME          0xc01
#define CSR_INSTRET       0xc02
#define CSR_HPMCOUNTER3   0xc03
#define CSR_HPMCOUNTER4   0xc04
#define CSR_HPMCOUNTER5   0xc05
#define CSR_HPMCOUNTER6   0xc06
#define CSR_HPMCOUNTER7   0xc07
#define CSR_HPMCOUNTER8   0xc08
#define CSR_HPMCOUNTER9   0xc09
#define CSR_HPMCOUNTER10  0xc0a
#define CSR_HPMCOUNTER11  0xc0b
#define CSR_HPMCOUNTER12  0xc0c
#define CSR_HPMCOUNTER13  0xc0d
#define CSR_HPMCOUNTER14  0xc0e
#define CSR_HPMCOUNTER15  0xc0f
#define CSR_HPMCOUNTER16  0xc10
#define CSR_HPMCOUNTER17  0xc11
#define CSR_HPMCOUNTER18  0xc12
#define CSR_HPMCOUNTER19  0xc13
#define CSR_HPMCOUNTER20  0xc14
#define CSR_HPMCOUNTER21  0xc15
#define CSR_HPMCOUNTER22  0xc16
#define CSR_HPMCOUNTER23  0xc17
#define CSR_HPMCOUNTER24  0xc18
#define CSR_HPMCOUNTER25  0xc19
#define CSR_HPMCOUNTER26  0xc1a
#define CSR_HPMCOUNTER27  0xc1b
#define CSR_HPMCOUNTER28  0xc1c
#define CSR_HPMCOUNTER29  0xc1d
#define CSR_HPMCOUNTER30  0xc1e
#define CSR_HPMCOUNTER31  0xc1f
#define CSR_CYCLEH        0xc80
#define CSR_TIMEH         0xc81
#define CSR_INSTRETH      0xc82
#define CSR_HPMCOUNTER3H  0xc83
#define CSR_HPMCOUNTER4H  0xc84
#define CSR_HPMCOUNTER5H  0xc85
#define CSR_HPMCOUNTER6H  0xc86
#define CSR_HPMCOUNTER7H  0xc87
#define CSR_HPMCOUNTER8H  0xc88
#define CSR_HPMCOUNTER9H  0xc89
#define CSR_HPMCOUNTER10H 0xc8a
#define CSR_HPMCOUNTER11H 0xc8b
#define CSR_HPMCOUNTER12H 0xc8c
#define CSR_HPMCOUNTER13H 0xc8d
#define CSR_HPMCOUNTER14H 0xc8e
#define CSR_HPMCOUNTER15H 0xc8f
#define CSR_HPMCOUNTER16H 0xc90
#define CSR_HPMCOUNTER17H 0xc91
#define CSR_HPMCOUNTER18H 0xc92
#define CSR_HPMCOUNTER19H 0xc93
#define CSR_HPMCOUNTER20H 0xc94
#define CSR_HPMCOUNTER21H 0xc95
#define CSR_HPMCOUNTER22H 0xc96
#define CSR_HPMCOUNTER23H 0xc97
#define CSR_HPMCOUNTER24H 0xc98
#define CSR_HPMCOUNTER25H 0xc99
#define CSR_HPMCOUNTER26H 0xc9a
#define CSR_HPMCOUNTER27H 0xc9b
#define CSR_HPMCOUNTER28H 0xc9c
#define CSR_HPMCOUNTER29H 0xc9d
#define CSR_HPMCOUNTER30H 0xc9e
#define CSR_HPMCOUNTER31H 0xc9f

#define CSR_SSCOUNTOVF 0xda0

#define CSR_SSTATUS    0x100
#define CSR_SIE        0x104
#define CSR_STVEC      0x105
#define CSR_SCOUNTEREN 0x106
#define CSR_SENVCFG    0x10a
#define CSR_SSCRATCH   0x140
#define CSR_SEPC       0x141
#define CSR_SCAUSE     0x142
#define CSR_STVAL      0x143
#define CSR_SIP        0x144
#define CSR_SATP       0x180

#define CSR_STIMECMP  0x14D
#define CSR_STIMECMPH 0x15D

/* Supervisor-Level Window to Indirectly Accessed Registers (AIA) */
#define CSR_SISELECT 0x150
#define CSR_SIREG    0x151

/* Supervisor-Level Interrupts (AIA) */
#define CSR_STOPEI 0x15c
#define CSR_STOPI  0xdb0

/* Supervisor-Level High-Half CSRs (AIA) */
#define CSR_SIEH 0x114
#define CSR_SIPH 0x154

#define CSR_VSSTATUS   0x200
#define CSR_VSIE       0x204
#define CSR_VSTVEC     0x205
#define CSR_VSSCRATCH  0x240
#define CSR_VSEPC      0x241
#define CSR_VSCAUSE    0x242
#define CSR_VSTVAL     0x243
#define CSR_VSIP       0x244
#define CSR_VSATP      0x280
#define CSR_VSTIMECMP  0x24D
#define CSR_VSTIMECMPH 0x25D

#define CSR_HSTATUS     0x600
#define CSR_HEDELEG     0x602
#define CSR_HIDELEG     0x603
#define CSR_HIE         0x604
#define CSR_HTIMEDELTA  0x605
#define CSR_HCOUNTEREN  0x606
#define CSR_HGEIE       0x607
#define CSR_HENVCFG     0x60a
#define CSR_HTIMEDELTAH 0x615
#define CSR_HENVCFGH    0x61a
#define CSR_HTVAL       0x643
#define CSR_HIP         0x644
#define CSR_HVIP        0x645
#define CSR_HTINST      0x64a
#define CSR_HGATP       0x680
#define CSR_HGEIP       0xe12

/* Virtual Interrupts and Interrupt Priorities (H-extension with AIA) */
#define CSR_HVIEN    0x608
#define CSR_HVICTL   0x609
#define CSR_HVIPRIO1 0x646
#define CSR_HVIPRIO2 0x647

/* VS-Level Window to Indirectly Accessed Registers (H-extension with AIA) */
#define CSR_VSISELECT 0x250
#define CSR_VSIREG    0x251

/* VS-Level Interrupts (H-extension with AIA) */
#define CSR_VSTOPEI 0x25c
#define CSR_VSTOPI  0xeb0

/* Hypervisor and VS-Level High-Half CSRs (H-extension with AIA) */
#define CSR_HIDELEGH  0x613
#define CSR_HVIENH    0x618
#define CSR_HVIPH     0x655
#define CSR_HVIPRIO1H 0x656
#define CSR_HVIPRIO2H 0x657
#define CSR_VSIEH     0x214
#define CSR_VSIPH     0x254

#define CSR_MSTATUS   0x300
#define CSR_MISA      0x301
#define CSR_MEDELEG   0x302
#define CSR_MIDELEG   0x303
#define CSR_MIE       0x304
#define CSR_MTVEC     0x305
#define CSR_MENVCFG   0x30a
#define CSR_MENVCFGH  0x31a
#define CSR_MSCRATCH  0x340
#define CSR_MEPC      0x341
#define CSR_MCAUSE    0x342
#define CSR_MTVAL     0x343
#define CSR_MIP       0x344
#define CSR_MSECCFG   0x747
#define CSR_PMPCFG0   0x3a0
#define CSR_PMPCFG1   0x3a1 // RV32 only
#define CSR_PMPCFG2   0x3a2
#define CSR_PMPCFG3   0x3a3 // RV32 only
#define CSR_PMPCFG4   0x3a4
#define CSR_PMPCFG5   0x3a5 // RV32 only
#define CSR_PMPCFG6   0x3a6
#define CSR_PMPCFG7   0x3a7 // RV32 only
#define CSR_PMPCFG8   0x3a8
#define CSR_PMPCFG9   0x3a9 // RV32 only
#define CSR_PMPCFG10  0x3aa
#define CSR_PMPCFG11  0x3ab // RV32 only
#define CSR_PMPCFG12  0x3ac
#define CSR_PMPCFG13  0x3ad // RV32 only
#define CSR_PMPCFG14  0x3ae
#define CSR_PMPCFG15  0x3af // RV32 only
#define CSR_PMPADDR0  0x3b0
#define CSR_PMPADDR1  0x3b1
#define CSR_PMPADDR2  0x3b2
#define CSR_PMPADDR3  0x3b3
#define CSR_PMPADDR4  0x3b4
#define CSR_PMPADDR5  0x3b5
#define CSR_PMPADDR6  0x3b6
#define CSR_PMPADDR7  0x3b7
#define CSR_PMPADDR8  0x3b8
#define CSR_PMPADDR9  0x3b9
#define CSR_PMPADDR10 0x3ba
#define CSR_PMPADDR11 0x3bb
#define CSR_PMPADDR12 0x3bc
#define CSR_PMPADDR13 0x3bd
#define CSR_PMPADDR14 0x3be
#define CSR_PMPADDR15 0x3bf
#define CSR_PMPADDR16 0x3c0
#define CSR_PMPADDR17 0x3c1
#define CSR_PMPADDR18 0x3c2
#define CSR_PMPADDR19 0x3c3
#define CSR_PMPADDR20 0x3c4
#define CSR_PMPADDR21 0x3c5
#define CSR_PMPADDR22 0x3c6
#define CSR_PMPADDR23 0x3c7
#define CSR_PMPADDR24 0x3c8
#define CSR_PMPADDR25 0x3c9
#define CSR_PMPADDR26 0x3ca
#define CSR_PMPADDR27 0x3cb
#define CSR_PMPADDR28 0x3cc
#define CSR_PMPADDR29 0x3cd
#define CSR_PMPADDR30 0x3ce
#define CSR_PMPADDR31 0x3cf
#define CSR_PMPADDR32 0x3d0
#define CSR_PMPADDR33 0x3d1
#define CSR_PMPADDR34 0x3d2
#define CSR_PMPADDR35 0x3d3
#define CSR_PMPADDR36 0x3d4
#define CSR_PMPADDR37 0x3d5
#define CSR_PMPADDR38 0x3d6
#define CSR_PMPADDR39 0x3d7
#define CSR_PMPADDR40 0x3d8
#define CSR_PMPADDR41 0x3d9
#define CSR_PMPADDR42 0x3da
#define CSR_PMPADDR43 0x3db
#define CSR_PMPADDR44 0x3dc
#define CSR_PMPADDR45 0x3dd
#define CSR_PMPADDR46 0x3de
#define CSR_PMPADDR47 0x3df
#define CSR_PMPADDR48 0x3e0
#define CSR_PMPADDR49 0x3e1
#define CSR_PMPADDR50 0x3e2
#define CSR_PMPADDR51 0x3e3
#define CSR_PMPADDR52 0x3e4
#define CSR_PMPADDR53 0x3e5
#define CSR_PMPADDR54 0x3e6
#define CSR_PMPADDR55 0x3e7
#define CSR_PMPADDR56 0x3e8
#define CSR_PMPADDR57 0x3e9
#define CSR_PMPADDR58 0x3ea
#define CSR_PMPADDR59 0x3eb
#define CSR_PMPADDR60 0x3ec
#define CSR_PMPADDR61 0x3ed
#define CSR_PMPADDR62 0x3ee
#define CSR_PMPADDR63 0x3ef
#define CSR_MVENDORID 0xf11
#define CSR_MARCHID   0xf12
#define CSR_MIMPID    0xf13
#define CSR_MHARTID   0xf14

/* Machine-Level Window to Indirectly Accessed Registers (AIA) */
#define CSR_MISELECT 0x350
#define CSR_MIREG    0x351

/* Machine-Level Interrupts (AIA) */
#define CSR_MTOPEI 0x35c
#define CSR_MTOPI  0xfb0

/* Virtual Interrupts for Supervisor Level (AIA) */
#define CSR_MVIEN 0x308
#define CSR_MVIP  0x309

/* Machine-Level High-Half CSRs (AIA) */
#define CSR_MIDELEGH 0x313
#define CSR_MIEH     0x314
#define CSR_MVIENH   0x318
#define CSR_MVIPH    0x319
#define CSR_MIPH     0x354

#define CSR_VSTART 0x8
#define CSR_VCSR   0xf
#define CSR_VL     0xc20
#define CSR_VTYPE  0xc21
#define CSR_VLENB  0xc22

#define RV_IRQ_PMU IRQ_PMU_OVF
#define SIP_LCOFIP (0x1 << IRQ_PMU_OVF)

/* IE/IP (Supervisor/Machine Interrupt Enable/Pending) flags */
#define IE_M_SIE (0x1 << IRQ_M_SOFT)
#define IE_M_TIE (0x1 << IRQ_M_TIMER)
#define IE_M_EIE (0x1 << IRQ_M_EXT)
#define IE_S_SIE (0x1 << IRQ_S_SOFT)
#define IE_S_TIE (0x1 << IRQ_S_TIMER)
#define IE_S_EIE (0x1 << IRQ_S_EXT)

#define bit(obj) (1ul << (obj))

#define csr_swap(csr, val)                                                                           \
    ({                                                                                               \
        unsigned long __v = (unsigned long)(val);                                                    \
        __asm__ __volatile__("csrrw %0, " __ASM_STR(csr) ", %1" : "=r"(__v) : "rK"(__v) : "memory"); \
        __v;                                                                                         \
    })

#define csr_read(csr)                                                              \
    ({                                                                             \
        register unsigned long __v;                                                \
        __asm__ __volatile__("csrr %0, " __ASM_STR(csr) : "=r"(__v) : : "memory"); \
        __v;                                                                       \
    })

#define csr_write(csr, val)                                                           \
    ({                                                                                \
        unsigned long __v = (unsigned long)(val);                                     \
        __asm__ __volatile__("csrw " __ASM_STR(csr) ", %0" : : "rK"(__v) : "memory"); \
    })

#define csr_read_set(csr, val)                                                                       \
    ({                                                                                               \
        unsigned long __v = (unsigned long)(val);                                                    \
        __asm__ __volatile__("csrrs %0, " __ASM_STR(csr) ", %1" : "=r"(__v) : "rK"(__v) : "memory"); \
        __v;                                                                                         \
    })

#define csr_set(csr, val)                                                             \
    ({                                                                                \
        unsigned long __v = (unsigned long)(val);                                     \
        __asm__ __volatile__("csrs " __ASM_STR(csr) ", %0" : : "rK"(__v) : "memory"); \
    })

#define csr_read_clear(csr, val)                                                                     \
    ({                                                                                               \
        unsigned long __v = (unsigned long)(val);                                                    \
        __asm__ __volatile__("csrrc %0, " __ASM_STR(csr) ", %1" : "=r"(__v) : "rK"(__v) : "memory"); \
        __v;                                                                                         \
    })

#define csr_clear(csr, val)                                                           \
    ({                                                                                \
        unsigned long __v = (unsigned long)(val);                                     \
        __asm__ __volatile__("csrc " __ASM_STR(csr) ", %0" : : "rK"(__v) : "memory"); \
    })

#endif //HMODE_CSR_H

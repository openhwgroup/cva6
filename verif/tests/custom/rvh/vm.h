#ifndef HMODE_VM_H
#define HMODE_VM_H

#include "types.h"

#define PAGE_SIZE                     (0x1000)
#define FLAG_MASK                     (0xE0000000000003FF)
#define BUILD_PTE(destination, flags) ((((destination) >> 2) & (0xFFFFFFFFFFF000 >> 2)) | ((flags) & (FLAG_MASK)))
#define FLAG_NONE                     (0ul)
#define FLAG_VALID                    (1ul)
#define FLAG_READ                     (1ul << 1)
#define FLAG_WRITE                    (1ul << 2)
#define FLAG_EXEC                     (1ul << 3)
#define FLAG_USER                     (1ul << 4)
#define FLAG_GLOBAL                   (1ul << 5)
#define FLAG_ACCESS                   (1ul << 6)
#define FLAG_DIRTY                    (1ul << 7)
#define ENTRY_SIZE(level)             (1ul << ((level) * 9 + 3))
#define ENTRY_MASK(level)             (0x1fful << ((level) * 9 + 3))
#define ENTRY_MASK_LOWER(level)       (ENTRY_SIZE(level) - 1)
#define ALIGN_ADDRESS(address, level) ((address) & (~ENTRY_MASK_LOWER(level)))
#define DEFAULT_FLAGS                 (FLAG_ACCESS | FLAG_DIRTY)
#define FLAG_SET(pte, flags)                               \
    ({                                                     \
        (*pte) &= ~FLAG_MASK;                              \
        (*pte) |= (((flags) | DEFAULT_FLAGS) & FLAG_MASK); \
    })

static inline void flush_tlb(void) {
    asm volatile("sfence.vma" : : : "memory");
}
static inline void flush_tlb_addr(uint64_t va) {
    asm volatile("sfence.vma %0" : : "r"(va) : "memory");
}
static inline void flush_tlb_asid(uint64_t asid) {
    asm volatile("sfence.vma x0,%0" : : "r"(asid) : "memory");
}
static inline void flush_tlb_asid_addr(uint64_t asid, uint64_t va) {
    asm volatile("sfence.vma %0,%1" : : "r"(va), "r"(asid) : "memory");
}
static inline void flush_htlb(void) {
    asm volatile("hfence.gvma" : : : "memory");
}
static inline void flush_htlb_addr(uint64_t gpa) {
    asm volatile("hfence.gvma %0" : : "r"(gpa >> 2) : "memory");
}
static inline void flush_htlb_vmid(uint64_t vmid) {
    asm volatile("hfence.gvma x0,%0" : : "r"(vmid >> 2) : "memory");
}
static inline void flush_htlb_vmid_addr(uint64_t vmid, uint64_t gpa) {
    asm volatile("hfence.gvma %0,%1" : : "r"(gpa >> 2), "r"(vmid) : "memory");
}
static inline void flush_vtlb(void) {
    asm volatile("hfence.vvma" : : : "memory");
}
static inline void flush_vtlb_addr(uint64_t gva) {
    asm volatile("hfence.vvma %0" : : "r"(gva) : "memory");
}
static inline void flush_vtlb_asid(uint64_t asid) {
    asm volatile("hfence.vvma x0,%0" : : "r"(asid) : "memory");
}
static inline void flush_vtlb_asid_addr(uint64_t asid, uint64_t gva) {
    asm volatile("hfence.vvma %0,%1" : : "r"(gva), "r"(asid) : "memory");
}

struct segment {
    uint64_t base;
    uint64_t mask; // size + 1
    uint64_t *associated_pte;
    uint64_t associated_pa;
    const char *comment;
};

enum mapping {
    MAPPING_S_LVL1,
    MAPPING_S_LVL2,
    MAPPING_S_LVL3,
    MAPPING_H_LVL1,
    MAPPING_H_LVL2,
    MAPPING_H_LVL3,
    MAPPING_VS_LVL1,
    MAPPING_VS_LVL2,
    MAPPING_VS_LVL3,
    MAPPING_MAX
};

extern struct segment mapping[MAPPING_MAX];

void build_page_tables(void);
uint64_t get_translated_symbol(uint64_t symbol_address, enum mapping id, const char func[], const char file[], int line);

extern uint64_t __satp_lvl3;
extern uint64_t __satp_lvl2;
extern uint64_t __satp_lvl1;
extern uint64_t *const satp_lvl3;
extern uint64_t *const satp_lvl2;
extern uint64_t *const satp_lvl1;
#define SATP_ROOT ((uint64_t)satp_lvl3)
extern uint64_t __hgatp_lvl3;
extern uint64_t __hgatp_lvl2;
extern uint64_t __hgatp_lvl1;
extern uint64_t *const hgatp_lvl3;
extern uint64_t *const hgatp_lvl2;
extern uint64_t *const hgatp_lvl1;
#define HGATP_ROOT ((uint64_t)hgatp_lvl3)

#endif //HMODE_VM_H

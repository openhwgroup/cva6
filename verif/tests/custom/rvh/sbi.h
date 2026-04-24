#ifndef HMODE_SBI_H
#define HMODE_SBI_H

#include "types.h"

// Content from this file is mostly stolen from Linux (arch/riscv/include/asm/sbi.h)

struct sbiret {
    long error;
    long value;
};

enum sbi_ext_id {
    SBI_EXT_BASE = 0x10,
    SBI_EXT_TIME = 0x54494D45,
    SBI_EXT_IPI = 0x735049,
    SBI_EXT_RFENCE = 0x52464E43,
    SBI_EXT_HSM = 0x48534D,
    SBI_EXT_SRST = 0x53525354,
    SBI_EXT_PMU = 0x504D55,
    SBI_EXT_DBCN = 0x4442434E
};

enum sbi_ext_base_fid {
    SBI_EXT_BASE_GET_SPEC_VERSION = 0,
    SBI_EXT_BASE_GET_IMP_ID,
    SBI_EXT_BASE_GET_IMP_VERSION,
    SBI_EXT_BASE_PROBE_EXT,
    SBI_EXT_BASE_GET_MVENDORID,
    SBI_EXT_BASE_GET_MARCHID,
    SBI_EXT_BASE_GET_MIMPID,
};

enum sbi_ext_time_fid {
    SBI_EXT_TIME_SET_TIMER = 0,
};

enum sbi_ext_ipi_fid {
    SBI_EXT_IPI_SEND_IPI = 0,
};

enum sbi_ext_rfence_fid {
    SBI_EXT_RFENCE_REMOTE_FENCE_I = 0,
    SBI_EXT_RFENCE_REMOTE_SFENCE_VMA,
    SBI_EXT_RFENCE_REMOTE_SFENCE_VMA_ASID,
    SBI_EXT_RFENCE_REMOTE_HFENCE_GVMA_VMID,
    SBI_EXT_RFENCE_REMOTE_HFENCE_GVMA,
    SBI_EXT_RFENCE_REMOTE_HFENCE_VVMA_ASID,
    SBI_EXT_RFENCE_REMOTE_HFENCE_VVMA,
};

enum sbi_ext_hsm_fid {
    SBI_EXT_HSM_HART_START = 0,
    SBI_EXT_HSM_HART_STOP,
    SBI_EXT_HSM_HART_STATUS,
    SBI_EXT_HSM_HART_SUSPEND,
};

enum sbi_hsm_hart_state {
    SBI_HSM_STATE_STARTED = 0,
    SBI_HSM_STATE_STOPPED,
    SBI_HSM_STATE_START_PENDING,
    SBI_HSM_STATE_STOP_PENDING,
    SBI_HSM_STATE_SUSPENDED,
    SBI_HSM_STATE_SUSPEND_PENDING,
    SBI_HSM_STATE_RESUME_PENDING,
};

enum sbi_ext_srst_fid {
    SBI_EXT_SRST_RESET = 0,
};

enum sbi_srst_reset_type {
    SBI_SRST_RESET_TYPE_SHUTDOWN = 0,
    SBI_SRST_RESET_TYPE_COLD_REBOOT,
    SBI_SRST_RESET_TYPE_WARM_REBOOT,
};

enum sbi_srst_reset_reason {
    SBI_SRST_RESET_REASON_NONE = 0,
    SBI_SRST_RESET_REASON_SYS_FAILURE,
};

enum sbi_ext_pmu_fid {
    SBI_EXT_PMU_NUM_COUNTERS = 0,
    SBI_EXT_PMU_COUNTER_GET_INFO,
    SBI_EXT_PMU_COUNTER_CFG_MATCH,
    SBI_EXT_PMU_COUNTER_START,
    SBI_EXT_PMU_COUNTER_STOP,
    SBI_EXT_PMU_COUNTER_FW_READ,
};

/** General pmu event codes specified in SBI PMU extension */
enum sbi_pmu_hw_generic_events_t {
    SBI_PMU_HW_NO_EVENT = 0,
    SBI_PMU_HW_CPU_CYCLES = 1,
    SBI_PMU_HW_INSTRUCTIONS = 2,
    SBI_PMU_HW_CACHE_REFERENCES = 3,
    SBI_PMU_HW_CACHE_MISSES = 4,
    SBI_PMU_HW_BRANCH_INSTRUCTIONS = 5,
    SBI_PMU_HW_BRANCH_MISSES = 6,
    SBI_PMU_HW_BUS_CYCLES = 7,
    SBI_PMU_HW_STALLED_CYCLES_FRONTEND = 8,
    SBI_PMU_HW_STALLED_CYCLES_BACKEND = 9,
    SBI_PMU_HW_REF_CPU_CYCLES = 10,

    SBI_PMU_HW_GENERAL_MAX,
};

/**
 * Special "firmware" events provided by the firmware, even if the hardware
 * does not support performance events. These events are encoded as a raw
 * event type in Linux kernel perf framework.
 */
enum sbi_pmu_fw_generic_events_t {
    SBI_PMU_FW_MISALIGNED_LOAD = 0,
    SBI_PMU_FW_MISALIGNED_STORE = 1,
    SBI_PMU_FW_ACCESS_LOAD = 2,
    SBI_PMU_FW_ACCESS_STORE = 3,
    SBI_PMU_FW_ILLEGAL_INSN = 4,
    SBI_PMU_FW_SET_TIMER = 5,
    SBI_PMU_FW_IPI_SENT = 6,
    SBI_PMU_FW_IPI_RCVD = 7,
    SBI_PMU_FW_FENCE_I_SENT = 8,
    SBI_PMU_FW_FENCE_I_RCVD = 9,
    SBI_PMU_FW_SFENCE_VMA_SENT = 10,
    SBI_PMU_FW_SFENCE_VMA_RCVD = 11,
    SBI_PMU_FW_SFENCE_VMA_ASID_SENT = 12,
    SBI_PMU_FW_SFENCE_VMA_ASID_RCVD = 13,

    SBI_PMU_FW_HFENCE_GVMA_SENT = 14,
    SBI_PMU_FW_HFENCE_GVMA_RCVD = 15,
    SBI_PMU_FW_HFENCE_GVMA_VMID_SENT = 16,
    SBI_PMU_FW_HFENCE_GVMA_VMID_RCVD = 17,

    SBI_PMU_FW_HFENCE_VVMA_SENT = 18,
    SBI_PMU_FW_HFENCE_VVMA_RCVD = 19,
    SBI_PMU_FW_HFENCE_VVMA_ASID_SENT = 20,
    SBI_PMU_FW_HFENCE_VVMA_ASID_RCVD = 21,
    SBI_PMU_FW_MAX,
};

/* SBI PMU event types */
enum sbi_pmu_event_type {
    SBI_PMU_EVENT_TYPE_HW = 0x0,
    SBI_PMU_EVENT_TYPE_CACHE = 0x1,
    SBI_PMU_EVENT_TYPE_RAW = 0x2,
    SBI_PMU_EVENT_TYPE_FW = 0xf,
};

/* SBI PMU event types */
enum sbi_pmu_ctr_type {
    SBI_PMU_CTR_TYPE_HW = 0x0,
    SBI_PMU_CTR_TYPE_FW,
};

enum sbi_ext_dbcn {
    SBI_EXT_DBCN_CONSOLE_WRITE = 0x0,
    SBI_EXT_DBCN_CONSOLE_READ = 0x1,
    SBI_EXT_DBCN_CONSOLE_WRITE_BYTE = 0x2

};

static inline struct sbiret sbi_ecall(enum sbi_ext_id ext, int fid, uint64_t arg0, uint64_t arg1, uint64_t arg2, uint64_t arg3, uint64_t arg4, uint64_t arg5) {
    struct sbiret ret;
    register uint64_t a0 asm("a0") = (uint64_t)(arg0);
    register uint64_t a1 asm("a1") = (uint64_t)(arg1);
    register uint64_t a2 asm("a2") = (uint64_t)(arg2);
    register uint64_t a3 asm("a3") = (uint64_t)(arg3);
    register uint64_t a4 asm("a4") = (uint64_t)(arg4);
    register uint64_t a5 asm("a5") = (uint64_t)(arg5);
    register uint64_t a6 asm("a6") = (uint64_t)(fid);
    register uint64_t a7 asm("a7") = (uint64_t)(ext);
    asm volatile("ecall" : "+r"(a0), "+r"(a1) : "r"(a2), "r"(a3), "r"(a4), "r"(a5), "r"(a6), "r"(a7) : "memory");
    register uint64_t sp asm("sp");
    ret.error = (long)a0;
    ret.value = (long)a1;
    return ret;
}

// PMU extension
static inline long sbi_pmu_num_counters(void) {
    struct sbiret r = sbi_ecall(SBI_EXT_PMU, SBI_EXT_PMU_NUM_COUNTERS, 0, 0, 0, 0, 0, 0);
    return r.value;
}
static inline struct sbiret sbi_pmu_counter_get_info(struct sbiret *ret, uint64_t counter_idx) {
    return sbi_ecall(SBI_EXT_PMU, SBI_EXT_PMU_COUNTER_GET_INFO, counter_idx, 0, 0, 0, 0, 0);
}
static inline struct sbiret sbi_pmu_counter_config_matching(struct sbiret *ret, uint64_t counter_idx_base, uint64_t counter_idx_mask, uint64_t config_flags, uint64_t event_idx, uint64_t event_data) {
    return sbi_ecall(SBI_EXT_PMU, SBI_EXT_PMU_COUNTER_CFG_MATCH, counter_idx_base, counter_idx_mask, config_flags, event_idx, event_data, 0);
}
static inline struct sbiret sbi_pmu_counter_start(struct sbiret *ret, uint64_t counter_idx_base, uint64_t counter_idx_mask, uint64_t start_flags, uint64_t initial_value) {
    return sbi_ecall(SBI_EXT_PMU, SBI_EXT_PMU_COUNTER_START, counter_idx_base, counter_idx_mask, start_flags, initial_value, 0, 0);
}
static inline struct sbiret sbi_pmu_counter_stop(struct sbiret *ret, uint64_t counter_idx_base, uint64_t counter_idx_mask, uint64_t stop_flags) {
    return sbi_ecall(SBI_EXT_PMU, SBI_EXT_PMU_COUNTER_STOP, counter_idx_base, counter_idx_mask, stop_flags, 0, 0, 0);
}

// RFENCE extension
static inline struct sbiret sbi_remote_fence_i(struct sbiret *ret, uint64_t mask, uint64_t base) {
    return sbi_ecall(SBI_EXT_RFENCE, SBI_EXT_RFENCE_REMOTE_FENCE_I, mask, base, 0, 0, 0, 0);
}
static inline struct sbiret sbi_remote_sfence_vma(struct sbiret *ret, uint64_t mask, uint64_t base, uint64_t start_addr, uint64_t size) {
    return sbi_ecall(SBI_EXT_RFENCE, SBI_EXT_RFENCE_REMOTE_SFENCE_VMA, mask, base, start_addr, size, 0, 0);
}
static inline struct sbiret sbi_remote_sfence_vma_asid(struct sbiret *ret, uint64_t mask, uint64_t base, uint64_t start_addr, uint64_t size, uint64_t asid) {
    return sbi_ecall(SBI_EXT_RFENCE, SBI_EXT_RFENCE_REMOTE_SFENCE_VMA_ASID, mask, base, start_addr, size, asid, 0);
}
static inline struct sbiret sbi_remote_hfence_gvma(struct sbiret *ret, uint64_t mask, uint64_t base, uint64_t start_addr, uint64_t size) {
    return sbi_ecall(SBI_EXT_RFENCE, SBI_EXT_RFENCE_REMOTE_HFENCE_GVMA, mask, base, start_addr, size, 0, 0);
}
static inline struct sbiret sbi_remote_hfence_gvma_vmid(struct sbiret *ret, uint64_t mask, uint64_t base, uint64_t start_addr, uint64_t size, uint64_t vmid) {
    return sbi_ecall(SBI_EXT_RFENCE, SBI_EXT_RFENCE_REMOTE_HFENCE_GVMA_VMID, mask, base, start_addr, size, vmid, 0);
}
static inline struct sbiret sbi_remote_hfence_vvma(struct sbiret *ret, uint64_t mask, uint64_t base, uint64_t start_addr, uint64_t size) {
    return sbi_ecall(SBI_EXT_RFENCE, SBI_EXT_RFENCE_REMOTE_HFENCE_VVMA, mask, base, start_addr, size, 0, 0);
}
static inline struct sbiret sbi_remote_hfence_vvma_asid(struct sbiret *ret, uint64_t mask, uint64_t base, uint64_t start_addr, uint64_t size, uint64_t asid) {
    return sbi_ecall(SBI_EXT_RFENCE, SBI_EXT_RFENCE_REMOTE_HFENCE_VVMA_ASID, mask, base, start_addr, size, asid, 0);
}

#endif // HMODE_SBI_H

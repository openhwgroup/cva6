#include <stdint.h>
#include <stdio.h>

#define CSR_MHPMEVENT3 0x323
#define CSR_MHPMEVENT4 0x324
#define CSR_MHPMEVENT5 0x325

/* === CSR helpers === */
#define stringify(x) #x
#define csr_write(csr, val) \
    asm volatile("csrw " stringify(csr) ", %0" :: "rK"(val))
#define csr_read(csr) ({ \
    uint32_t _v; \
    asm volatile("csrr %0, " stringify(csr) : "=r"(_v)); \
    _v; \
})

/* === Control functions === */
static inline void set_enclave_id(uint8_t id)
{
    uint32_t v = ((uint32_t)(id & 0xF)) << 23;
    csr_write(CSR_MHPMEVENT4, v);
}

static inline void set_secure_flag(int enable)
{
    if (enable)
        csr_write(CSR_MHPMEVENT3, (1u << 23));
    else
        csr_write(CSR_MHPMEVENT3, 0);
}

static inline void hc_flush_enclave(int enable)
{
    if (enable)
        csr_write(CSR_MHPMEVENT5, (1u << 23));
    else
        csr_write(CSR_MHPMEVENT5, 0);
}

/* === Simple workload === */
void fill_region(volatile char *buf, int size, const char *label)
{
    printf("[INFO] Filling region for %s...\n", label);
    for (int i = 0; i < size; i++) {
        buf[i] = (char)('A' + (i % 26));
    }
}

void verify_region(volatile char *buf, int size, const char *label)
{
    printf("[INFO] Verifying region for %s...\n", label);
    for (int i = 0; i < size; i++) {
        if (buf[i] != (char)('A' + (i % 26))) {
            printf("[ERROR] Data mismatch in %s at offset %d!\n", label, i);
            return;
        }
    }
    printf("[OK] %s verification passed.\n", label);
}

/* === Main test sequence === */
int main(void)
{
    static volatile char enclaveA_buf[64];
    static volatile char enclaveB_buf[64];

    /* STEP 1: Create Enclave A */
    set_enclave_id(1);
    set_secure_flag(1);
    fill_region(enclaveA_buf, 64, "Enclave A");
    verify_region(enclaveA_buf, 64, "Enclave A");

    /* STEP 2: Switch to Enclave B */
    set_enclave_id(2);
    fill_region(enclaveB_buf, 64, "Enclave B");
    verify_region(enclaveB_buf, 64, "Enclave B");

    /* STEP 3: Reactivate Enclave A */
    set_enclave_id(1);
    verify_region(enclaveA_buf, 64, "Enclave A");

    /* STEP 4: Flush Enclave A (Destruction) */
    hc_flush_enclave(1);   
    /*set_secure_flag(0);
    set_enclave_id(0);
    hc_flush_enclave(0);*/
    return 0;
}

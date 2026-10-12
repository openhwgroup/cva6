#include <stdint.h>
#include <stdio.h>

/* CSR numbers*/
#define CSR_MHPMEVENT3 0x323
#define CSR_MHPMEVENT4 0x324
#define CSR_MHPMEVENT5 0x325

/* CSR helpers */
#define stringify(x) #x
#define csr_write(csr, val) \
    asm volatile("csrw " stringify(csr) ", %0" :: "rK"(val))
#define csr_read(csr) ({ \
    uint32_t _v; \
    asm volatile("csrr %0, " stringify(csr) : "=r"(_v)); \
    _v; \
})

/* Paramètres (adapte selon ta L1/L2 pour forcer évictions) */
#define LINE_SIZE       64
#define L1_SIZE_BYTES   (16 * 1024) /* exemple L1 = 16KiB */
#define L1_ASSOC        4
#define SET_SPAN_L1     (LINE_SIZE * (L1_SIZE_BYTES / (LINE_SIZE * L1_ASSOC)))
/* Taille de buffer : faire grand pour saturer (par enclave) */
#define SIZE_PER_ENCL_BYTES (L1_ASSOC * SET_SPAN_L1) /* taille qui couvre une "partition" d'un ensemble */
#define SIZE_PER_ENCL (SIZE_PER_ENCL_BYTES) /* bytes */

/* On utilise buffers statiques alignés implicitement ; volatile pour empêcher optimisations */
static volatile uint8_t enclaveA_buf[SIZE_PER_ENCL];
static volatile uint8_t enclaveB_buf[SIZE_PER_ENCL];
static volatile uint8_t normal_buf[SIZE_PER_ENCL];

/* Set enclave id (bits 23..26 or 23..25 depending on your encoding) */
static inline void set_enclave_id(uint8_t id)
{
    uint32_t v = ((uint32_t)(id & 0xF)) << 23;
    csr_write(CSR_MHPMEVENT4, v);
}

/* Enable/disable secure flag = countermeasure activation (bit 23) */
static inline void set_secure_flag(int enable)
{
    if (enable)
        csr_write(CSR_MHPMEVENT3, (1u << 23));
    else
        csr_write(CSR_MHPMEVENT3, (0u << 23));
}

static inline void hc_flush_enclave(int enable) {
    if (enable)
        csr_write(CSR_MHPMEVENT5, (1u << 23));
    else
        csr_write(CSR_MHPMEVENT5, (0u << 23));
}

/* Small memory access helpers */
static inline void write_addr(volatile uint8_t *p, size_t off, uint8_t v) {
    p[off] = v;
    asm volatile("" :: "r"(p[off]) : "memory");
}
static inline uint8_t read_addr(volatile uint8_t *p, size_t off) {
    volatile uint8_t v = p[off];
    asm volatile("" :: "r"(v) : "memory");
    return v;
}

/* Fill region to touch all ways of the same set */
static void fill_region(volatile uint8_t *buf, int base_val, const char *who)
{
    /* touch WAYS lines that map to same set: stepping by SET_SPAN_L1 */
    for (int k = 0; k < L1_ASSOC; ++k) {
        size_t idx = (size_t)k * SET_SPAN_L1;
        write_addr(buf, idx, (uint8_t)(base_val + k));
        /* read back to ensure resident */
        (void)read_addr(buf, idx);
    }
}

/* Thrash region: repeatedly access same set to force replacements */
static void thrash_region(volatile uint8_t *buf, int loops, const char *who)
{
    volatile uint8_t sink = 0;
    for (int i = 0; i < loops; ++i) {
        for (int k = 0; k < (L1_ASSOC * 3); ++k) { /* 3x ways => pressure */
            size_t idx = (size_t)(k % L1_ASSOC) * SET_SPAN_L1;
            buf[idx] ^= (uint8_t)(i + k);
            sink ^= buf[idx];
        }
    }
}

/* read-check : read first line(s) to sample HIT vs MISS inference */
static void read_check(volatile uint8_t *buf, const char *who)
{
    uint8_t v0 = read_addr(buf, 0);
    uint8_t v1 = read_addr(buf, SET_SPAN_L1); /* another way */
}

/* main sequence describing the scenario */
int main(void)
{
    /* 0) normal app runs first and fills its region */
    set_enclave_id(0);     /* normal app (id 0) */
    set_secure_flag(0);
    fill_region(normal_buf, 0xA0, "NORMAL");

    /* 1) Enclave A runs and saturates cache */
    set_enclave_id(1);
    set_secure_flag(1);
    fill_region(enclaveA_buf, 10, "ENCLAVE_A");

    /* optionally thrash a bit to ensure allocation */
    thrash_region(enclaveA_buf, 100, "ENCLAVE_A_thrash_after_fill");
    read_check(enclaveA_buf, "ENCLAVE_A (after fill)");

    /* 2) Enclave B runs and saturates cache (potentially evict A) */
    /*set_enclave_id(2);
    set_secure_flag(1);
    fill_region(enclaveB_buf, 20, "ENCLAVE_B");*/

    /* big thrash to cause evictions of previous lines */
    /*thrash_region(enclaveB_buf, 200, "ENCLAVE_B_big_thrash");
    read_check(enclaveB_buf, "ENCLAVE_B (after thrash)");*/

    /* 3) destroy Enclave B: simply stop touching B region and 'exit' B */
    hc_flush_enclave(1);

    /* small idle loop to simulate delay where B is inactive; */
    //for (volatile int i=0; i<100; ++i) { asm volatile("" ::: "memory"); }
    
    /* 4) Resume Enclave A: check whether its lines survived or were evicted */
    //set_enclave_id(1);
    //set_secure_flag(1);
    /* read sample before re-writing to try detect if lines were evicted */
    //read_check(enclaveA_buf, "ENCLAVE_A (resume, pre-fill read)");

    /* re-touch A (force rewriting its set) */
    //fill_region(enclaveA_buf, 10, "ENCLAVE_A (resume refill)");
    //read_check(enclaveA_buf, "ENCLAVE_A (resume after refill)");

    return 0;
}
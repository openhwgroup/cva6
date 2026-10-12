#include <stdint.h>
#include <stdio.h>

/* CSR numbers */
#define CSR_MHPMEVENT3 0x323
#define CSR_MHPMEVENT4 0x324

/* CSR helpers */
#define stringify(x) #x
#define csr_write(csr, val) \
    asm volatile("csrw " stringify(csr) ", %0" :: "rK"(val))

static inline void set_enclave_id(uint8_t id)
{
    uint32_t v = ((uint32_t)(id & 0xF)) << 23;
    csr_write(CSR_MHPMEVENT4, v);
}

static inline void set_secure_flag(void)
{
    csr_write(CSR_MHPMEVENT3, (1u << 23));
}

static inline uint32_t rdcycle(void)
{
    uint64_t v;
    asm volatile("rdcycle %0" : "=r"(v));
    return v;
}

static inline void fence_rw(void) { asm volatile("fence rw, rw" ::: "memory"); }
static inline void keep_u32(uint32_t x) { asm volatile("" :: "r"(x) : "memory"); }

int main(void)
{
    //set_enclave_id(1);
    //set_secure_flag();

    static volatile uint32_t line __attribute__((aligned(64))) = 0x12345678;
    volatile uint32_t sink = 0;

    const uint32_t N = 100;   

    /* Warm-up load (NOT timed): ensures next loads are hits */
    sink += line;
    fence_rw();

    /* Timed region: ONLY hits (steady-state) */
    uint64_t t0 = rdcycle();
    for (uint32_t i = 0; i < N; i++) {
        sink += line;
    }
    uint64_t t1 = rdcycle();
    fence_rw();

    keep_u32(sink);

    uint64_t cycles = t1 - t0;

    printf("\nHit: total=%llu cycles, per_load=%llu + %llu/%u cycles, sink=%u (0x%08x)\n",
           (unsigned long long)cycles,
           (unsigned long long)(cycles / N),
           (unsigned long long)(cycles % N),
           (unsigned)N,
           (unsigned)sink, (unsigned)sink);

    return 0;
}
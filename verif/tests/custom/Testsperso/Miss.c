#include <stdint.h>
#include <stdio.h>

/* -------- cycle counter -------- */
static inline uint64_t rdcycle(void) {
  uint64_t v;
  asm volatile ("csrr %0, mcycle" : "=r"(v));
  return v;
}

/* -------- enclave CSRs -------- */
#define CSR_MHPMEVENT3 0x323
#define CSR_MHPMEVENT4 0x324
#define stringify(x) #x
#define csr_write(csr, val) asm volatile("csrw " stringify(csr) ", %0" :: "rK"(val))

static inline void set_enclave_id(uint8_t id) {
  uint64_t v = ((uint64_t)(id & 0xF)) << 23;
  csr_write(CSR_MHPMEVENT4, v);
}
static inline void secure_on(void) { csr_write(CSR_MHPMEVENT3, (1u << 23)); }

#define FENCE() asm volatile("fence rw, rw" ::: "memory")

static inline void touch8(volatile uint8_t *p, volatile uint32_t *sink) {
  *sink += *p;
  asm volatile("" ::: "memory");
}

/* -------- Cache params (must match your RTL) -------- */
#define WAYS       8
#define LINE_SIZE  16      /* keep if your RTL line size is 16; else put 64 */
#define SETS       256
#define STRIDE     (SETS * LINE_SIZE)

/* allocate WAYS+2 lines (one for "normal miss", one for "bypass candidate") */
static volatile uint8_t region[(WAYS + 2) * STRIDE] __attribute__((aligned(STRIDE)));

static inline uint64_t burst_load(volatile uint8_t *p, uint32_t reps) {
  volatile uint32_t sink = 0;
  FENCE();
  uint64_t t0 = rdcycle();
  for (uint32_t i = 0; i < reps; i++) {
    touch8(p, &sink);
  }
  uint64_t t1 = rdcycle();
  FENCE();
  /* prevent optimize */
  asm volatile("" :: "r"(sink) : "memory");
  return t1 - t0;
}

int main(void) {
  volatile uint8_t *base = region;

  volatile uint8_t *E1[WAYS];
  for (int i = 0; i < WAYS; i++) {
    E1[i] = base + (i * STRIDE);
  }

  volatile uint8_t *MISS_NORMAL = base + ((WAYS + 0) * STRIDE);
  volatile uint8_t *BYPASS_CAND = base + ((WAYS + 1) * STRIDE);

  printf("2-enclave same-set test (miss vs bypass)\n");
  printf("base=%p stride=%u\n", (void*)base, (unsigned)STRIDE);

  /* ---------- Enclave 1: fill all ways of the set ---------- */
  set_enclave_id(1);
  secure_on();
  FENCE();
  volatile uint32_t tmp = 0;
  for (int i = 0; i < WAYS; i++) touch8(E1[i], &tmp);
  FENCE();

  /* ---------- Enclave 2: measure normal miss (should insert) ---------- */
  set_enclave_id(2);
  secure_on();
  FENCE();

  /* Ensure MISS_NORMAL not already touched in EID2 */
  uint64_t miss_b1 = burst_load(MISS_NORMAL, 64);
  uint64_t miss_b2 = burst_load(MISS_NORMAL, 64);

  /* ---------- Re-fill again with EID1 (keep set full) ---------- */
  set_enclave_id(1);
  secure_on();
  FENCE();
  for (int i = 0; i < WAYS; i++) touch8(E1[i], &tmp);
  FENCE();

  /* ---------- Enclave 2: measure bypass candidate ---------- */
  set_enclave_id(2);
  secure_on();
  FENCE();

  uint64_t by_b1 = burst_load(BYPASS_CAND, 64);
  uint64_t by_b2 = burst_load(BYPASS_CAND, 64);

  printf("MISS_NORMAL bursts (64 loads): b1=%llu, b2=%llu (b2 should be smaller if inserted)\n",
         (unsigned long long)miss_b1, (unsigned long long)miss_b2);

  printf("BYPASS_CAND bursts (64 loads): b1=%llu, b2=%llu (if bypass, b2 ~ b1)\n",
         (unsigned long long)by_b1, (unsigned long long)by_b2);

  return 0;
}
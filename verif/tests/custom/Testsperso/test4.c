#include <stdint.h>
#include <stdio.h>

/* ----------- CSRs standards ----------- */
static inline uint64_t rdcycle(void) {
  uint64_t v;
  asm volatile ("csrr %0, mcycle" : "=r"(v));
  return v;
}

/* ----------- Tes CSRs “enclave id / secure” ----------- */
#define CSR_MHPMEVENT3 0x323
#define CSR_MHPMEVENT4 0x324
#define stringify(x) #x
#define csr_write(csr, val) asm volatile("csrw " stringify(csr) ", %0" :: "rK"(val))

static inline void set_enclave_id(uint8_t id) {
  uint64_t v = ((uint64_t)(id & 0xF)) << 23;
  csr_write(CSR_MHPMEVENT4, v);
}
static inline void secure_on(void) { csr_write(CSR_MHPMEVENT3, (1u << 23)); }

/* ----------- Cache params ----------- */
#define WAYS       8
#define LINE_SIZE  16
#define SETS       256
#define STRIDE     (SETS * LINE_SIZE)  

#define FENCE() asm volatile("fence rw, rw" ::: "memory")

#define TOUCH(p) do {                \
  volatile uint8_t _v = *(p);        \
  asm volatile("" ::: "memory");     \
  (void)_v;                          \
} while (0)


static volatile uint8_t region[(WAYS + 1) * STRIDE] __attribute__((aligned(STRIDE)));

int main(void) {
  volatile uint8_t *base = region;

  volatile uint8_t *E1[WAYS];
  for (int i = 0; i < WAYS; i++) {
    E1[i] = base + (i * STRIDE);
  }
  volatile uint8_t *E2_X = base + (WAYS * STRIDE); /* 9e ligne congruente */

  printf("2-enclave same-set full-fill test\n");
  // Enclave 1 : remplit TOUTES les ways du set 
  set_enclave_id(1);
  secure_on();
  FENCE();

  for (int i = 0; i < WAYS; i++) {
    TOUCH(E1[i]);
  }
  FENCE();

  // Enclave 2 : accède à une nouvelle ligne congruente 
  set_enclave_id(2);
  secure_on();
  FENCE();

  TOUCH(E2_X);
  FENCE();

  printf("Done\n");
  return 0;
}

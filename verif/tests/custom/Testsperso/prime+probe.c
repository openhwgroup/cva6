// prime_probe_eviction_test_int.c
// Minimal : prime 8 ways -> victim 9th congruent line -> probe -> summary (INT ONLY: no floats)

#include <stdint.h>
#include <stddef.h>
#include <stdio.h>

/* === Config === */
#define TRACE_BUF_ADDR      0x80010000UL
#define TRACE_BUF_NTRACES   10
#define EVSET_SIZE          8
#define BIGBUF_ADDR         0x80020000UL
#define BIGBUF_SIZE         (1<<20)
#define LINE_SIZE_BYTES     16        // 128-bit line width => 16B
#define N_SETS              256
#define TARGET_SET          5
#define VICTIM_INTENSITY    20000     // augmenté pour forcer l’eviction
#define THRESH_MARGIN       8         // cycles au-dessus de la moyenne
#define THRESH_MIN          16        // plancher de sécurité

/* Globals */
volatile uint64_t *trace_buf = (volatile uint64_t *)TRACE_BUF_ADDR;
volatile uint8_t *bigbuf     = (volatile uint8_t *)BIGBUF_ADDR;
volatile uint8_t *evset[EVSET_SIZE];

/* Helpers */
static inline uint64_t rdcycle(void){ uint64_t c; asm volatile ("rdcycle %0":"=r"(c)); return c; }
static inline void do_nops(int n){ for (int i=0;i<n;i++) asm volatile("nop"); }
static inline void access_addr(volatile uint8_t *p){ volatile uint8_t t=*p; (void)t; }
static inline unsigned set_of(uintptr_t a){ return (unsigned)((a / LINE_SIZE_BYTES) % N_SETS); }

static inline uintptr_t pick_offset_for_set(uintptr_t base, unsigned target_set){
    for (uintptr_t off=0; off < (uintptr_t)N_SETS*LINE_SIZE_BYTES && off+LINE_SIZE_BYTES <= BIGBUF_SIZE; off+=LINE_SIZE_BYTES)
        if (set_of(base+off)==target_set) return off;
    return 0;
}

void build_evset(unsigned target_set){
    const uintptr_t STRIDE = (uintptr_t)N_SETS * LINE_SIZE_BYTES;
    uintptr_t base = (uintptr_t)bigbuf;
    uintptr_t off0 = pick_offset_for_set(base, target_set);
    uintptr_t a0   = base + off0;
    for (unsigned k=0;k<EVSET_SIZE;k++)
        evset[k] = (volatile uint8_t *)(a0 + (uintptr_t)k*STRIDE);
}

void prime_set(void){
    for (int i=0;i<EVSET_SIZE;i++) access_addr(evset[i]);
}

/* 9e adresse congruente dans le MEME set (k = EVSET_SIZE) */
void victim_access_9th(unsigned target_set){
    const uintptr_t STRIDE = (uintptr_t)N_SETS * LINE_SIZE_BYTES;
    uintptr_t base = (uintptr_t)bigbuf;
    uintptr_t off0 = pick_offset_for_set(base, target_set);
    uintptr_t a0   = base + off0;
    uintptr_t addr = a0 + (uintptr_t)EVSET_SIZE * STRIDE;
    volatile uint8_t *p = (volatile uint8_t *)addr;
    for (int r = 0; r < 50000; r++) {
        *p = (uint8_t)(r & 0xFF);
        asm volatile("" ::: "memory");
    }
}


void probe_and_store_once(int t){
    for (int i=0;i<EVSET_SIZE;i++){
        uint64_t t0 = rdcycle();
        access_addr(evset[i]);
        uint64_t t1 = rdcycle();
        trace_buf[(uint64_t)t*EVSET_SIZE + i] = (t1 - t0);
    }
}

/* Sanity: apercu 1ere ligne */
void dump_first_trace_row(void){
    if (TRACE_BUF_NTRACES < 1) return;
    for (int i=0;i<EVSET_SIZE;i++){
        uint64_t v = trace_buf[i];
        printf("TRACE 0000 %02d 0x%016llx (dec %llu)\n", i, (unsigned long long)v, (unsigned long long)v);
    }
}

/* Analyse ENTIER (pas de %f) */
void dump_evictions_and_summary_int(void){
    // 1) moyenne entière
    uint64_t sum = 0;
    int total = TRACE_BUF_NTRACES * EVSET_SIZE;
    for (int t=0;t<TRACE_BUF_NTRACES;t++)
        for (int i=0;i<EVSET_SIZE;i++)
            sum += trace_buf[(uint64_t)t*EVSET_SIZE + i];

    // moyenne entière arrondie: (sum + total/2) / total
    uint32_t avg = (total>0) ? (uint32_t)((sum + (uint64_t)(total/2)) / (uint64_t)total) : 0;
    int threshold = (int)avg + THRESH_MARGIN;
    if (threshold < THRESH_MIN) threshold = THRESH_MIN;

    // 2) compter les évictions et imprimer les hits > threshold
    int ev_count[EVSET_SIZE]; for (int i=0;i<EVSET_SIZE;i++) ev_count[i]=0;
    for (int t=0;t<TRACE_BUF_NTRACES;t++){
        for (int i=0;i<EVSET_SIZE;i++){
            uint64_t val = trace_buf[(uint64_t)t*EVSET_SIZE + i];
            if ((int)val > threshold){
                ev_count[i]++;
                // dé-commente si tu veux voir chaque éviction
                // printf("EVICT TRACE %04d %02d 0x%016llx (dec %llu)\n", t, i, (unsigned long long)val, (unsigned long long)val);
            }
        }
    }

    // 3) résumé (pourcentages entiers *100 / N)
    printf("AUTO THRESHOLD calc: avg=%u -> threshold=%d\n", avg, threshold);
    printf("=== EVICTION SUMMARY (int) ===\n");
    for (int i=0;i<EVSET_SIZE;i++){
        int pct = (TRACE_BUF_NTRACES>0) ? (ev_count[i]*100 / TRACE_BUF_NTRACES) : 0;
        printf("index %d: evictions=%d (%d%%)\n", i, ev_count[i], pct);
    }
}

int main(void){
    // bounds
    uintptr_t buf_start = (uintptr_t)trace_buf;
    uintptr_t buf_end   = buf_start + (TRACE_BUF_NTRACES * EVSET_SIZE * sizeof(uint64_t));
    uintptr_t big_start = (uintptr_t)bigbuf;
    printf("[INFO] trace_buf 0x%08lx..0x%08lx bigbuf 0x%08lx\n",
           (unsigned long)buf_start, (unsigned long)buf_end, (unsigned long)big_start);
    if (buf_end > big_start){
        printf("[ERR] trace buffer overlaps bigbuf\n");
        asm volatile("ebreak");
    }

    // Build + petit debug mapping concis
    build_evset(TARGET_SET);
    for (unsigned k=0;k<EVSET_SIZE;k++){
    }
    // 9e adresse (doit rester dans set TARGET_SET)
    {
        const uintptr_t STRIDE = (uintptr_t)N_SETS * LINE_SIZE_BYTES;
        uintptr_t a0 = ((uintptr_t)evset[0]) - ((uintptr_t)0)*STRIDE; // base alignée
        uintptr_t addr9 = a0 + (uintptr_t)EVSET_SIZE * STRIDE;
    }

    // Expériences
    for (int t=0;t<TRACE_BUF_NTRACES;t++){
        prime_set();
        victim_access_9th(TARGET_SET);
        asm volatile("fence");
        do_nops(16);
        probe_and_store_once(t);
    }

    // Sanity & résumé
    dump_first_trace_row();
    dump_evictions_and_summary_int();
    return 0;
}


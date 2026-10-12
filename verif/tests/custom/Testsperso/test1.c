#include <stdint.h>
#include <stdio.h>

/* CSR numbers */
#define CSR_MHPMEVENT3 0x323
#define CSR_MHPMEVENT4 0x324

/* CSR helpers */
#define stringify(x) #x
#define csr_write(csr, val) \
    asm volatile("csrw " stringify(csr) ", %0" :: "rK"(val))
#define csr_read(csr) ({ \
    uint32_t _v; \
    asm volatile("csrr %0, " stringify(csr) : "=r"(_v)); \
    _v; \
})

/* Configuration mémoire / test */
#define SIZE_PER_ENCL 1024     /* éléments par enclave */
static volatile uint8_t enclave1_buf[SIZE_PER_ENCL];
static volatile uint8_t enclave2_buf[SIZE_PER_ENCL];

/* Helpers pour régler l'ID d'enclave et le flag secure/countermeasure */
static inline void set_enclave_id(uint8_t id)
{
    uint32_t v = ((uint32_t)(id & 0xF)) << 23;
    csr_write(CSR_MHPMEVENT4, v);
}

static inline void set_secure_flag()
{
   csr_write(CSR_MHPMEVENT3, (1u << 23));
}

/* Tâche d'enclave : écrire puis relire sa zone */
static void enclave_task(uint8_t id, volatile uint8_t *buf, int value)
{
    set_enclave_id(id);
    set_secure_flag(); // activer "mode secure 

    /* Écrire des valeurs pour remplir des lignes cache */
    for (int i = 0; i < SIZE_PER_ENCL; ++i) {
        buf[i] = (uint8_t)(value + (i & 0xFF));
        asm volatile("" :: "r"(buf[i]) : "memory");
    }

    /* Relire une valeur clef*/
    volatile uint8_t sample = buf[0];
    asm volatile("" :: "r"(sample) : "memory"); /* ensure read happens */
}

/* Application normale*/
static void normal_app(void)
{
    for (int i = 0; i < SIZE_PER_ENCL; ++i) {
        enclave1_buf[i] = (uint8_t)(0xA0 + (i & 0xFF)); /* on réutilise la mémoire statique */
        asm volatile("" :: "r"(enclave1_buf[i]) : "memory");
    }
    volatile uint8_t sample = enclave1_buf[0];
    asm volatile("" :: "r"(sample) : "memory");
}

int main(void)
{

    /* 1) L'application normale */
    normal_app();

    /* 2) Enclave 1 s'exécute, écrit dans sa région (enclave1_buf) */
    enclave_task(1, enclave1_buf, 10);

    /* 3) Enclave 2 s'exécute, écrit dans sa région (enclave2_buf) */
    enclave_task(2, enclave2_buf, 20);

    return 0;
}
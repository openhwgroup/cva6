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


int main(void)
{
   /*Creation de l'Enclave*/
   //set_enclave_id(1);

   /*Activation de la contre-measure*/
   //set_secure_flag();

   /*Simple code*/
   int a=5;
   int b=3;
   int c=a+b;;
   
   printf("\nC est : %d\n",c);

 return 0;
}
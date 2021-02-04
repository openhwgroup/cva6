#include <stdio.h>
#include <stdlib.h>
#include <strings.h>

//#include "../../../core/custom/startup/support.h"
#include "./support.h"

/*
 * Possible misaligned scenarios for 32 bit bus
 *
 * 1 byte access
 *   - Never
 *
 * 2 byte access
 *   - Address & 0x1
 *   if 0x3, then 2 read32()
 *
 * 4 byte access
 *   - (Address & 0x1) | (Address & 0x2)
 *   then 2 read32()
 *
 * 8 byte access
 *   - (Address & 0x1) | (Address & 0x2) | (Address & 0x4)
 *   then 3 read32()
 *
 */

typedef unsigned char          u8;
typedef unsigned short         u16;
typedef unsigned int           u32;
typedef unsigned long long int u64;

// 64 bit printf fmt does not work
// use a union and print as 2x32bit
union {
    u32 u32v[2];
    u64 u64v;
} u64_32;

int main () {
    printf("Hello World\n");
    printf("Test misaligned load/store\n");

    u64 u64Load[4];    // 32 bytes
    u64 u64Store[4];   // 32 bytes
    u8  *pLoad  = (u8 *) u64Load;
    u8  *pStore = (u8 *) u64Store;

    u32 i;
    for (i=0; i<32; i++) {
        *(pLoad+i) = i;
    }
    u8  *cpa;
    u16 *spa;
    u32 *ipa;
    u64 *lpa;

    // Load Test
    cpa = pLoad;
    for (i=0; i<16; i++) {
        spa = (u16 *) cpa;
        ipa = (u32 *) cpa;
        lpa = (u64 *) cpa;

        printf("\n");
        printf("Store Index=%d off=%d\n", i, i%4);
        printf("  (u8  *) =               %02X\n", *cpa);
        printf("  (u16 *) =             %04X\n",   *spa);
        printf("  (u32 *) =         %08X\n",       *ipa);

        u64_32.u64v = *lpa;
        printf("  (u64 *) = %08X%08X\n",           u64_32.u32v[1], u64_32.u32v[0]);

        cpa++;
    }

    // Store Test
    cpa = pStore;
    for (i=0; i<16; i++) {
        spa = (u16 *) cpa;
        ipa = (u32 *) cpa;
        lpa = (u64 *) cpa;

        printf("\n");
        printf("Load Index=%d off=%d\n", i, i%4);

        bzero(cpa, 32);
        *spa = *(u16 *)(pLoad + i);
        printf("  (u16 *) =             %04X\n", *spa);

        bzero(cpa, 32);
        *ipa = *(u32 *)(pLoad + i);
        printf("  (u32 *) =         %08X\n",     *ipa);

        bzero(cpa, 32);
        *lpa = *(u64 *)(pLoad + i);
        u64_32.u64v = *lpa;
        printf("  (u64 *) = %08X%08X\n",         u64_32.u32v[1], u64_32.u32v[0]);

        cpa++;
    }

}

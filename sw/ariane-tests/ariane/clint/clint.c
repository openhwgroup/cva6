#include "util.h"

#define MTIMECMP_BASE 0x4000
#define MTIME_BASE 0xbff8

volatile uint64_t mtime;

int main (int argc, char** argv)
{
    // *(volatile int *) (CLINT_BASE + MTIME_BASE) = 0;

    mtime = *(volatile int *) (CLINT_BASE + MTIME_BASE);

    (*(volatile int *) (CLINT_BASE + MTIMECMP_BASE)) = mtime + 10;

    set_csr(mstatus, MSTATUS_MIE);
    set_csr(mie, MIP_MTIP);

    for(;;) {
        mtime = *(volatile int *) (CLINT_BASE + MTIME_BASE);
        // write_csr(mscratch, mtime);
        for (int i = 0; i < 2000; i++)  asm volatile ("nop");
    }
}

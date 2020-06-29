#include <stdio.h>
#include <stdlib.h>
#include <time.h>

#include "isr.h"
#include "matrix.h"

#define ERR_CODE_TEST_2      2
#define ERR_CODE_TEST_3      3
#define ERR_CODE_TEST_5      5

#define OUTPORT 0x10000000

#define RND_STALL_REG_10       0x16000028 // irq_mode
#define RND_STALL_REG_11       0x1600002C // irq_min_cycles
#define RND_STALL_REG_12       0x16000030 // irq_max_cycles
#define RND_STALL_REG_13       0x16000034 // irq_pc_trig
#define RND_STALL_REG_14       0x16000038 // irq_lines
#define RND_STALL_REG_15       0x1600003C // irq_linesx

#define IRQ_MODE_STD     1
#define IRQ_MODE_RND     2
#define IRQ_MODE_PC_TRIG 3
#define IRQ_MODE_SD      4

#define MSTATUS_MIE_BIT 3

#define IRQ_NUM 51
#define STD_IRQ_MASK 0xFFFF0888 // this accounts for non implemented irqs

#define SOFTWARE_IRQ_ID  3
#define TIMER_IRQ_ID     7
#define EXTERNAL_IRQ_ID  11
#define FAST0_IRQ_ID     16
#define FAST1_IRQ_ID     17
#define FAST2_IRQ_ID     18
#define FAST3_IRQ_ID     19
#define FAST4_IRQ_ID     20
#define FAST5_IRQ_ID     21
#define FAST6_IRQ_ID     22
#define FAST7_IRQ_ID     23
#define FAST8_IRQ_ID     24
#define FAST9_IRQ_ID     25
#define FAST10_IRQ_ID    26
#define FAST11_IRQ_ID    27
#define FAST12_IRQ_ID    28
#define FAST13_IRQ_ID    29
#define FAST14_IRQ_ID    30
#define FAST15_IRQ_ID    31
#define FAST16_IRQ_ID    32
#define FAST17_IRQ_ID    33
#define FAST18_IRQ_ID    34
#define FAST19_IRQ_ID    35
#define FAST20_IRQ_ID    36
#define FAST21_IRQ_ID    37
#define FAST22_IRQ_ID    38
#define FAST23_IRQ_ID    39
#define FAST24_IRQ_ID    40
#define FAST25_IRQ_ID    41
#define FAST26_IRQ_ID    42
#define FAST27_IRQ_ID    43
#define FAST28_IRQ_ID    44
#define FAST29_IRQ_ID    45
#define FAST30_IRQ_ID    46
#define FAST31_IRQ_ID    47
#define FAST32_IRQ_ID    48
#define FAST33_IRQ_ID    49
#define FAST34_IRQ_ID    50
#define FAST35_IRQ_ID    51
#define FAST36_IRQ_ID    52
#define FAST37_IRQ_ID    53
#define FAST38_IRQ_ID    54
#define FAST39_IRQ_ID    55
#define FAST40_IRQ_ID    56
#define FAST41_IRQ_ID    57
#define FAST42_IRQ_ID    58
#define FAST43_IRQ_ID    59
#define FAST44_IRQ_ID    60
#define FAST45_IRQ_ID    61
#define FAST46_IRQ_ID    62
#define FAST47_IRQ_ID    63

#define RND_IRQ_NUM        50
#define RND_IE_NUM         50
#define RND_IRQ_MIN_CYCLES 100
#define RND_IRQ_MAX_CYCLES 200

volatile uint32_t irq_processed           = 1;
volatile uint32_t irq_id                  = 0;
volatile uint64_t irq_pending             = 0;
volatile uint32_t irq_pending32_std       = 0;
volatile uint32_t irq_pending32_1         = 0;
volatile uint32_t irq_to_test32_std       = 0;
volatile uint32_t irq_to_test32_1         = 0;
volatile uint64_t prev_irq_pending        = 0;
volatile uint32_t prev_irq_pending32_std  = 0;
volatile uint32_t prev_irq_pending32_1    = 0;
volatile uint32_t first_irq_pending32_std = 0;
volatile uint32_t first_irq_pending32_1   = 0;
volatile uint32_t ie_mask32_std           = 0;
volatile uint32_t ie_mask32_1             = 0;
volatile uint32_t mmstatus                = 0;
volatile uint32_t bit_to_set              = 0;
volatile uint32_t irq_mode                = 0;

uint32_t IRQ_ID_PRIORITY [IRQ_NUM] =
{
    FAST47_IRQ_ID   ,
    FAST46_IRQ_ID   ,
    FAST45_IRQ_ID   ,
    FAST44_IRQ_ID   ,
    FAST43_IRQ_ID   ,
    FAST42_IRQ_ID   ,
    FAST41_IRQ_ID   ,
    FAST40_IRQ_ID   ,
    FAST39_IRQ_ID   ,
    FAST38_IRQ_ID   ,
    FAST37_IRQ_ID   ,
    FAST36_IRQ_ID   ,
    FAST35_IRQ_ID   ,
    FAST34_IRQ_ID   ,
    FAST33_IRQ_ID   ,
    FAST32_IRQ_ID   ,
    FAST31_IRQ_ID   ,
    FAST30_IRQ_ID   ,
    FAST29_IRQ_ID   ,
    FAST28_IRQ_ID   ,
    FAST27_IRQ_ID   ,
    FAST26_IRQ_ID   ,
    FAST25_IRQ_ID   ,
    FAST24_IRQ_ID   ,
    FAST23_IRQ_ID   ,
    FAST22_IRQ_ID   ,
    FAST21_IRQ_ID   ,
    FAST20_IRQ_ID   ,
    FAST19_IRQ_ID   ,
    FAST18_IRQ_ID   ,
    FAST17_IRQ_ID   ,
    FAST16_IRQ_ID   ,
    FAST15_IRQ_ID   ,
    FAST14_IRQ_ID   ,
    FAST13_IRQ_ID   ,
    FAST12_IRQ_ID   ,
    FAST11_IRQ_ID   ,
    FAST10_IRQ_ID   ,
    FAST9_IRQ_ID    ,
    FAST8_IRQ_ID    ,
    FAST7_IRQ_ID    ,
    FAST6_IRQ_ID    ,
    FAST5_IRQ_ID    ,
    FAST4_IRQ_ID    ,
    FAST3_IRQ_ID    ,
    FAST2_IRQ_ID    ,
    FAST1_IRQ_ID    ,
    FAST0_IRQ_ID    ,
    EXTERNAL_IRQ_ID ,
    SOFTWARE_IRQ_ID ,
    TIMER_IRQ_ID
};


// macro to print out a variable as binary
#define PRINTF_BINARY_PATTERN_INT8 "%c%c%c%c%c%c%c%c"
#define PRINTF_BYTE_TO_BINARY_INT8(i)    \
    (((i) & 0x80ll) ? '1' : '0'), \
    (((i) & 0x40ll) ? '1' : '0'), \
    (((i) & 0x20ll) ? '1' : '0'), \
    (((i) & 0x10ll) ? '1' : '0'), \
    (((i) & 0x08ll) ? '1' : '0'), \
    (((i) & 0x04ll) ? '1' : '0'), \
    (((i) & 0x02ll) ? '1' : '0'), \
    (((i) & 0x01ll) ? '1' : '0')

#define PRINTF_BINARY_PATTERN_INT16 \
    PRINTF_BINARY_PATTERN_INT8              PRINTF_BINARY_PATTERN_INT8
#define PRINTF_BYTE_TO_BINARY_INT16(i) \
    PRINTF_BYTE_TO_BINARY_INT8((i) >> 8),   PRINTF_BYTE_TO_BINARY_INT8(i)
#define PRINTF_BINARY_PATTERN_INT32 \
    PRINTF_BINARY_PATTERN_INT16             PRINTF_BINARY_PATTERN_INT16
#define PRINTF_BYTE_TO_BINARY_INT32(i) \
    PRINTF_BYTE_TO_BINARY_INT16((i) >> 16), PRINTF_BYTE_TO_BINARY_INT16(i)
#define PRINTF_BINARY_PATTERN_INT64    \
    PRINTF_BINARY_PATTERN_INT32             PRINTF_BINARY_PATTERN_INT32
#define PRINTF_BYTE_TO_BINARY_INT64(i) \
    PRINTF_BYTE_TO_BINARY_INT32((i) >> 32), PRINTF_BYTE_TO_BINARY_INT32(i)

/*R/W to memory*/

void writew(uint32_t val, volatile uint32_t *addr)
{
    asm volatile("sw %0, 0(%1)" : : "r"(val), "r"(addr));
}


uint32_t irq_served = 0;

#define FAST_IRQ_GENERIC(id)                                                        \
do {                                                                                \
    irq_id = id;                                                                    \
    if (irq_mode == IRQ_MODE_RND)                                                   \
    {                                                                               \
        asm volatile("csrr %0, 0x344": "=r" (irq_pending32_std));                   \
        asm volatile("csrr %0, 0x7D1": "=r" (irq_pending32_1));                     \
    }                                                                               \
    if (irq_id > 31)                                                                \
    { irq_pending32_1 &= (~(1 << irq_id)); }                                        \
    else                                                                            \
    { irq_pending32_std &= (~(1 << irq_id)); }                                      \
    writew(irq_pending32_std, RND_STALL_REG_14);                                    \
    writew(irq_pending32_1, RND_STALL_REG_15);                                      \
    if (irq_mode == IRQ_MODE_RND)                                                   \
    {                                                                               \
        irq_served++;                                                               \
        irq_mode = IRQ_MODE_STD;                                                    \
        writew(irq_mode, RND_STALL_REG_10);                                         \
        irq_mode = IRQ_MODE_RND;                                                    \
        writew(irq_mode, RND_STALL_REG_10);                                         \
    }                                                                               \
    else                                                                            \
    {                                                                               \
        asm volatile("csrr %0, mstatus": "=r" (mmstatus));                          \
        mmstatus &= (~(1 << 7));                                                    \
        asm volatile("csrw mstatus, %[mmstatus]" : : [mmstatus] "r" (mmstatus));    \
    }                                                                               \
} while(0)

void software_irq_handler(void)
{
    FAST_IRQ_GENERIC(SOFTWARE_IRQ_ID);
}

void timer_irq_handler(void) //TODO: do this here
{
    FAST_IRQ_GENERIC(TIMER_IRQ_ID);
}

void external_irq_handler(void)
{
    FAST_IRQ_GENERIC(EXTERNAL_IRQ_ID);
}

void fast0_irq_handler(void)
{
    FAST_IRQ_GENERIC(FAST0_IRQ_ID);
}

void fast1_irq_handler(void)
{
    FAST_IRQ_GENERIC(FAST1_IRQ_ID);
}

void fast2_irq_handler(void)
{
    FAST_IRQ_GENERIC(FAST2_IRQ_ID);
}

void fast3_irq_handler(void)
{
    FAST_IRQ_GENERIC(FAST3_IRQ_ID);
}

void fast4_irq_handler(void)
{
    FAST_IRQ_GENERIC(FAST4_IRQ_ID);
}

void fast5_irq_handler(void)
{
    FAST_IRQ_GENERIC(FAST5_IRQ_ID);
}

void fast6_irq_handler(void)
{
    FAST_IRQ_GENERIC(FAST6_IRQ_ID);
}

void fast7_irq_handler(void)
{
    FAST_IRQ_GENERIC(FAST7_IRQ_ID);
}

void fast8_irq_handler(void)
{
    FAST_IRQ_GENERIC(FAST8_IRQ_ID);
}

void fast9_irq_handler(void)
{
    FAST_IRQ_GENERIC(FAST9_IRQ_ID);
}

void fast10_irq_handler(void)
{
    FAST_IRQ_GENERIC(FAST10_IRQ_ID);
}

void fast11_irq_handler(void)
{
    FAST_IRQ_GENERIC(FAST11_IRQ_ID);
}

void fast12_irq_handler(void)
{
    FAST_IRQ_GENERIC(FAST12_IRQ_ID);
}

void fast13_irq_handler(void)
{
    FAST_IRQ_GENERIC(FAST13_IRQ_ID);
}

void fast14_irq_handler(void)
{
    FAST_IRQ_GENERIC(FAST14_IRQ_ID);
}

void fast15_irq_handler(void)
{
    FAST_IRQ_GENERIC(FAST15_IRQ_ID);
}

void fast16_irq_handler(void)
{
    FAST_IRQ_GENERIC(FAST16_IRQ_ID);
}

void fast17_irq_handler(void)
{
    FAST_IRQ_GENERIC(FAST17_IRQ_ID);
}

void fast18_irq_handler(void)
{
    FAST_IRQ_GENERIC(FAST18_IRQ_ID);
}

void fast19_irq_handler(void)
{
    FAST_IRQ_GENERIC(FAST19_IRQ_ID);
}

void fast20_irq_handler(void)
{
    FAST_IRQ_GENERIC(FAST20_IRQ_ID);
}

void fast21_irq_handler(void)
{
    FAST_IRQ_GENERIC(FAST21_IRQ_ID);
}

void fast22_irq_handler(void)
{
    FAST_IRQ_GENERIC(FAST22_IRQ_ID);
}

void fast23_irq_handler(void)
{
    FAST_IRQ_GENERIC(FAST23_IRQ_ID);
}

void fast24_irq_handler(void)
{
    FAST_IRQ_GENERIC(FAST24_IRQ_ID);
}

void fast25_irq_handler(void)
{
    FAST_IRQ_GENERIC(FAST25_IRQ_ID);
}

void fast26_irq_handler(void)
{
    FAST_IRQ_GENERIC(FAST26_IRQ_ID);
}

void fast27_irq_handler(void)
{
    FAST_IRQ_GENERIC(FAST27_IRQ_ID);
}

void fast28_irq_handler(void)
{
    FAST_IRQ_GENERIC(FAST28_IRQ_ID);
}

void fast29_irq_handler(void)
{
    FAST_IRQ_GENERIC(FAST29_IRQ_ID);
}

void fast30_irq_handler(void)
{
    FAST_IRQ_GENERIC(FAST30_IRQ_ID);
}

void fast31_irq_handler(void)
{
    FAST_IRQ_GENERIC(FAST31_IRQ_ID);
}

void fast32_irq_handler(void)
{
    FAST_IRQ_GENERIC(FAST32_IRQ_ID);
}

void fast33_irq_handler(void)
{
    FAST_IRQ_GENERIC(FAST33_IRQ_ID);
}

void fast34_irq_handler(void)
{
    FAST_IRQ_GENERIC(FAST34_IRQ_ID);
}

void fast35_irq_handler(void)
{
    FAST_IRQ_GENERIC(FAST35_IRQ_ID);
}

void fast36_irq_handler(void)
{
    FAST_IRQ_GENERIC(FAST36_IRQ_ID);
}

void fast37_irq_handler(void)
{
    FAST_IRQ_GENERIC(FAST37_IRQ_ID);
}

void fast38_irq_handler(void)
{
    FAST_IRQ_GENERIC(FAST38_IRQ_ID);
}

void fast39_irq_handler(void)
{
    FAST_IRQ_GENERIC(FAST39_IRQ_ID);
}

void fast40_irq_handler(void)
{
    FAST_IRQ_GENERIC(FAST40_IRQ_ID);
}

void fast41_irq_handler(void)
{
    FAST_IRQ_GENERIC(FAST41_IRQ_ID);
}

void fast42_irq_handler(void)
{
    FAST_IRQ_GENERIC(FAST42_IRQ_ID);
}

void fast43_irq_handler(void)
{
    FAST_IRQ_GENERIC(FAST43_IRQ_ID);
}

void fast44_irq_handler(void)
{
    FAST_IRQ_GENERIC(FAST44_IRQ_ID);
}

void fast45_irq_handler(void)
{
    FAST_IRQ_GENERIC(FAST45_IRQ_ID);
}

void fast46_irq_handler(void)
{
    FAST_IRQ_GENERIC(FAST46_IRQ_ID);
}

void fast47_irq_handler(void)
{
    FAST_IRQ_GENERIC(FAST47_IRQ_ID);
}

uint32_t random_num(uint32_t upper_bound, uint32_t lower_bound)
{

    uint32_t random_num = *((int *)0x15001000);
    uint32_t num = (random_num  % (upper_bound - lower_bound + 1)) + lower_bound;
    return num;
}
void mstatus_enable(uint32_t bit_enabled)
{
    asm volatile("csrr %0, mstatus": "=r" (mmstatus));
    mmstatus |= (1 << bit_enabled);
    asm volatile("csrw mstatus, %[mmstatus]" : : [mmstatus] "r" (mmstatus));
}

void mstatus_disable(uint32_t bit_disabled)
{
    asm volatile("csrr %0, mstatus": "=r" (mmstatus));
    mmstatus &= (~(1 << bit_disabled));
    asm volatile("csrw mstatus, %[mmstatus]" : : [mmstatus] "r" (mmstatus));
}

// integer matrix multiplication
void mat_mult(uint32_t mat1[MAT_DIM][MAT_DIM], uint32_t mat2[MAT_DIM][MAT_DIM], uint32_t res[MAT_DIM][MAT_DIM])
{
    uint32_t i, j, k;
    for (i = 0; i < MAT_DIM; i++)
    {
        for (j = 0; j < MAT_DIM; j++)
        {
            res[i][j] = 0;
            for (k = 0; k < MAT_DIM; k++)
                res[i][j] += mat1[i][k] * mat2[k][j];
        }
    }
}

int main(int argc, char *argv[])
{
    printf("TEST 1 - TRIGGER ALL IRQS IN SEQUENCE: ");

    // Enable all mie (need to store)
    ie_mask32_std = 0xFFFFFFFF;
    ie_mask32_1   = 0xFFFFFFFF;

    asm volatile("csrw 0x304, %[ie_mask32_std]"
                  : : [ie_mask32_std] "r" (ie_mask32_std));
    asm volatile("csrw 0x7D0, %[ie_mask32_1]"
                  : : [ie_mask32_1] "r" (ie_mask32_1));

    // software defined irq gen mode
    writew(IRQ_MODE_SD, RND_STALL_REG_10);

    // disable mstatues.mie
    mstatus_disable(MSTATUS_MIE_BIT);

    for (int i = 32; i < IRQ_NUM; i++)
    {
        // add new pending irq
        if (IRQ_ID_PRIORITY[i] > 31)
        {
            irq_pending32_1 |= (1 << IRQ_ID_PRIORITY[i]);
        }
        else
        {
            irq_pending32_std |= (1 << IRQ_ID_PRIORITY[i]);
        }

        prev_irq_pending32_std = irq_pending32_std;
        prev_irq_pending32_1 = irq_pending32_1;
        writew(irq_pending32_std, RND_STALL_REG_14);
        writew(irq_pending32_1, RND_STALL_REG_15);

        // enable mstatus.mie
        mstatus_enable(MSTATUS_MIE_BIT);

        // wait for the irq to be served
        while(prev_irq_pending32_std == irq_pending32_std && prev_irq_pending32_1 == irq_pending32_1);

        // irq_id sampling and testing
        if(IRQ_ID_PRIORITY[i] != irq_id)
        {
            printf("\nERR: IRQ served in wrong order %d %d\n", IRQ_ID_PRIORITY[i], irq_id);
            return -1;
        }
    };

    printf("OK\n");

    // TODO: needs to make sure preivous test finished

    //-------------------------------------------------------------------------------------------------------------------------------------------
    //-------------------------------------------------------------------------------------------------------------------------------------------

    //////////////////////
    // All IRQS AT ONCE //
    //////////////////////

    // Test 2 is a test where the core is stressed:
    // words are generated:
    // - all irqs are triggered at the same time
    // - all irqs are enabled
    // We expect the core to serve them one after the oteher
    // in the correct priority order

    printf("TEST 2 - TRIGGER ALL IRQS AT ONCE: ");

    // Enable all mie (need to store)
    ie_mask32_std = 0xFFFFFFFF;
    ie_mask32_1   = 0xFFFFFFFF;

    asm volatile("csrw 0x304, %[ie_mask32_std]"
                  : : [ie_mask32_std] "r" (ie_mask32_std));
    asm volatile("csrw 0x7D0, %[ie_mask32_1]"
                  : : [ie_mask32_1] "r" (ie_mask32_1));

    // Multiple interrupts at a time
    irq_pending32_1   = 0xFFFFFFFF;
    irq_pending32_std = 0xFFFFFFFF;

    // disable mstatues.mie
    mstatus_disable(MSTATUS_MIE_BIT);

    // for this test we only write once
    writew(irq_pending32_1, RND_STALL_REG_15);
    writew(irq_pending32_std, RND_STALL_REG_14);

    for (int i = 0; i < IRQ_NUM; i++)
    {
        // sample irq_pending
        prev_irq_pending32_std = irq_pending32_std;
        prev_irq_pending32_1   = irq_pending32_1;

        // enable mstatus.mie
        mstatus_enable(MSTATUS_MIE_BIT);

        // wait for nex irq to be served
        while(prev_irq_pending32_std == irq_pending32_std && prev_irq_pending32_1 == irq_pending32_1);

        // irq_id sampling and testing
        if(IRQ_ID_PRIORITY[i] != irq_id)
        {
            printf("\nERR: IRQ served in wrong order %d %d\n", IRQ_ID_PRIORITY[i], irq_id);
            return ERR_CODE_TEST_2;
        }
    }
    printf("OK\n");

    //-------------------------------------------------------------------------------------------------------------------------------------------
    //-------------------------------------------------------------------------------------------------------------------------------------------

    printf("TEST 3 - RANDOMIZE: "); //TODO: improve messages

    ///////////////////////////////
    // Random test with masking  //
    ///////////////////////////////

    // Test 3 is a random test where two 32 bit-wide
    // words are generated:
    // - a mask (rnd_ie_mask)
    // - and a value for the irq_pending
    //
    //

    irq_processed     = 1;
    irq_id            = 0;
    ie_mask32_1   = 0;
    irq_pending32_1   = 0;
    ie_mask32_std = 0;
    irq_pending32_std = 0;

    // build ie word randomly
    for (int i = 0; i < RND_IE_NUM; ++i)
    {
        // todo here we can set to 1 irqs already set
        bit_to_set = random_num(63, 0);
        if (bit_to_set > 31)
        {
            ie_mask32_1   |= (1 << bit_to_set);
        }
        else
        {
            ie_mask32_std |= (1 << bit_to_set);
        }
    }

    // mask to consider only implemented irqs
    ie_mask32_std = ie_mask32_std & STD_IRQ_MASK;

    // write the mask to mie
    asm volatile("csrw 0x304, %[ie_mask32_std]" : : [ie_mask32_std] "r" (ie_mask32_std));
    asm volatile("csrw 0x7D0, %[ie_mask32_1]" : : [ie_mask32_1] "r" (ie_mask32_1));


    // build irq word randomly
    for (int i = 0; i < RND_IRQ_NUM; ++i)
    {
        // todo here we can set to 1 also non-implemented irqs + irqs already set
        bit_to_set = random_num(63, 0);
        if (bit_to_set > 31)
        {
            irq_pending32_1   |= (1 << bit_to_set);
        }
        else
        {
            irq_pending32_std |= (1 << bit_to_set);
        }
    }

    // mask to consider only implemented irqs
    irq_pending32_std = irq_pending32_std & STD_IRQ_MASK;

    first_irq_pending32_std = irq_pending32_std;
    first_irq_pending32_1   = irq_pending32_1;

    uint32_t irq_to_serve_num = 0;
    uint32_t irq_served_num = 0;

    // build words to be tested
    for (int i = 0; i < 32; ++i)
    {
        if ((1 << i) & first_irq_pending32_1 & ie_mask32_1)
        {
            irq_to_test32_1 |= (1 << i);
        }

        if ((1 << i) & first_irq_pending32_std & ie_mask32_std)
        {
            irq_to_test32_std |= (1 << i);
        }

    }

    // disable mstatues.mie
    mstatus_disable(MSTATUS_MIE_BIT);

    // for this test we only write once
    writew(irq_pending32_1, RND_STALL_REG_15);
    writew(irq_pending32_std, RND_STALL_REG_14);

    for (int i = 0; i < IRQ_NUM; ++i)
    {
        if (IRQ_ID_PRIORITY[i] > 31 && (1 << IRQ_ID_PRIORITY[i] & irq_to_test32_1))
        {
            // sample irq_pending
            prev_irq_pending32_1 = irq_pending32_1;

            // enable mstatus.mie
            mstatus_enable(MSTATUS_MIE_BIT);

            // wait for next irq to be served
            while(prev_irq_pending32_1 == irq_pending32_1);
            //{ printf("waiting for irq %u \n", IRQ_ID_PRIORITY[i]);}

            // irq_id sampling and testing
            if(IRQ_ID_PRIORITY[i] != irq_id)
            {
                printf("\nERR: IRQ served in wrong order %d %d\n", IRQ_ID_PRIORITY[i], irq_id);
                return ERR_CODE_TEST_3;
            }
        }
        else if (IRQ_ID_PRIORITY[i] <= 31 && (1 << IRQ_ID_PRIORITY[i] & irq_to_test32_std))
        {
            // sample irq_pending
            prev_irq_pending32_std = irq_pending32_std;

            // enable mstatus.mie
            mstatus_enable(MSTATUS_MIE_BIT);

            // wait for next irq to be served
            while(prev_irq_pending32_std == irq_pending32_std);
            //{ printf("waiting for irq %u \n", IRQ_ID_PRIORITY[i]);}

            // irq_id sampling and testing
            if(IRQ_ID_PRIORITY[i] != irq_id)
            {
                printf("\nERR: IRQ served in wrong order %d %d\n", IRQ_ID_PRIORITY[i], irq_id);
                return ERR_CODE_TEST_3;
            }
        }
    }

    if(irq_pending32_std != ((~ie_mask32_std) & first_irq_pending32_std))
    {
        printf("\nERR: wrong number of irq served\n"
            "first_irq_pending32_std: "PRINTF_BINARY_PATTERN_INT32"\n"
            "ie_mask32_std:           "PRINTF_BINARY_PATTERN_INT32"\n"
            "irq_to_test32_std:       "PRINTF_BINARY_PATTERN_INT32"\n"
            "irq_pending32_std:       "PRINTF_BINARY_PATTERN_INT32"\n",
            PRINTF_BYTE_TO_BINARY_INT32(first_irq_pending32_std),
            PRINTF_BYTE_TO_BINARY_INT32(ie_mask32_std),
            PRINTF_BYTE_TO_BINARY_INT32(irq_to_test32_std),
            PRINTF_BYTE_TO_BINARY_INT32(irq_pending32_std));
        return ERR_CODE_TEST_3;
    }

    if(irq_pending32_1   != ((~ie_mask32_1) & first_irq_pending32_1))
    {
        printf("\nERR: wrong number of irq served\n"
            "first_irq_pending32_1: "PRINTF_BINARY_PATTERN_INT32"\n"
            "ie_mask32_1:           "PRINTF_BINARY_PATTERN_INT32"\n"
            "irq_to_test32_1:       "PRINTF_BINARY_PATTERN_INT32"\n"
            "irq_pending32_1:       "PRINTF_BINARY_PATTERN_INT32"\n",
            PRINTF_BYTE_TO_BINARY_INT32(first_irq_pending32_1),
            PRINTF_BYTE_TO_BINARY_INT32(ie_mask32_1),
            PRINTF_BYTE_TO_BINARY_INT32(irq_to_test32_1),
            PRINTF_BYTE_TO_BINARY_INT32(irq_pending32_1));
        return ERR_CODE_TEST_3;
    }
    printf("OK\n");

    // ///////////////////////////////
    // // TEST 4: PC Trig Test      //
    // ///////////////////////////////

    // // Test 4: a software interrupt (id = 3) is raised
    // // as the program counter assumes a desired value


    // printf("\nTEST 4: PC TRIG\n");

    // // Enable all mie (need to store)
    // regVal = 0xFFFFFFFF;
    // asm volatile("csrw 0x304, %[regVal]"
    //               : : [regVal] "r" (regVal));

    // // set desired PC value
    // writew(0x0000043e, RND_STALL_REG_13);
    // // switch to PC_TRIG mode
    // writew(IRQ_MODE_PC_TRIG, RND_STALL_REG_10);

    // mstatus_enable(MSTATUS_MIE_BIT);

    // mat_mult(mat1, mat2, res);

    // printf("\nResult matrix is\n");
    // for (int i = 0; i < MAT_DIM; i++)
    // {
    //     // mstatus_enable(MSTATUS_MIE_BIT);
    //     for (int j = 0; j < MAT_DIM; j++)
    //     {
    //         print_dec(res[i][j]);
    //         mstatus_enable(MSTATUS_MIE_BIT);
    //         print_chr(' ');
    //     }
    //     printf("\n");
    // }

    /////////////////////////////////
    // TEST 5: Random IRQs bombing //
    /////////////////////////////////

    // Test 5: random irqs arrive randomly
    // while the core is executing some task (e.g. matrix mult)

    printf("\nTEST 5 - RANDOM IRQS BOMBING: \n");

    mstatus_disable(MSTATUS_MIE_BIT);

    // Enable all mie and miex bits
    ie_mask32_std = 0xFFFFFFFF;
    ie_mask32_1   = 0xFFFFFFFF;

    asm volatile("csrw 0x304, %[ie_mask32_std]" : : [ie_mask32_std] "r" (ie_mask32_std));
    asm volatile("csrw 0x7D0, %[ie_mask32_1]"   : : [ie_mask32_1]   "r" (ie_mask32_1));

    writew(RND_IRQ_MIN_CYCLES, RND_STALL_REG_11);
    writew(RND_IRQ_MAX_CYCLES, RND_STALL_REG_12);

    // random irq gen mode:
    // the random interrupt generator will
    // keep on generating random interrupt vectors
    irq_mode = IRQ_MODE_RND;
    writew(irq_mode, RND_STALL_REG_10);

    irq_served = 0;

    mstatus_enable(MSTATUS_MIE_BIT);

    mat_mult(mat1, mat2, res);

    // disable irqs and check the result
    mstatus_disable(MSTATUS_MIE_BIT);

    printf("%d IRQ SERVED\n", irq_served);

     irq_served = 0;


    for (int i = 0; i < MAT_DIM; i++)
    {
        // mstatus_enable(MSTATUS_MIE_BIT);
        for (int j = 0; j < MAT_DIM; j++)
        {
            if(res[i][j] != res_expected[i][j])
            {
                printf("\nERR: wrong\nExpected %d Got %d at address %x\n", res_expected[i][j], res[i][j], &res[i][j]);
                return ERR_CODE_TEST_5;
            }
        }
    }

    return EXIT_SUCCESS;
}






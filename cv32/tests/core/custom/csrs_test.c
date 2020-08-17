//
// Copyright (C) EM Microelectronic US Inc.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//   http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND,
// either express or implied.
//
// See the License for the specific language governing permissions and
// limitations under the License.
//

#include <stdint.h>
#include <string.h>

#define TEST_DEAD_SPACE (0)

void CheckError();

#define csrw(csr, value) asm volatile("csrw\t\t" #csr ", %0" \
                                      : /* no output */      \
                                      : "r"(value));
#define csrr(csr, value) asm volatile("csrr\t\t%0, " #csr "" \
                                      : "=r"(value));

#define CSR_MSCRATCH 0x340
#define CSR_MEPC 0x341
#define CSR_MCAUSE 0x342
#define CSR_MINTSTATUS 0x346
#define CSR_MINTTHRESH 0x347

#define write_csr(reg, value)                             \
    {                                                     \
        asm volatile("csrw %0, %1" ::"i"(reg), "r"(value) \
                     : "memory");                         \
    }

#define read_csr(reg)              \
    {                              \
        asm volatile("csrr %0, %1" \
                     : "=r"(value) \
                     : "i"(reg)    \
                     : "memory");  \
    }

static volatile int gErrorExpected = 0;
static volatile int gActiveRegister = 0;
static int gCount = 0;
static int gCheck = 0;

uint32_t csr_read_impl()
{
    uint32_t value;

    read_csr(0x123);
    return value;
}

void csr_write_impl(uint32_t value)
{
    write_csr(0x123, value);
}

/// @todo Fix?
// uint16_t csr_read_buffer[sizeof(csr_read_impl) / sizeof(uint16_t)];
// uint16_t csr_write_buffer[sizeof(csr_write_impl) / sizeof(uint16_t)];
uint16_t csr_read_buffer[3];
uint16_t csr_write_buffer[3];

uint32_t csr_read(int reg)
{
    csr_read_buffer[1] = (csr_read_buffer[1] & 0x000F) | (reg << 4);
    //asm volatile("nop\n"); //
    return ((uint32_t(*)())csr_read_buffer)();
}

void csr_write(int reg, uint32_t value)
{
    csr_write_buffer[1] = (csr_write_buffer[1] & 0x000F) | (reg << 4);

    ((void (*)(uint32_t))csr_write_buffer)(value);
}

void ExceptionHandler()
{
    uint32_t value;

    if (!gErrorExpected)
    {
        gCheck++;
        asm("li x18, 1");
        asm("li x19, 0x20000000");
        asm("sw x18, 0(x19)");
        asm("wfi");
        write_csr(CSR_MSCRATCH, gActiveRegister | (int)0x80000000UL);
    }

    // Skip over the instruction (assuming it is not compressed)
    read_csr(CSR_MEPC);
    value += 4;
    write_csr(CSR_MEPC, value);
    write_csr(CSR_MSCRATCH, gActiveRegister | (int)0x40000000UL);

    gErrorExpected = 0;
}

void CheckError()
{
    // If the error was not see by the exception handler stop the test.
    if (gErrorExpected)
    {
        write_csr(CSR_MSCRATCH, gActiveRegister | (int)0x40000000UL);
    }
}

void TestNone(int reg)
{
	printf("TestNone: 0x%0x\n", reg);
    gActiveRegister = reg;
    gErrorExpected = 1;
    csr_read(reg);
    CheckError();
    gErrorExpected = 1;
    csr_write(reg, 0xCAFEBEEF);
    CheckError();
    gCount++;
}

void TestReadOnly(int reg)
{
	printf("TestReadOnly: 0x%0x\n", reg);
    gActiveRegister = reg;
    gErrorExpected = 0;
    csr_read(reg);
    CheckError();
    gErrorExpected = 1;
    csr_write(reg, 0xCAFEBEEF);
    CheckError();
    gCount++;
}

void TestWriteOnly(int reg)
{
	printf("TestWriteOnly: 0x%0x\n", reg);
    gActiveRegister = reg;
    gErrorExpected = 1;
    csr_read(reg);
    CheckError();
    gErrorExpected = 0;
    csr_write(reg, 0xCAFEBEEF);
    CheckError();
    gCount++;
}

void TestReadWrite(int reg)
{
	printf("TestReadWrite: 0x%0x\n", reg);
    gActiveRegister = reg;
    gErrorExpected = 0;
    uint32_t value = csr_read(reg);
    CheckError();
    csr_write(reg, 0xCAFEBEEF);
    CheckError();
    csr_write(reg, value);
    CheckError();
    gCount++;
}

int main()
{
    /// @todo Fix?
    // memcpy(csr_read_buffer, csr_read_impl, sizeof(csr_read_impl));
    // memcpy(csr_write_buffer, csr_write_impl, sizeof(csr_write_impl));
    memcpy(csr_read_buffer, csr_read_impl, 6);
    memcpy(csr_write_buffer, csr_write_impl, 6);

    TestNone(0x000); // ustatus
    TestNone(0x001); // fflags
    TestNone(0x002); // frm
    TestNone(0x003); // fcsr
    TestNone(0x004); // uie
    TestNone(0x005); // utvec
    TestNone(0x006);
    TestNone(0x007); // utvt (clic)

#if 1 == TEST_DEAD_SPACE
    for (int i = 0x008; i < 0x040; ++i)
    {
        TestNone(i);
    }
#endif // TEST_DEAD_SPACE

    TestNone(0x040); // uscratch
    TestNone(0x041); // uepc
    TestNone(0x042); // ucause
    TestNone(0x043); // utval
    TestNone(0x044); // uip
    TestNone(0x045); // unxti (clic)
    TestNone(0x046); // uintstatus (clic)
    TestNone(0x047); // uintthresh (clic)
    TestNone(0x048); // uscratchsw (clic)
    TestNone(0x049); // uscratchswl (clic)

#if 1 == TEST_DEAD_SPACE
    for (int i = 0x04A; i < 0x100; ++i)
    {
        TestNone(i);
    }
#endif // TEST_DEAD_SPACE

    TestNone(0x100); // sstatus
    TestNone(0x101);
    TestNone(0x102); // sedeleg
    TestNone(0x103); // sideleg
    TestNone(0x104); // sie
    TestNone(0x105); // stvec
    TestNone(0x106); // scounteren
    TestNone(0x107); // stvt (clic)

#if 1 == TEST_DEAD_SPACE
    for (int i = 0x108; i < 0x140; ++i)
    {
        TestNone(i);
    }
#endif // TEST_DEAD_SPACE

    TestNone(0x140); // sscratch
    TestNone(0x141); // sepc
    TestNone(0x142); // scause
    TestNone(0x143); // stval
    TestNone(0x144); // sip
    TestNone(0x145); // snxti (clic)
    TestNone(0x146); // sintstatus (clic)
    TestNone(0x147); // sintthresh (clic)
    TestNone(0x148); // sscratchsw (clic)
    TestNone(0x149); // sscratchswl (clic)

#if 1 == TEST_DEAD_SPACE
    for (int i = 0x14A; i < 0x180; ++i)
    {
        TestNone(i);
    }
#endif // TEST_DEAD_SPACE

    TestNone(0x180); // satp

#if 1 == TEST_DEAD_SPACE
    for (int i = 0x181; i < 0x200; ++i)
    {
        TestNone(i);
    }
#endif // TEST_DEAD_SPACE

    TestNone(0x200); // bsstatus
    TestNone(0x201);
    TestNone(0x202);
    TestNone(0x203);
    TestNone(0x204); // bsie
    TestNone(0x205); // bstvec

#if 1 == TEST_DEAD_SPACE
    for (int i = 0x206; i < 0x240; ++i)
    {
        TestNone(i);
    }
#endif // TEST_DEAD_SPACE

    TestNone(0x240); // bsscratch
    TestNone(0x241); // bsepc
    TestNone(0x242); // bscause
    TestNone(0x243); // bstval
    TestNone(0x244); // bsip

#if 1 == TEST_DEAD_SPACE
    for (int i = 0x245; i < 0x280; ++i)
    {
        TestNone(i);
    }
#endif // TEST_DEAD_SPACE

    TestNone(0x280); // bsatp

#if 1 == TEST_DEAD_SPACE
    for (int i = 0x281; i < 0x300; ++i)
    {
        TestNone(i);
    }
#endif // TEST_DEAD_SPACE

    TestReadWrite(0x300); // mstatus
    TestReadWrite(0x301); // misa
    TestNone(0x302);      // medeleg
    TestNone(0x303);      // mideleg
    TestReadWrite(0x304); // mie
    TestReadWrite(0x305); // mtvec
    TestReadWrite(0x306); // mcounteren
    TestNone(0x307);      // mtvt (clic)

#if 1 == TEST_DEAD_SPACE
    for (int i = 0x308; i < 0x320; ++i)
    {
        TestNone(i);
    }
#endif // TEST_DEAD_SPACE

    TestReadWrite(0x320); // mcountinhibit
    TestNone(0x321);
    TestNone(0x322);
    TestReadWrite(0x323); // mhpmevent3
    TestReadWrite(0x324); // mhpmevent4
    TestReadWrite(0x325); // mhpmevent5
    TestReadWrite(0x326); // mhpmevent6
    TestReadWrite(0x327); // mhpmevent7
    TestReadWrite(0x328); // mhpmevent8
    TestReadWrite(0x329); // mhpmevent9
    TestReadWrite(0x32A); // mhpmevent10
    TestReadWrite(0x32B); // mhpmevent11
    TestReadWrite(0x32C); // mhpmevent12
    TestReadWrite(0x32D); // mhpmevent13
    TestReadWrite(0x32E); // mhpmevent14
    TestReadWrite(0x32F); // mhpmevent15
    TestReadWrite(0x330); // mhpmevent16
    TestReadWrite(0x331); // mhpmevent17
    TestReadWrite(0x332); // mhpmevent18
    TestReadWrite(0x333); // mhpmevent19
    TestReadWrite(0x334); // mhpmevent20
    TestReadWrite(0x335); // mhpmevent21
    TestReadWrite(0x336); // mhpmevent22
    TestReadWrite(0x337); // mhpmevent23
    TestReadWrite(0x338); // mhpmevent24
    TestReadWrite(0x339); // mhpmevent25
    TestReadWrite(0x33A); // mhpmevent26
    TestReadWrite(0x33B); // mhpmevent27
    TestReadWrite(0x33C); // mhpmevent28
    TestReadWrite(0x33D); // mhpmevent29
    TestReadWrite(0x33E); // mhpmevent30
    TestReadWrite(0x33F); // mhpmevent31

    TestReadWrite(0x340); // mscratch
    TestReadWrite(0x341); // mepc
    TestReadWrite(0x342); // mcause
    TestReadWrite(0x343); // mtval
    TestReadWrite(0x344); // mip
    TestNone(0x345);      // mnxti (clic)
    //TestReadWrite(0x346); // mintstatus (clic)
    TestNone(0x347);      // mintthresh (clic)
    TestNone(0x348);      // mscratchsw (clic)
    TestNone(0x349);      // mscratchswl (clic)

#if 1 == TEST_DEAD_SPACE
    for (int i = 0x34A; i < 0x3A0; ++i)
    {
        TestNone(i);
    }
#endif // TEST_DEAD_SPACE

    TestNone(0x3A0); // pmpcfg0
    TestNone(0x3A1); // pmpcfg1
    TestNone(0x3A2); // pmpcfg2
    TestNone(0x3A3); // pmpcfg3

#if 1 == TEST_DEAD_SPACE
    for (int i = 0x3A4; i < 0x3B0; ++i)
    {
        TestNone(i);
    }
#endif // TEST_DEAD_SPACE

    TestNone(0x3B0); // pmpaddr0
    TestNone(0x3B1); // pmpaddr1
    TestNone(0x3B2); // pmpaddr2
    TestNone(0x3B3); // pmpaddr3
    TestNone(0x3B4); // pmpaddr4
    TestNone(0x3B5); // pmpaddr5
    TestNone(0x3B6); // pmpaddr6
    TestNone(0x3B7); // pmpaddr7
    TestNone(0x3B8); // pmpaddr8
    TestNone(0x3B9); // pmpaddr9
    TestNone(0x3BA); // pmpaddr10
    TestNone(0x3BB); // pmpaddr11
    TestNone(0x3BC); // pmpaddr12
    TestNone(0x3BD); // pmpaddr13
    TestNone(0x3BE); // pmpaddr14
    TestNone(0x3BF); // pmpaddr15

#if 1 == TEST_DEAD_SPACE
    for (int i = 0x3C0; i < 0x7A0; ++i)
    {
        TestNone(i);
    }
#endif // TEST_DEAD_SPACE

    //TestReadWrite(0x7A0); // tselect
    //TestReadWrite(0x7A1); // tdata1
    //TestReadWrite(0x7A2); // tdata2
    //TestReadWrite(0x7A3); // tdata3
    //TestReadWrite(0x7A4); // tinfo
    TestNone(0x7A5);      // tcontrol
    TestNone(0x7A6);
    TestNone(0x7A7);
    //TestReadWrite(0x7A8); // mcontext
    TestNone(0x7A9);
    //TestReadWrite(0x7AA); // scontext

#if 1 == TEST_DEAD_SPACE
    for (int i = 0x7AB; i < 0x7C0; ++i)
    {
        TestNone(i);
    }
#endif // TEST_DEAD_SPACE

    //TestReadWrite(0x7C0); // lpstart0
    //TestReadWrite(0x7C1); // lpend0
    //TestReadWrite(0x7C2); // lpcount0
    TestNone(0x7C3);
    //TestReadWrite(0x7C4); // lpstart1
    //TestReadWrite(0x7C5); // lpend1
    //TestReadWrite(0x7C6); // lpcount1

#if 1 == TEST_DEAD_SPACE
    for (int i = 0x7C7; i < 0xA00; ++i)
    {
        TestNone(i);
    }
#endif // TEST_DEAD_SPACE

    TestNone(0xA00); // hstatus
    TestNone(0xA01);
    TestNone(0xA02); // hedeleg
    TestNone(0xA03); // hideleg

#if 1 == TEST_DEAD_SPACE
    for (int i = 0xA04; i < 0xA80; ++i)
    {
        TestNone(i);
    }
#endif // TEST_DEAD_SPACE

    TestNone(0xA80); // hgatp

#if 1 == TEST_DEAD_SPACE
    for (int i = 0xA81; i < 0xB00; ++i)
    {
        TestNone(i);
    }
#endif // TEST_DEAD_SPACE

    TestReadWrite(0xB00); // mcycle
    TestNone(0xB01); // mtime		//
    TestReadWrite(0xB02); // minstret
    TestReadWrite(0xB03); // mhpmcounter3
    TestReadWrite(0xB04); // mhpmcounter4
    TestReadWrite(0xB05); // mhpmcounter5
    TestReadWrite(0xB06); // mhpmcounter6
    TestReadWrite(0xB07); // mhpmcounter7
    TestReadWrite(0xB08); // mhpmcounter8
    TestReadWrite(0xB09); // mhpmcounter9
    TestReadWrite(0xB0A); // mhpmcounter10
    TestReadWrite(0xB0B); // mhpmcounter11
    TestReadWrite(0xB0C); // mhpmcounter12
    TestReadWrite(0xB0D); // mhpmcounter13
    TestReadWrite(0xB0E); // mhpmcounter14
    TestReadWrite(0xB0F); // mhpmcounter15
    TestReadWrite(0xB10); // mhpmcounter16
    TestReadWrite(0xB11); // mhpmcounter17
    TestReadWrite(0xB12); // mhpmcounter18
    TestReadWrite(0xB13); // mhpmcounter19
    TestReadWrite(0xB14); // mhpmcounter20
    TestReadWrite(0xB06); // mhpmcounter6
    TestReadWrite(0xB15); // mhpmcounter21
    TestReadWrite(0xB16); // mhpmcounter22
    TestReadWrite(0xB17); // mhpmcounter23
    TestReadWrite(0xB18); // mhpmcounter24
    TestReadWrite(0xB19); // mhpmcounter25
    TestReadWrite(0xB1A); // mhpmcounter26
    TestReadWrite(0xB1B); // mhpmcounter27
    TestReadWrite(0xB1C); // mhpmcounter28
    TestReadWrite(0xB1D); // mhpmcounter29
    TestReadWrite(0xB1E); // mhpmcounter30
    TestReadWrite(0xB1F); // mhpmcounter31

#if 1 == TEST_DEAD_SPACE
    for (int i = 0xB20; i < 0xB80; ++i)
    {
        TestNone(i);
    }
#endif // TEST_DEAD_SPACE

    TestReadWrite(0xB80); // mcycleh
    TestNone(0xB81); // mtimeh		//
    TestReadWrite(0xB82); // minstreth
    TestReadWrite(0xB83); // mhpmcounter3h
    TestReadWrite(0xB84); // mhpmcounter4h
    TestReadWrite(0xB85); // mhpmcounter5h
    TestReadWrite(0xB86); // mhpmcounter6h
    TestReadWrite(0xB87); // mhpmcounter7h
    TestReadWrite(0xB88); // mhpmcounter8h
    TestReadWrite(0xB89); // mhpmcounter9h
    TestReadWrite(0xB8A); // mhpmcounter10h
    TestReadWrite(0xB8B); // mhpmcounter11h
    TestReadWrite(0xB8C); // mhpmcounter12h
    TestReadWrite(0xB8D); // mhpmcounter13h
    TestReadWrite(0xB8E); // mhpmcounter14h
    TestReadWrite(0xB8F); // mhpmcounter15h
    TestReadWrite(0xB90); // mhpmcounter16h
    TestReadWrite(0xB91); // mhpmcounter17h
    TestReadWrite(0xB92); // mhpmcounter18h
    TestReadWrite(0xB93); // mhpmcounter19h
    TestReadWrite(0xB94); // mhpmcounter20h
    TestReadWrite(0xB95); // mhpmcounter21h
    TestReadWrite(0xB96); // mhpmcounter22h
    TestReadWrite(0xB97); // mhpmcounter23h
    TestReadWrite(0xB98); // mhpmcounter24h
    TestReadWrite(0xB99); // mhpmcounter25h
    TestReadWrite(0xB9A); // mhpmcounter26h
    TestReadWrite(0xB9B); // mhpmcounter27h
    TestReadWrite(0xB9C); // mhpmcounter28h
    TestReadWrite(0xB9D); // mhpmcounter29h
    TestReadWrite(0xB9E); // mhpmcounter30h
    TestReadWrite(0xB9F); // mhpmcounter31h

#if 1 == TEST_DEAD_SPACE
    for (int i = 0xBA0; i < 0xC00; ++i)
    {
        TestNone(i);
    }
#endif // TEST_DEAD_SPACE

    TestReadOnly(0xC00); // cycle
    TestReadOnly(0xC01); // time
    TestReadOnly(0xC02); // instret
    TestReadOnly(0xC03); // hpmcounter3
    TestReadOnly(0xC04); // hpmcounter4
    TestReadOnly(0xC05); // hpmcounter5
    TestReadOnly(0xC06); // hpmcounter6
    TestReadOnly(0xC07); // hpmcounter7
    TestReadOnly(0xC08); // hpmcounter8
    TestReadOnly(0xC09); // hpmcounter9
    TestReadOnly(0xC0A); // hpmcounter10
    TestReadOnly(0xC0B); // hpmcounter11
    TestReadOnly(0xC0C); // hpmcounter12
    TestReadOnly(0xC0D); // hpmcounter13
    TestReadOnly(0xC0E); // hpmcounter14
    TestReadOnly(0xC0F); // hpmcounter15
    TestReadOnly(0xC10); // hpmcounter16
    TestReadOnly(0xC11); // hpmcounter17
    TestReadOnly(0xC12); // hpmcounter18
    TestReadOnly(0xC13); // hpmcounter19
    TestReadOnly(0xC14); // hpmcounter20
    TestReadOnly(0xC15); // hpmcounter21
    TestReadOnly(0xC16); // hpmcounter22
    TestReadOnly(0xC17); // hpmcounter23
    TestReadOnly(0xC18); // hpmcounter24
    TestReadOnly(0xC19); // hpmcounter25
    TestReadOnly(0xC1A); // hpmcounter26
    TestReadOnly(0xC1B); // hpmcounter27
    TestReadOnly(0xC1C); // hpmcounter28
    TestReadOnly(0xC1D); // hpmcounter29
    TestReadOnly(0xC1E); // hpmcounter30
    TestReadOnly(0xC1F); // hpmcounter31

#if 1 == TEST_DEAD_SPACE
    for (int i = 0xC20; i < 0xC80; ++i)
    {
        TestNone(i);
    }
#endif // TEST_DEAD_SPACE

    TestReadOnly(0xC80); // cycleh
    TestReadOnly(0xC81); // timeh
    TestReadOnly(0xC82); // instreth
    TestReadOnly(0xC83); // hpmcounter3h
    TestReadOnly(0xC84); // hpmcounter4h
    TestReadOnly(0xC85); // hpmcounter5h
    TestReadOnly(0xC86); // hpmcounter6h
    TestReadOnly(0xC87); // hpmcounter7h
    TestReadOnly(0xC88); // hpmcounter8h
    TestReadOnly(0xC89); // hpmcounter9h
    TestReadOnly(0xC8A); // hpmcounter10h
    TestReadOnly(0xC8B); // hpmcounter11h
    TestReadOnly(0xC8C); // hpmcounter12h
    TestReadOnly(0xC8D); // hpmcounter13h
    TestReadOnly(0xC8E); // hpmcounter14h
    TestReadOnly(0xC8F); // hpmcounter15h
    TestReadOnly(0xC90); // hpmcounter16h
    TestReadOnly(0xC91); // hpmcounter17h
    TestReadOnly(0xC92); // hpmcounter18h
    TestReadOnly(0xC93); // hpmcounter19h
    TestReadOnly(0xC94); // hpmcounter20h
    TestReadOnly(0xC95); // hpmcounter21h
    TestReadOnly(0xC96); // hpmcounter22h
    TestReadOnly(0xC97); // hpmcounter23h
    TestReadOnly(0xC98); // hpmcounter24h
    TestReadOnly(0xC99); // hpmcounter25h
    TestReadOnly(0xC9A); // hpmcounter26h
    TestReadOnly(0xC9B); // hpmcounter27h
    TestReadOnly(0xC9C); // hpmcounter28h
    TestReadOnly(0xC9D); // hpmcounter29h
    TestReadOnly(0xC9E); // hpmcounter30h
    TestReadOnly(0xC9F); // hpmcounter31h

#if 1 == TEST_DEAD_SPACE
    for (int i = 0xCA0; i < 0xF11; ++i)
    {
        TestNone(i);
    }
#endif // TEST_DEAD_SPACE

    TestReadOnly(0xF11); // mvendorid
    TestReadOnly(0xF12); // marchid
    TestReadOnly(0xF13); // mimpid
    TestReadOnly(0xF14); // mhartid

#if 1 == TEST_DEAD_SPACE
    for (int i = 0xF15; i < 0xF46; ++i)
    {
        TestNone(i);
    }
    
    TestNone(0xF46); // unknown CSR
    
    for (int i = 0xF47; i < 0xFB0; ++i)
    {
        TestNone(i);
    }
#endif // TEST_DEAD_SPACE

    TestNone(0x7B0); // dcsr
    TestNone(0x7B1); // dpc
    TestNone(0x7B2); // dscratch0
    TestNone(0x7B3); // dscratch1

#if 1 == TEST_DEAD_SPACE
    for (int i = 0xFB4; i <= 0xFFF; ++i)
    {
        TestNone(i);
    }
#endif // TEST_DEAD_SPACE
    if(gCheck)
    {
        asm("li x18, 1");
        asm("li x19, 0x20000000");
        asm("sw x18, 0(x19)");
        asm("wfi");
    }
    asm("li x18, 123456789");
    asm("li x19, 0x20000000");
    asm("sw x18, 0(x19)");
    asm("wfi");
}

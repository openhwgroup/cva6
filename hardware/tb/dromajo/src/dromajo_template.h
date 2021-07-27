/*
 * RISCV emulator
 *
 * Copyright (c) 2016 Fabrice Bellard
 * Copyright (C) 2017,2018,2019, Esperanto Technologies Inc.
 *
 * Licensed under the Apache License, Version 2.0 (the "License")
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *   http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 *
 * THIS FILE IS BASED ON THE RISCVEMU SOURCE CODE WHICH IS DISTRIBUTED
 * UNDER THE FOLLOWING LICENSE:
 *
 * Copyright (c) 2016 Fabrice Bellard
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in
 * all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL
 * THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
 * THE SOFTWARE.
 */
#if XLEN == 32
#define uintx_t uint32_t
#define intx_t int32_t
#elif XLEN == 64
#define uintx_t uint64_t
#define intx_t int64_t
#elif XLEN == 128
#define uintx_t uint128_t
#define intx_t int128_t
#else
#error unsupported XLEN
#endif

static inline intx_t glue(div, XLEN)(intx_t a, intx_t b)
{
    if (b == 0) {
        return -1;
    } else if (a == ((intx_t)1 << (XLEN - 1)) && b == -1) {
        return a;
    } else {
        return a / b;
    }
}

static inline uintx_t glue(divu, XLEN)(uintx_t a, uintx_t b)
{
    if (b == 0) {
        return -1;
    } else {
        return a / b;
    }
}

static inline intx_t glue(rem, XLEN)(intx_t a, intx_t b)
{
    if (b == 0) {
        return a;
    } else if (a == ((intx_t)1 << (XLEN - 1)) && b == -1) {
        return 0;
    } else {
        return a % b;
    }
}

static inline uintx_t glue(remu, XLEN)(uintx_t a, uintx_t b)
{
    if (b == 0) {
        return a;
    } else {
        return a % b;
    }
}

#if XLEN == 32

static inline uint32_t mulh32(int32_t a, int32_t b)
{
    return ((int64_t)a * (int64_t)b) >> 32;
}

static inline uint32_t mulhsu32(int32_t a, uint32_t b)
{
    return ((int64_t)a * (int64_t)b) >> 32;
}

static inline uint32_t mulhu32(uint32_t a, uint32_t b)
{
    return ((int64_t)a * (int64_t)b) >> 32;
}

#elif XLEN == 64 && defined(HAVE_INT128)

static inline uint64_t mulh64(int64_t a, int64_t b)
{
    return ((int128_t)a * (int128_t)b) >> 64;
}

static inline uint64_t mulhsu64(int64_t a, uint64_t b)
{
    return ((int128_t)a * (int128_t)b) >> 64;
}

static inline uint64_t mulhu64(uint64_t a, uint64_t b)
{
    return ((int128_t)a * (int128_t)b) >> 64;
}

#else

#if XLEN == 64
#define UHALF uint32_t
#define UHALF_LEN 32
#elif XLEN == 128
#define UHALF uint64_t
#define UHALF_LEN 64
#else
#error unsupported XLEN
#endif

static uintx_t glue(mulhu, XLEN)(uintx_t a, uintx_t b)
{
    UHALF a0, a1, b0, b1, r2, r3;
    uintx_t r00, r01, r10, r11, c;
    a0 = a;
    a1 = a >> UHALF_LEN;
    b0 = b;
    b1 = b >> UHALF_LEN;

    r00 = (uintx_t)a0 * (uintx_t)b0;
    r01 = (uintx_t)a0 * (uintx_t)b1;
    r10 = (uintx_t)a1 * (uintx_t)b0;
    r11 = (uintx_t)a1 * (uintx_t)b1;

    //    r0 = r00;
    c = (r00 >> UHALF_LEN) + (UHALF)r01 + (UHALF)r10;
    //    r1 = c;
    c = (c >> UHALF_LEN) + (r01 >> UHALF_LEN) + (r10 >> UHALF_LEN) + (UHALF)r11;
    r2 = c;
    r3 = (c >> UHALF_LEN) + (r11 >> UHALF_LEN);

    //    *plow = ((uintx_t)r1 << UHALF_LEN) | r0;
    return ((uintx_t)r3 << UHALF_LEN) | r2;
}

#undef UHALF

static inline uintx_t glue(mulh, XLEN)(intx_t a, intx_t b)
{
    uintx_t r1;
    r1 = glue(mulhu, XLEN)(a, b);
    if (a < 0)
        r1 -= a;
    if (b < 0)
        r1 -= b;
    return r1;
}

static inline uintx_t glue(mulhsu, XLEN)(intx_t a, uintx_t b)
{
    uintx_t r1;
    r1 = glue(mulhu, XLEN)(a, b);
    if (a < 0)
        r1 -= a;
    return r1;
}

#endif

#define DUP2(F, n) F(n) F(n+1)
#define DUP4(F, n) DUP2(F, n) DUP2(F, n + 2)
#define DUP8(F, n) DUP4(F, n) DUP4(F, n + 4)
#define DUP16(F, n) DUP8(F, n) DUP8(F, n + 8)
#define DUP32(F, n) DUP16(F, n) DUP16(F, n + 16)

#define C_QUADRANT(n) \
    case n+(0 << 2): case n+(1 << 2): case n+(2 << 2): case n+(3 << 2): \
    case n+(4 << 2): case n+(5 << 2): case n+(6 << 2): case n+(7 << 2): \
    case n+(8 << 2): case n+(9 << 2): case n+(10 << 2): case n+(11 << 2): \
    case n+(12 << 2): case n+(13 << 2): case n+(14 << 2): case n+(15 << 2): \
    case n+(16 << 2): case n+(17 << 2): case n+(18 << 2): case n+(19 << 2): \
    case n+(20 << 2): case n+(21 << 2): case n+(22 << 2): case n+(23 << 2): \
    case n+(24 << 2): case n+(25 << 2): case n+(26 << 2): case n+(27 << 2): \
    case n+(28 << 2): case n+(29 << 2): case n+(30 << 2): case n+(31 << 2):

#define GET_PC() (target_ulong)((uintptr_t)code_ptr + code_to_pc_addend)
#define GET_INSN_COUNTER() (insn_counter_addend - n_cycles)

#define C_NEXT_INSN code_ptr += 2; break
#define NEXT_INSN code_ptr += 4; break
#define JUMP_INSN(kind) do {       \
        code_ptr = NULL;           \
        code_end = NULL;           \
        code_to_pc_addend = s->pc; \
        s->info = kind;            \
        s->next_addr = s->pc;      \
        goto jump_insn;            \
    } while (0)

#define chkfp32 glue(chkfp32, XLEN)

static uint32_t chkfp32(target_ulong a)
{
    if ((a & 0xFFFFFFFF00000000ULL) != 0xFFFFFFFF00000000ULL)
        return -1U << 22;  // Not boxed => return float32 QNAN

    return (uint32_t) a;
}

/*
 * Table 2.1: Return-address stack prediction hints
 *      rd      rs1     rs1=rd          RAS action
 *    !x1/x5  !x1/x5       -            none
 *    !x1/x5   x1/x5       -            pop
 *     x1/x5  !x1/x5       -            push
 *     x1/x5   x1/x5       0            pop, then push
 *     x1/x5   x1/x5       1            push
 */

int no_inline glue(riscv_cpu_interp, XLEN)(RISCVCPUState *s, int n_cycles);

int no_inline glue(riscv_cpu_interp, XLEN)(RISCVCPUState *s, int n_cycles)
{
    uint32_t opcode, insn, rd, rs1, rs2, funct3;
    int32_t imm, cond, err;
    target_ulong addr, val, val2;
    uint8_t *code_ptr, *code_end;
    target_ulong code_to_pc_addend;
    uint64_t insn_counter_addend;
    uint64_t insn_counter_start = s->insn_counter;
#if FLEN > 0
    uint32_t rs3;
    int32_t rm;
#endif
    int insn_executed = 0;
    s->most_recently_written_reg = -1;
    s->most_recently_written_fp_reg = -1;
    s->info = ctf_nop;

    if (n_cycles == 0)
        return 0;
    insn_counter_addend = s->insn_counter + n_cycles;

    /* check pending interrupts */
    if (unlikely(((s->mip & s->mie) != 0) && (s->machine->common.pending_interrupt != -1 || !s->machine->common.cosim))) {
        if (raise_interrupt(s)) {
            --insn_counter_addend;
            goto done_interp;
        }
    }

    s->pending_exception = -1;
    n_cycles++;
    /* Note: we assume NULL is represented as a zero number */
    code_ptr = NULL;
    code_end = NULL;
    code_to_pc_addend = s->pc;

    /* we use a single execution loop to keep a simple control flow
       for emscripten */
    for (;;) {
        s->pc = GET_PC();
        if (unlikely(!--n_cycles))
            goto the_end;

        ++insn_executed;

        /* Handled any breakpoint triggers in order (note, we
         * precompute the mask and pattern to lower some of the
         * cost). */
        target_ulong t_mctl  = MCONTROL_EXECUTE | (MCONTROL_U << s->priv);
        target_ulong t_mask  = ((target_ulong)0xF << 60) | t_mctl;
        target_ulong t_match = ((target_ulong)0x2 << 60) | t_mctl;

        for (int i = 0; i < MAX_TRIGGERS; ++i)
            if ((s->tdata1[i] & t_mask) != t_match && s->tdata2[i] == s->pc) {
                --insn_counter_addend;
                s->pending_exception = CAUSE_BREAKPOINT;
                s->pending_tval = 0;
                raise_exception2(s, s->pending_exception, s->pending_tval);
                goto done_interp;
            }

        if (unlikely(code_ptr >= code_end)) {
            uint32_t tlb_idx;
            uint16_t insn_high;
            target_ulong addr;

            /* check pending interrupts */
            if (unlikely(((s->mip & s->mie) != 0) && (s->machine->common.pending_interrupt != -1 || !s->machine->common.cosim))) {
                if (raise_interrupt(s)) {
                    goto the_end;
                }
            }

            addr = s->pc;
            tlb_idx = (addr >> PG_SHIFT) & (TLB_SIZE - 1);
            if (likely(s->tlb_code[tlb_idx].vaddr == (addr & ~PG_MASK))) {
                /* TLB match */
                uintptr_t mem_addend;
                mem_addend = s->tlb_code[tlb_idx].mem_addend;
                code_ptr = (uint8_t *)(mem_addend + (uintptr_t)addr);
                code_end = (uint8_t *)(mem_addend +
                                       (uintptr_t)((addr & ~PG_MASK) + PG_MASK - 1));
                code_to_pc_addend = addr - (uintptr_t)code_ptr;
                if (unlikely(code_ptr >= code_end)) {
                    /* instruction is potentially half way between two
                       pages ? */
                    insn = *(uint16_t *)code_ptr;
                    if ((insn & 3) == 3) {
                        /* instruction is half way between two pages */
                        if (unlikely(target_read_insn_u16(s, &insn_high, addr + 2)))
                            goto mmu_exception;
                        insn |= insn_high << 16;
                    }
                } else {
                    insn = get_insn32(code_ptr);
                }

            } else {
                if (unlikely(target_read_insn_slow(s, &insn, 32, addr)))
                    goto mmu_exception;
            }
        } else {
            /* fast path */
            insn = get_insn32(code_ptr);
        }

        opcode = insn & 0x7f;
        rd = (insn >> 7) & 0x1f;
        rs1 = (insn >> 15) & 0x1f;
        rs2 = (insn >> 20) & 0x1f;
        switch (opcode) {
        C_QUADRANT(0)
            funct3 = (insn >> 13) & 7;
            rd = ((insn >> 2) & 7) | 8;
            switch (funct3) {
            case 0: /* c.addi4spn */
                imm = get_field1(insn, 11, 4, 5) |
                    get_field1(insn, 7, 6, 9) |
                    get_field1(insn, 6, 2, 2) |
                    get_field1(insn, 5, 3, 3);
                if (imm == 0)
                    goto illegal_insn;
                write_reg(rd, (intx_t)(read_reg(2) + imm));
                break;
#if XLEN >= 128
            case 1: /* c.lq */
                imm = get_field1(insn, 11, 4, 5) |
                    get_field1(insn, 10, 8, 8) |
                    get_field1(insn, 5, 6, 7);
                rs1 = ((insn >> 7) & 7) | 8;
                addr = (intx_t)(read_reg(rs1) + imm);
                s->last_addr = addr;
                if (target_read_u128(s, &val, addr))
                    goto mmu_exception;
                write_reg(rd, val);
                break;
#elif FLEN >= 64
            case 1: /* c.fld */
                {
                    uint64_t rval;
                    if (s->fs == 0)
                        goto illegal_insn;
                    imm = get_field1(insn, 10, 3, 5) |
                        get_field1(insn, 5, 6, 7);
                    rs1 = ((insn >> 7) & 7) | 8;
                    addr = (intx_t)(read_reg(rs1) + imm);
                    if (target_read_u64(s, &rval, addr))
                        goto mmu_exception;
                    write_fp_reg(rd, rval | F64_HIGH);
                }
                break;
#endif
            case 2: /* c.lw */
                {
                    uint32_t rval;
                    imm = get_field1(insn, 10, 3, 5) |
                        get_field1(insn, 6, 2, 2) |
                        get_field1(insn, 5, 6, 6);
                    rs1 = ((insn >> 7) & 7) | 8;
                    addr = (intx_t)(read_reg(rs1) + imm);
                    if (target_read_u32(s, &rval, addr))
                        goto mmu_exception;
                    write_reg(rd, (int32_t)rval);
                }
                break;
#if XLEN >= 64
            case 3: /* c.ld */
                {
                    uint64_t rval;
                    imm = get_field1(insn, 10, 3, 5) |
                        get_field1(insn, 5, 6, 7);
                    rs1 = ((insn >> 7) & 7) | 8;
                    addr = (intx_t)(read_reg(rs1) + imm);
                    if (target_read_u64(s, &rval, addr))
                        goto mmu_exception;
                    write_reg(rd, (int64_t)rval);
                }
                break;
#elif FLEN >= 32
            case 3: /* c.flw */
                {
                    uint32_t rval;
                    if (s->fs == 0)
                        goto illegal_insn;
                    imm = get_field1(insn, 10, 3, 5) |
                        get_field1(insn, 6, 2, 2) |
                        get_field1(insn, 5, 6, 6);
                    rs1 = ((insn >> 7) & 7) | 8;
                    addr = (intx_t)(read_reg(rs1) + imm);
                    if (target_read_u32(s, &rval, addr))
                        goto mmu_exception;
                    write_fp_reg(rd, rval | F32_HIGH);
                }
                break;
#endif
#if XLEN >= 128
            case 5: /* c.sq */
                imm = get_field1(insn, 11, 4, 5) |
                    get_field1(insn, 10, 8, 8) |
                    get_field1(insn, 5, 6, 7);
                rs1 = ((insn >> 7) & 7) | 8;
                addr = (intx_t)(read_reg(rs1) + imm);
                val = read_reg(rd);
                if (target_write_u128(s, addr, val))
                    goto mmu_exception;
                break;
#elif FLEN >= 64
            case 5: /* c.fsd */
                if (s->fs == 0)
                    goto illegal_insn;
                imm = get_field1(insn, 10, 3, 5) |
                    get_field1(insn, 5, 6, 7);
                rs1 = ((insn >> 7) & 7) | 8;
                addr = (intx_t)(read_reg(rs1) + imm);
                if (target_write_u64(s, addr, read_fp_reg(rd)))
                    goto mmu_exception;
                break;
#endif
            case 6: /* c.sw */
                imm = get_field1(insn, 10, 3, 5) |
                    get_field1(insn, 6, 2, 2) |
                    get_field1(insn, 5, 6, 6);
                rs1 = ((insn >> 7) & 7) | 8;
                addr = (intx_t)(read_reg(rs1) + imm);
                val = read_reg(rd);
                if (target_write_u32(s, addr, val))
                    goto mmu_exception;
                break;
#if XLEN >= 64
            case 7: /* c.sd */
                imm = get_field1(insn, 10, 3, 5) |
                    get_field1(insn, 5, 6, 7);
                rs1 = ((insn >> 7) & 7) | 8;
                addr = (intx_t)(read_reg(rs1) + imm);
                val = read_reg(rd);
                if (target_write_u64(s, addr, val))
                    goto mmu_exception;
                break;
#elif FLEN >= 32
            case 7: /* c.fsw */
                if (s->fs == 0)
                    goto illegal_insn;
                imm = get_field1(insn, 10, 3, 5) |
                    get_field1(insn, 6, 2, 2) |
                    get_field1(insn, 5, 6, 6);
                rs1 = ((insn >> 7) & 7) | 8;
                addr = (intx_t)(read_reg(rs1) + imm);
                if (target_write_u32(s, addr, read_fp_reg(rd)))
                    goto mmu_exception;
                break;
#endif
            default:
                goto illegal_insn;
            }
            C_NEXT_INSN;
        C_QUADRANT(1)
            funct3 = (insn >> 13) & 7;
            switch (funct3) {
            case 0: /* c.addi/c.nop */
                if (rd != 0) {
                    imm = sext(get_field1(insn, 12, 5, 5) |
                               get_field1(insn, 2, 0, 4), 6);
                    write_reg(rd, (intx_t)(read_reg(rd) + imm));
                }
                break;
#if XLEN == 32
            case 1: /* c.jal */
                imm = sext(get_field1(insn, 12, 11, 11) |
                           get_field1(insn, 11, 4, 4) |
                           get_field1(insn, 9, 8, 9) |
                           get_field1(insn, 8, 10, 10) |
                           get_field1(insn, 7, 6, 6) |
                           get_field1(insn, 6, 7, 7) |
                           get_field1(insn, 3, 1, 3) |
                           get_field1(insn, 2, 5, 5), 12);
                write_reg(1, GET_PC() + 2);
                s->pc = (intx_t)(GET_PC() + imm);
                JUMP_INSN(ctf_taken_jump);
#else
            case 1: /* c.addiw */
                if (rd == 0)
                    goto illegal_insn;
                imm = sext(get_field1(insn, 12, 5, 5) |
                           get_field1(insn, 2, 0, 4), 6);
                write_reg(rd, (int32_t)(read_reg(rd) + imm));
                break;
#endif
            case 2: /* c.li */
                if (rd != 0) {
                    imm = sext(get_field1(insn, 12, 5, 5) |
                               get_field1(insn, 2, 0, 4), 6);
                    write_reg(rd, imm);
                }
                break;
            case 3:
                if (rd == 2) {
                    /* c.addi16sp */
                    imm = sext(get_field1(insn, 12, 9, 9) |
                               get_field1(insn, 6, 4, 4) |
                               get_field1(insn, 5, 6, 6) |
                               get_field1(insn, 3, 7, 8) |
                               get_field1(insn, 2, 5, 5), 10);
                    if (imm == 0)
                        goto illegal_insn;
                    write_reg(2, (intx_t)(read_reg(2) + imm));
                } else if (rd != 0) {
                    /* c.lui */
                    imm = sext(get_field1(insn, 12, 17, 17) |
                               get_field1(insn, 2, 12, 16), 18);
                    if (imm == 0)
                        goto illegal_insn;
                    write_reg(rd, imm);
                }
                break;
            case 4:
                funct3 = (insn >> 10) & 3;
                rd = ((insn >> 7) & 7) | 8;
                switch (funct3) {
                case 0: /* c.srli */
                case 1: /* c.srai */
                    imm = get_field1(insn, 12, 5, 5) |
                        get_field1(insn, 2, 0, 4);
#if XLEN == 32
                    if (imm & 0x20)
                        goto illegal_insn;
#elif XLEN == 128
                    if (imm == 0)
                        imm = 64;
                    else if (imm >= 32)
                        imm = 128 - imm;
#endif
                    if (funct3 == 0)
                        write_reg(rd, (intx_t)((uintx_t)read_reg(rd) >> imm));
                    else
                        write_reg(rd, (intx_t)read_reg(rd) >> imm);

                    break;
                case 2: /* c.andi */
                    imm = sext(get_field1(insn, 12, 5, 5) |
                               get_field1(insn, 2, 0, 4), 6);
                    write_reg(rd, read_reg(rd) & imm);
                    break;
                case 3:
                    rs2 = ((insn >> 2) & 7) | 8;
                    funct3 = ((insn >> 5) & 3) | ((insn >> (12 - 2)) & 4);
                    switch (funct3) {
                    case 0: /* c.sub */
                        write_reg(rd, (intx_t)(read_reg(rd) - read_reg(rs2)));
                        break;
                    case 1: /* c.xor */
                        write_reg(rd, read_reg(rd) ^ read_reg(rs2));
                        break;
                    case 2: /* c.or */
                        write_reg(rd, read_reg(rd) | read_reg(rs2));
                        break;
                    case 3: /* c.and */
                        write_reg(rd, read_reg(rd) & read_reg(rs2));
                        break;
#if XLEN >= 64
                    case 4: /* c.subw */
                        write_reg(rd, (int32_t)(read_reg(rd) - read_reg(rs2)));
                        break;
                    case 5: /* c.addw */
                        write_reg(rd, (int32_t)(read_reg(rd) + read_reg(rs2)));
                        break;
#endif
                    default:
                        goto illegal_insn;
                    }
                    break;
                }
                break;
            case 5: /* c.j */
                imm = sext(get_field1(insn, 12, 11, 11) |
                           get_field1(insn, 11, 4, 4) |
                           get_field1(insn, 9, 8, 9) |
                           get_field1(insn, 8, 10, 10) |
                           get_field1(insn, 7, 6, 6) |
                           get_field1(insn, 6, 7, 7) |
                           get_field1(insn, 3, 1, 3) |
                           get_field1(insn, 2, 5, 5), 12);
                s->pc = (intx_t)(GET_PC() + imm);
                JUMP_INSN(ctf_taken_jump);
            case 6: /* c.beqz */
                rs1 = ((insn >> 7) & 7) | 8;
                imm = sext(get_field1(insn, 12, 8, 8) |
                           get_field1(insn, 10, 3, 4) |
                           get_field1(insn, 5, 6, 7) |
                           get_field1(insn, 3, 1, 2) |
                           get_field1(insn, 2, 5, 5), 9);
                if (read_reg(rs1) == 0) {
                    s->pc = (intx_t)(GET_PC() + imm);
                    JUMP_INSN(ctf_taken_branch);
                }
                break;
            case 7: /* c.bnez */
                rs1 = ((insn >> 7) & 7) | 8;
                imm = sext(get_field1(insn, 12, 8, 8) |
                           get_field1(insn, 10, 3, 4) |
                           get_field1(insn, 5, 6, 7) |
                           get_field1(insn, 3, 1, 2) |
                           get_field1(insn, 2, 5, 5), 9);
                if (read_reg(rs1) != 0) {
                    s->pc = (intx_t)(GET_PC() + imm);
                    JUMP_INSN(ctf_taken_branch);
                }
                break;
            default:
                goto illegal_insn;
            }
            C_NEXT_INSN;
        C_QUADRANT(2)
            funct3 = (insn >> 13) & 7;
            rs2 = (insn >> 2) & 0x1f;
            switch (funct3) {
            case 0: /* c.slli */
                imm = get_field1(insn, 12, 5, 5) | rs2;
#if XLEN == 32
                if (imm & 0x20)
                    goto illegal_insn;
#elif XLEN == 128
                if (imm == 0)
                    imm = 64;
#endif
                if (rd != 0)
                    write_reg(rd, (intx_t)(read_reg(rd) << imm));
                break;
#if XLEN == 128
            case 1: /* c.lqsp */
                if (rd == 0)
                    goto illegal_insn;
                imm = get_field1(insn, 12, 5, 5) |
                    (rs2 & (1 << 4)) |
                    get_field1(insn, 2, 6, 9);
                addr = (intx_t)(read_reg(2) + imm);
                if (target_read_u128(s, &val, addr))
                    goto mmu_exception;
                if (rd != 0)
                    write_reg(rd, val);
                break;
#elif FLEN >= 64
            case 1: /* c.fldsp */
                {
                    uint64_t rval;
                    if (s->fs == 0)
                        goto illegal_insn;
                    imm = get_field1(insn, 12, 5, 5) |
                        (rs2 & (3 << 3)) |
                        get_field1(insn, 2, 6, 8);
                    addr = (intx_t)(read_reg(2) + imm);
                    if (target_read_u64(s, &rval, addr))
                        goto mmu_exception;
                    write_fp_reg(rd, rval | F64_HIGH);
                }
                break;
#endif
            case 2: /* c.lwsp */
                {
                    uint32_t rval;
                    if (rd == 0)
                        goto illegal_insn;
                    imm = get_field1(insn, 12, 5, 5) |
                        (rs2 & (7 << 2)) |
                        get_field1(insn, 2, 6, 7);
                    addr = (intx_t)(read_reg(2) + imm);
                    if (target_read_u32(s, &rval, addr))
                        goto mmu_exception;
                    write_reg(rd, (int32_t)rval);
                }
                break;
#if XLEN >= 64
            case 3: /* c.ldsp */
                {
                    uint64_t rval;
                    if (rd == 0)
                        goto illegal_insn;
                    imm = get_field1(insn, 12, 5, 5) |
                        (rs2 & (3 << 3)) |
                        get_field1(insn, 2, 6, 8);
                    addr = (intx_t)(read_reg(2) + imm);
                    if (target_read_u64(s, &rval, addr))
                        goto mmu_exception;
                    write_reg(rd, (int64_t)rval);
                }
                break;
#elif FLEN >= 32
            case 3: /* c.flwsp */
                {
                    uint32_t rval;
                    if (s->fs == 0)
                        goto illegal_insn;
                    imm = get_field1(insn, 12, 5, 5) |
                        (rs2 & (7 << 2)) |
                        get_field1(insn, 2, 6, 7);
                    addr = (intx_t)(read_reg(2) + imm);
                    if (target_read_u32(s, &rval, addr))
                        goto mmu_exception;
                    write_fp_reg(rd, rval | F32_HIGH);
                }
                break;
#endif
            case 4:
                if (((insn >> 12) & 1) == 0) {
                    if (rs2 == 0) {
                        /* c.jr */
                        if (rd == 0)
                            goto illegal_insn;
                        s->pc = read_reg(rd) & ~1;
                        JUMP_INSN(ctf_compute_hint(0, rd));
                    } else {
                        /* c.mv */
                        if (rd != 0)
                            write_reg(rd, read_reg(rs2));
                    }
                } else {
                    if (rs2 == 0) {
                        if (rd == 0) {
                            /* c.ebreak */
                            s->pending_exception = CAUSE_BREAKPOINT;
                            s->pending_tval = 0;
                            goto exception;
                        } else {
                            /* c.jalr */
                            val = GET_PC() + 2;
                            s->pc = read_reg(rd) & ~1;
                            write_reg(1, val);
                            JUMP_INSN(ctf_compute_hint(1, rd));
                        }
                    } else {
                        if (rd != 0)
                            write_reg(rd, (intx_t)(read_reg(rd) + read_reg(rs2)));
                    }
                }
                break;
#if XLEN == 128
            case 5: /* c.sqsp */
                imm = get_field1(insn, 10, 3, 5) |
                    get_field1(insn, 7, 6, 8);
                addr = (intx_t)(read_reg(2) + imm);
                if (target_write_u128(s, addr, read_reg(rs2)))
                    goto mmu_exception;
                break;
#elif FLEN >= 64
            case 5: /* c.fsdsp */
                if (s->fs == 0)
                    goto illegal_insn;
                imm = get_field1(insn, 10, 3, 5) |
                    get_field1(insn, 7, 6, 8);
                addr = (intx_t)(read_reg(2) + imm);
                if (target_write_u64(s, addr, read_fp_reg(rs2)))
                    goto mmu_exception;
                break;
#endif
            case 6: /* c.swsp */
                imm = get_field1(insn, 9, 2, 5) |
                    get_field1(insn, 7, 6, 7);
                addr = (intx_t)(read_reg(2) + imm);
                if (target_write_u32(s, addr, read_reg(rs2)))
                    goto mmu_exception;
                break;
#if XLEN >= 64
            case 7: /* c.sdsp */
                imm = get_field1(insn, 10, 3, 5) |
                    get_field1(insn, 7, 6, 8);
                addr = (intx_t)(read_reg(2) + imm);
                if (target_write_u64(s, addr, read_reg(rs2)))
                    goto mmu_exception;
                break;
#elif FLEN >= 32
            case 7: /* c.swsp */
                if (s->fs == 0)
                    goto illegal_insn;
                imm = get_field1(insn, 9, 2, 5) |
                    get_field1(insn, 7, 6, 7);
                addr = (intx_t)(read_reg(2) + imm);
                if (target_write_u32(s, addr, read_fp_reg(rs2)))
                    goto mmu_exception;
                break;
#endif
            default:
                goto illegal_insn;
            }
            C_NEXT_INSN;

        case 0x37: /* lui */
            if (rd != 0)
                write_reg(rd, (int32_t)(insn & 0xfffff000));
            NEXT_INSN;
        case 0x17: /* auipc */
            if (rd != 0)
                write_reg(rd, (intx_t)(GET_PC() + (int32_t)(insn & 0xfffff000)));
            NEXT_INSN;
        case 0x6f: /* jal */
            imm = ((insn >> (31 - 20)) & (1 << 20)) |
                ((insn >> (21 - 1)) & 0x7fe) |
                ((insn >> (20 - 11)) & (1 << 11)) |
                (insn & 0xff000);
            imm = (imm << 11) >> 11;
            {
                intx_t new_pc = (intx_t)(GET_PC() + imm);
                if (!(s->misa & MCPUID_C) && (new_pc & 3) != 0) {
                    s->pending_exception = CAUSE_MISALIGNED_FETCH;
                    s->pending_tval = 0;
                    goto exception;
                }
            }
            if (rd != 0)
                write_reg(rd, GET_PC() + 4);
            s->pc = (intx_t)(GET_PC() + imm);
            JUMP_INSN(ctf_taken_jump);
        case 0x67: /* jalr */
            funct3 = (insn >> 12) & 7;
            if (funct3 != 0)
                goto illegal_insn;
            imm = (int32_t)insn >> 20;
            val = GET_PC() + 4;
            {
                intx_t new_pc = (intx_t)(read_reg(rs1) + imm) & ~1;
                if (!(s->misa & MCPUID_C) && (new_pc & 3) != 0) {
                    s->pending_exception = CAUSE_MISALIGNED_FETCH;
                    s->pending_tval = 0;
                    goto exception;
                }
            }
            s->pc = (intx_t)(read_reg(rs1) + imm) & ~1;
            if (rd != 0)
                write_reg(rd, val);
            JUMP_INSN(ctf_compute_hint(rd, rs1));
        case 0x63:
            funct3 = (insn >> 12) & 7;
            switch (funct3 >> 1) {
            case 0: /* beq/bne */
                cond = (read_reg(rs1) == read_reg(rs2));
                break;
            case 2: /* blt/bge */
                cond = ((target_long)read_reg(rs1) < (target_long)read_reg(rs2));
                break;
            case 3: /* bltu/bgeu */
                cond = (read_reg(rs1) < read_reg(rs2));
                break;
            default:
                goto illegal_insn;
            }
            cond ^= (funct3 & 1);
            if (cond) {
                imm = ((insn >> (31 - 12)) & (1 << 12)) |
                    ((insn >> (25 - 5)) & 0x7e0) |
                    ((insn >> (8 - 1)) & 0x1e) |
                    ((insn << (11 - 7)) & (1 << 11));
                imm = (imm << 19) >> 19;

                intx_t new_pc = (intx_t)(GET_PC() + imm);
                if (!(s->misa & MCPUID_C) && (new_pc & 3) != 0) {
                    s->pending_exception = CAUSE_MISALIGNED_FETCH;
                    s->pending_tval = 0;
                    goto exception;
                }

                s->pc = (intx_t)(GET_PC() + imm);
                JUMP_INSN(ctf_taken_branch);
            }
            NEXT_INSN;
        case 0x03: /* load */
            funct3 = (insn >> 12) & 7;
            imm = (int32_t)insn >> 20;
            addr = read_reg(rs1) + imm;
            switch (funct3) {
            case 0: /* lb */
                {
                    uint8_t rval;
                    if (target_read_u8(s, &rval, addr))
                        goto mmu_exception;
                    val = (int8_t)rval;
                }
                break;
            case 1: /* lh */
                {
                    uint16_t rval;
                    if (target_read_u16(s, &rval, addr))
                        goto mmu_exception;
                    val = (int16_t)rval;
                }
                break;
            case 2: /* lw */
                {
                    uint32_t rval;
                    if (target_read_u32(s, &rval, addr))
                        goto mmu_exception;
                    val = (int32_t)rval;
                }
                break;
            case 4: /* lbu */
                {
                    uint8_t rval;
                    if (target_read_u8(s, &rval, addr))
                        goto mmu_exception;
                    val = rval;
                }
                break;
            case 5: /* lhu */
                {
                    uint16_t rval;
                    if (target_read_u16(s, &rval, addr))
                        goto mmu_exception;
                    val = rval;
                }
                break;
#if XLEN >= 64
            case 3: /* ld */
                {
                    uint64_t rval;
                    if (target_read_u64(s, &rval, addr))
                        goto mmu_exception;
                    val = (int64_t)rval;
                }
                break;
            case 6: /* lwu */
                {
                    uint32_t rval;
                    if (target_read_u32(s, &rval, addr))
                        goto mmu_exception;
                    val = rval;
                }
                break;
#endif
#if XLEN >= 128
            case 7: /* ldu */
                {
                    uint64_t rval;
                    if (target_read_u64(s, &rval, addr))
                        goto mmu_exception;
                    val = rval;
                }
                break;
#endif
            default:
                goto illegal_insn;
            }
            if (rd != 0)
                write_reg(rd, val);
            NEXT_INSN;
        case 0x23: /* store */
            funct3 = (insn >> 12) & 7;
            imm = rd | ((insn >> (25 - 5)) & 0xfe0);
            imm = (imm << 20) >> 20;
            addr = read_reg(rs1) + imm;
            val = read_reg(rs2);
            switch (funct3) {
            case 0: /* sb */
                if (target_write_u8(s, addr, val))
                    goto mmu_exception;
                break;
            case 1: /* sh */
                if (target_write_u16(s, addr, val))
                    goto mmu_exception;
                break;
            case 2: /* sw */
                if (target_write_u32(s, addr, val))
                    goto mmu_exception;
                break;
#if XLEN >= 64
            case 3: /* sd */
                if (target_write_u64(s, addr, val))
                    goto mmu_exception;
                break;
#endif
#if XLEN >= 128
            case 4: /* sq */
                if (target_write_u128(s, addr, val))
                    goto mmu_exception;
                break;
#endif
            default:
                goto illegal_insn;
            }
            NEXT_INSN;
        case 0x13:
            funct3 = (insn >> 12) & 7;
            imm = (int32_t)insn >> 20;
            switch (funct3) {
            case 0: /* addi */
                val = (intx_t)(read_reg(rs1) + imm);
                break;
            case 1: /* slli */
                if ((imm & ~(XLEN - 1)) != 0)
                    goto illegal_insn;
                val = (intx_t)(read_reg(rs1) << (imm & (XLEN - 1)));
                break;
            case 2: /* slti */
                val = (target_long)read_reg(rs1) < (target_long)imm;
                break;
            case 3: /* sltiu */
                val = read_reg(rs1) < (target_ulong)imm;
                break;
            case 4: /* xori */
                val = read_reg(rs1) ^ imm;
                break;
            case 5: /* srli/srai */
                if ((imm & ~((XLEN - 1) | 0x400)) != 0)
                    goto illegal_insn;
                if (imm & 0x400)
                    val = (intx_t)read_reg(rs1) >> (imm & (XLEN - 1));
                else
                    val = (intx_t)((uintx_t)read_reg(rs1) >> (imm & (XLEN - 1)));
                break;
            case 6: /* ori */
                val = read_reg(rs1) | imm;
                break;
            default:
            case 7: /* andi */
                val = read_reg(rs1) & imm;
                break;
            }
            if (rd != 0)
                write_reg(rd, val);
            NEXT_INSN;
#if XLEN >= 64
        case 0x1b:/* OP-IMM-32 */
            funct3 = (insn >> 12) & 7;
            imm = (int32_t)insn >> 20;
            val = read_reg(rs1);
            switch (funct3) {
            case 0: /* addiw */
                val = (int32_t)(val + imm);
                break;
            case 1: /* slliw */
                if ((imm & ~31) != 0)
                    goto illegal_insn;
                val = (int32_t)(val << (imm & 31));
                break;
            case 5: /* srliw/sraiw */
                if ((imm & ~(31 | 0x400)) != 0)
                    goto illegal_insn;
                if (imm & 0x400)
                    val = (int32_t)val >> (imm & 31);
                else
                    val = (int32_t)((uint32_t)val >> (imm & 31));
                break;
            default:
                goto illegal_insn;
            }
            if (rd != 0)
                write_reg(rd, val);
            NEXT_INSN;
#endif
#if XLEN >= 128
        case 0x5b: /* OP-IMM-64 */
            funct3 = (insn >> 12) & 7;
            imm = (int32_t)insn >> 20;
            val = read_reg(rs1);
            switch (funct3) {
            case 0: /* addid */
                val = (int64_t)(val + imm);
                break;
            case 1: /* sllid */
                if ((imm & ~63) != 0)
                    goto illegal_insn;
                val = (int64_t)(val << (imm & 63));
                break;
            case 5: /* srlid/sraid */
                if ((imm & ~(63 | 0x400)) != 0)
                    goto illegal_insn;
                if (imm & 0x400)
                    val = (int64_t)val >> (imm & 63);
                else
                    val = (int64_t)((uint64_t)val >> (imm & 63));
                break;
            default:
                goto illegal_insn;
            }
            if (rd != 0)
                write_reg(rd, val);
            NEXT_INSN;
#endif
        case 0x33:
            imm = insn >> 25;
            val = read_reg(rs1);
            val2 = read_reg(rs2);
            if (imm == 1) {
                funct3 = (insn >> 12) & 7;
                switch (funct3) {
                case 0: /* mul */
                    val = (intx_t)((intx_t)val * (intx_t)val2);
                    break;
                case 1: /* mulh */
                    val = (intx_t)glue(mulh, XLEN)(val, val2);
                    break;
                case 2:/* mulhsu */
                    val = (intx_t)glue(mulhsu, XLEN)(val, val2);
                    break;
                case 3:/* mulhu */
                    val = (intx_t)glue(mulhu, XLEN)(val, val2);
                    break;
                case 4:/* div */
                    val = glue(div, XLEN)(val, val2);
                    break;
                case 5:/* divu */
                    val = (intx_t)glue(divu, XLEN)(val, val2);
                    break;
                case 6:/* rem */
                    val = glue(rem, XLEN)(val, val2);
                    break;
                case 7:/* remu */
                    val = (intx_t)glue(remu, XLEN)(val, val2);
                    break;
                default:
                    goto illegal_insn;
                }
            } else {
                if (imm & ~0x20)
                    goto illegal_insn;
                funct3 = ((insn >> 12) & 7) | ((insn >> (30 - 3)) & (1 << 3));
                switch (funct3) {
                case 0: /* add */
                    val = (intx_t)(val + val2);
                    break;
                case 0 | 8: /* sub */
                    val = (intx_t)(val - val2);
                    break;
                case 1: /* sll */
                    val = (intx_t)(val << (val2 & (XLEN - 1)));
                    break;
                case 2: /* slt */
                    val = (target_long)val < (target_long)val2;
                    break;
                case 3: /* sltu */
                    val = val < val2;
                    break;
                case 4: /* xor */
                    val = val ^ val2;
                    break;
                case 5: /* srl */
                    val = (intx_t)((uintx_t)val >> (val2 & (XLEN - 1)));
                    break;
                case 5 | 8: /* sra */
                    val = (intx_t)val >> (val2 & (XLEN - 1));
                    break;
                case 6: /* or */
                    val = val | val2;
                    break;
                case 7: /* and */
                    val = val & val2;
                    break;
                default:
                    goto illegal_insn;
                }
            }
            if (rd != 0)
                write_reg(rd, val);
            NEXT_INSN;
#if XLEN >= 64
        case 0x3b: /* OP-32 */
            imm = insn >> 25;
            val = read_reg(rs1);
            val2 = read_reg(rs2);
            if (imm == 1) {
                funct3 = (insn >> 12) & 7;
                switch (funct3) {
                case 0: /* mulw */
                    val = (int32_t)((int32_t)val * (int32_t)val2);
                    break;
                case 4:/* divw */
                    val = div32(val, val2);
                    break;
                case 5:/* divuw */
                    val = (int32_t)divu32(val, val2);
                    break;
                case 6:/* remw */
                    val = rem32(val, val2);
                    break;
                case 7:/* remuw */
                    val = (int32_t)remu32(val, val2);
                    break;
                default:
                    goto illegal_insn;
                }
            } else {
                if (imm & ~0x20)
                    goto illegal_insn;
                funct3 = ((insn >> 12) & 7) | ((insn >> (30 - 3)) & (1 << 3));
                switch (funct3) {
                case 0: /* addw */
                    val = (int32_t)(val + val2);
                    break;
                case 0 | 8: /* subw */
                    val = (int32_t)(val - val2);
                    break;
                case 1: /* sllw */
                    val = (int32_t)((uint32_t)val << (val2 & 31));
                    break;
                case 5: /* srlw */
                    val = (int32_t)((uint32_t)val >> (val2 & 31));
                    break;
                case 5 | 8: /* sraw */
                    val = (int32_t)val >> (val2 & 31);
                    break;
                default:
                    goto illegal_insn;
                }
            }
            if (rd != 0)
                write_reg(rd, val);
            NEXT_INSN;
#endif
#if XLEN >= 128
        case 0x7b: /* OP-64 */
            imm = insn >> 25;
            val = read_reg(rs1);
            val2 = read_reg(rs2);
            if (imm == 1) {
                funct3 = (insn >> 12) & 7;
                switch (funct3) {
                case 0: /* muld */
                    val = (int64_t)((int64_t)val * (int64_t)val2);
                    break;
                case 4:/* divd */
                    val = div64(val, val2);
                    break;
                case 5:/* divud */
                    val = (int64_t)divu64(val, val2);
                    break;
                case 6:/* remd */
                    val = rem64(val, val2);
                    break;
                case 7:/* remud */
                    val = (int64_t)remu64(val, val2);
                    break;
                default:
                    goto illegal_insn;
                }
            } else {
                if (imm & ~0x20)
                    goto illegal_insn;
                funct3 = ((insn >> 12) & 7) | ((insn >> (30 - 3)) & (1 << 3));
                switch (funct3) {
                case 0: /* addd */
                    val = (int64_t)(val + val2);
                    break;
                case 0 | 8: /* subd */
                    val = (int64_t)(val - val2);
                    break;
                case 1: /* slld */
                    val = (int64_t)((uint64_t)val << (val2 & 63));
                    break;
                case 5: /* srld */
                    val = (int64_t)((uint64_t)val >> (val2 & 63));
                    break;
                case 5 | 8: /* srad */
                    val = (int64_t)val >> (val2 & 63);
                    break;
                default:
                    goto illegal_insn;
                }
            }
            if (rd != 0)
                write_reg(rd, val);
            NEXT_INSN;
#endif
        case 0x73:
            funct3 = (insn >> 12) & 7;
            imm = insn >> 20;
            if (funct3 & 4)
                val = rs1;
            else
                val = read_reg(rs1);
            funct3 &= 3;
            switch (funct3) {
            case 1: /* csrrw */
                s->insn_counter = GET_INSN_COUNTER();
                if (!s->stop_the_counter) {
                  int delta = s->insn_counter - insn_counter_start;
                  assert(delta >= 0);
                  s->mcycle += delta;
                  s->minstret += delta;
                }
                if (csr_read(s, &val2, imm, TRUE))
                    goto illegal_insn;
                val2 = (intx_t)val2;
                err = csr_write(s, imm, val);
                if (err == -2)
                    goto mmu_exception;
                if (err < 0)
                    goto illegal_insn;
                if (rd != 0)
                    write_reg(rd, val2);
                insn_counter_addend = s->insn_counter + n_cycles;
                if (err > 0) {
                    s->pc = GET_PC() + 4;
                    if (err == 2)
                        JUMP_INSN(ctf_nop);
                    else
                        goto done_interp;
                }
                break;
            case 2: /* csrrs */
            case 3: /* csrrc */
                s->insn_counter = GET_INSN_COUNTER();
                if (!s->stop_the_counter) {
                  int delta = s->insn_counter - insn_counter_start;
                  assert(delta >= 0);
                  s->mcycle += delta;
                  s->minstret += delta;
                }
                if (csr_read(s, &val2, imm, (rs1 != 0)))
                    goto illegal_insn;
                val2 = (intx_t)val2;
                if (rs1 != 0) {
                    if (funct3 == 2)
                        val = val2 | val;
                    else
                        val = val2 & ~val;
                    err = csr_write(s, imm, val);
                    if (err == -2)
                        goto mmu_exception;
                    if (err < 0)
                        goto illegal_insn;
                } else {
                    err = 0;
                }
                if (rd != 0)
                    write_reg(rd, val2);
                if (err > 0) {
                    s->pc = GET_PC() + 4;
                    if (err == 2)
                        JUMP_INSN(ctf_nop);
                    else
                        goto done_interp;
                }
                break;
            case 0:
                switch (imm) {
                case 0x000: /* ecall */
                    if (insn & 0x000fff80)
                        goto illegal_insn;
                    s->pending_exception = CAUSE_USER_ECALL + s->priv;
                    s->pending_tval = 0;
                    /* Intercept SBI_SHUTDOWN, that is, ecall with a7 == SBI_SHUTDOWN */
                    if (!s->ignore_sbi_shutdown && s->priv == PRV_M && read_reg(0x17) == SBI_SHUTDOWN)
                        s->terminate_simulation = 1;
                    goto exception;
                case 0x001: /* ebreak */
                    if (insn & 0x000fff80)
                        goto illegal_insn;
                    s->pending_exception = CAUSE_BREAKPOINT;
                    s->pending_tval = 0;
                    goto exception;
                case 0x102: /* sret */
                    {
                        if (insn & 0x000fff80)
                            goto illegal_insn;
                        if (s->priv < PRV_S)
                            goto illegal_insn;
                        if (s->priv == PRV_S && s->mstatus & MSTATUS_TSR)
                            goto illegal_insn;
                        s->pc = GET_PC();
                        handle_sret(s);
                        goto done_interp;
                    }
                    break;
                case 0x302: /* mret */
                    {
                        if (insn & 0x000fff80)
                            goto illegal_insn;
                        if (s->priv < PRV_M)
                            goto illegal_insn;
                        s->pc = GET_PC();
                        handle_mret(s);
                        goto done_interp;
                    }
                    break;
                case 0x7b2: /* dret */
                    if (!s->debug_mode) goto illegal_insn;
                    {
                        if (insn & 0x000fff80)
                            goto illegal_insn;
                        if (s->priv < PRV_M) // FIXME: It should be illegal even in M, but this is the only that we have now
                            goto illegal_insn;
                        s->pc = GET_PC();
                        handle_dret(s);
                        goto done_interp;
                    }
                    break;
                case 0x105: /* wfi */
                    if (insn & 0x00007f80)
                        goto illegal_insn;
                    if (s->priv == PRV_U)
                        goto illegal_insn;
                    /* "When TW=1, if WFI is executed in S- mode, and
                       it does not complete within an
                       implementation-specific, bounded time limit,
                       the WFI instruction causes an illegal
                       instruction trap." */
                    if (s->priv == PRV_S && s->mstatus & MSTATUS_TW)
                        goto illegal_insn;
                    /* go to power down if no enabled interrupts are
                       pending */
                    if (((s->mip & s->mie) == 0) && (s->machine->common.pending_interrupt == -1) || !s->machine->common.cosim) {
                        s->power_down_flag = TRUE;
                        s->pc = GET_PC() + 4;
                        goto done_interp;
                    }
                    break;
                default:
                    if ((imm >> 5) == 0x09) {
                        /* sfence.vma */
                        if (insn & 0x00007f80)
                            goto illegal_insn;
                        if (s->priv == PRV_U)
                            goto illegal_insn;
                        if (s->priv == PRV_S && s->mstatus & MSTATUS_TVM)
                            goto illegal_insn;
                        if (rs1 == 0) {
                            tlb_flush_all(s);
                        } else {
                            tlb_flush_vaddr(s, read_reg(rs1));
                        }
                        /* the current code TLB may have been flushed */
                        s->pc = GET_PC() + 4;
                        JUMP_INSN(ctf_nop);
                    } else {
                        goto illegal_insn;
                    }
                    break;
                }
                break;
            default:
                goto illegal_insn;
            }
            NEXT_INSN;
        case 0x0f: /* misc-mem */
            funct3 = (insn >> 12) & 7;
            switch (funct3) {
            case 0: /* fence */
                if (insn & 0xf00fff80)
                    goto illegal_insn;
                break;
            case 1: /* fence.i */
                if (insn != 0x0000100f)
                    goto illegal_insn;
                break;
#if XLEN >= 128
            case 2: /* lq */
                imm = (int32_t)insn >> 20;
                addr = read_reg(rs1) + imm;
                if (target_read_u128(s, &val, addr))
                    goto mmu_exception;
                if (rd != 0)
                    write_reg(rd, val);
                break;
#endif
            default:
                goto illegal_insn;
            }
            NEXT_INSN;
        case 0x2f:
            funct3 = (insn >> 12) & 7;
#define OP_A(size)                                                      \
            {                                                           \
                uint ## size ##_t rval;                                 \
                                                                        \
                addr = read_reg(rs1);                                   \
                funct3 = insn >> 27;                                    \
                switch (funct3) {                                       \
                case 2: /* lr.w */                                      \
                    if (rs2 != 0)                                       \
                        goto illegal_insn;                              \
                    if (target_read_u ## size(s, &rval, addr))          \
                        goto mmu_exception;                             \
                    val = (int## size ## _t)rval;                       \
                    s->load_res = addr;                                 \
                    break;                                              \
                                                                        \
                case 3: /* sc.w */                                      \
                                                                        \
                    if ((addr & (size/8 - 1)) != 0) {                   \
                        s->pending_tval = addr;                         \
                        s->pending_exception = CAUSE_MISALIGNED_STORE;  \
                        goto mmu_exception;                             \
                    }                                                   \
                                                                        \
                    if (s->load_res == addr) {                          \
                        if (target_write_u ## size(s, addr, read_reg(rs2))) \
                            goto mmu_exception;                         \
                        val = 0;                                        \
                        s->load_res = ~0;                               \
                    } else {                                            \
                        val = 1;                                        \
                    }                                                   \
                    break;                                              \
                case 1: /* amiswap.w */                                 \
                case 0: /* amoadd.w */                                  \
                case 4: /* amoxor.w */                                  \
                case 0xc: /* amoand.w */                                \
                case 0x8: /* amoor.w */                                 \
                case 0x10: /* amomin.w */                               \
                case 0x14: /* amomax.w */                               \
                case 0x18: /* amominu.w */                              \
                case 0x1c: /* amomaxu.w */                              \
                    if (target_read_u ## size(s, &rval, addr)) {        \
                        s->pending_exception += 2; /* LD -> ST */       \
                        goto mmu_exception;                             \
                    }                                                   \
                    val = (int## size ## _t)rval;                       \
                    val2 = read_reg(rs2);                               \
                    switch (funct3) {                                    \
                    case 1: /* amiswap.w */                             \
                        break;                                          \
                    case 0: /* amoadd.w */                              \
                        val2 = (int## size ## _t)(val + val2);          \
                        break;                                          \
                    case 4: /* amoxor.w */                              \
                        val2 = (int## size ## _t)(val ^ val2);          \
                        break;                                          \
                    case 0xc: /* amoand.w */                            \
                        val2 = (int## size ## _t)(val & val2);          \
                        break;                                          \
                    case 0x8: /* amoor.w */                             \
                        val2 = (int## size ## _t)(val | val2);          \
                        break;                                          \
                    case 0x10: /* amomin.w */                           \
                        if ((int## size ## _t)val < (int## size ## _t)val2) \
                            val2 = (int## size ## _t)val;               \
                        break;                                          \
                    case 0x14: /* amomax.w */                           \
                        if ((int## size ## _t)val > (int## size ## _t)val2) \
                            val2 = (int## size ## _t)val;               \
                        break;                                          \
                    case 0x18: /* amominu.w */                          \
                        if ((uint## size ## _t)val < (uint## size ## _t)val2) \
                            val2 = (int## size ## _t)val;               \
                        break;                                          \
                    case 0x1c: /* amomaxu.w */                          \
                        if ((uint## size ## _t)val > (uint## size ## _t)val2) \
                            val2 = (int## size ## _t)val;               \
                        break;                                          \
                    default:                                            \
                        goto illegal_insn;                              \
                    }                                                   \
                    if (target_write_u ## size(s, addr, val2))          \
                        goto mmu_exception;                             \
                    break;                                              \
                default:                                                \
                    goto illegal_insn;                                  \
                }                                                       \
            }

            switch (funct3) {
            case 2:
                OP_A(32);
                break;
#if XLEN >= 64
            case 3:
                OP_A(64);
                break;
#endif
#if XLEN >= 128
            case 4:
                OP_A(128);
                break;
#endif
            default:
                goto illegal_insn;
            }
            if (rd != 0)
                write_reg(rd, val);
            NEXT_INSN;
#if FLEN > 0
            /* FPU */
        case 0x07: /* fp load */
            if (s->fs == 0)
                goto illegal_insn;
            funct3 = (insn >> 12) & 7;
            imm = (int32_t)insn >> 20;
            addr = read_reg(rs1) + imm;
            switch (funct3) {
            case 2: /* flw */
                {
                    uint32_t rval;
                    if (target_read_u32(s, &rval, addr))
                        goto mmu_exception;
                    write_fp_reg(rd, rval | F32_HIGH);
                }
                break;
#if FLEN >= 64
            case 3: /* fld */
                {
                    uint64_t rval;
                    if (target_read_u64(s, &rval, addr))
                        goto mmu_exception;
                    write_fp_reg(rd, rval | F64_HIGH);
                }
                break;
#endif
#if FLEN >= 128
            case 4: /* flq */
                {
                    uint128_t rval;
                    if (target_read_u128(s, &rval, addr))
                        goto mmu_exception;
                    write_fp_reg(rd, rval);
                }
                break;
#endif
            default:
                goto illegal_insn;
            }
            NEXT_INSN;
        case 0x27: /* fp store */
            if (s->fs == 0)
                goto illegal_insn;
            funct3 = (insn >> 12) & 7;
            imm = rd | ((insn >> (25 - 5)) & 0xfe0);
            imm = (imm << 20) >> 20;
            addr = read_reg(rs1) + imm;
            switch (funct3) {
            case 2: /* fsw */
                if (target_write_u32(s, addr, read_fp_reg(rs2)))
                    goto mmu_exception;
                break;
#if FLEN >= 64
            case 3: /* fsd */
                if (target_write_u64(s, addr, read_fp_reg(rs2)))
                    goto mmu_exception;
                break;
#endif
#if FLEN >= 128
            case 4: /* fsq */
                if (target_write_u128(s, addr, read_fp_reg(rs2)))
                    goto mmu_exception;
                break;
#endif
            default:
                goto illegal_insn;
            }
            NEXT_INSN;
        case 0x43: /* fmadd */
            if (s->fs == 0)
                goto illegal_insn;
            funct3 = (insn >> 25) & 3;
            rs3 = insn >> 27;
            rm = get_insn_rm(s, (insn >> 12) & 7);
            if (rm < 0)
                goto illegal_insn;
            switch (funct3) {
            case 0:
                write_fp_reg(rd, (fp_uint)fma_sf32(chkfp32(read_fp_reg(rs1)),
                                          chkfp32(read_fp_reg(rs2)),
                                          chkfp32(read_fp_reg(rs3)),
                                          (RoundingModeEnum)rm, &s->fflags) | F32_HIGH);
                break;
#if FLEN >= 64
            case 1:
                write_fp_reg(rd, (fp_uint)fma_sf64(read_fp_reg(rs1),
                                          read_fp_reg(rs2),
                                          read_fp_reg(rs3),
                                          (RoundingModeEnum)rm, &s->fflags) | F64_HIGH);
                break;
#endif
#if FLEN >= 128
            case 3:
                write_fp_reg(rd, (fp_uint)fma_sf128(read_fp_reg(rs1),
                                           read_fp_reg(rs2),
                                           read_fp_reg(rs3),
                                           (RoundingModeEnum)rm, &s->fflags));;
#endif
            default:
                goto illegal_insn;
            }
            NEXT_INSN;
        case 0x47: /* fmsub */
            if (s->fs == 0)
                goto illegal_insn;
            funct3 = (insn >> 25) & 3;
            rs3 = insn >> 27;
            rm = get_insn_rm(s, (insn >> 12) & 7);
            if (rm < 0)
                goto illegal_insn;
            switch (funct3) {
            case 0:
                write_fp_reg(rd, fma_sf32(chkfp32(read_fp_reg(rs1)),
                                          chkfp32(read_fp_reg(rs2)),
                                          chkfp32(read_fp_reg(rs3)) ^ FSIGN_MASK32,
                                          (RoundingModeEnum)rm, &s->fflags) | F32_HIGH);
                break;
#if FLEN >= 64
            case 1:
                write_fp_reg(rd, fma_sf64(read_fp_reg(rs1),
                                          read_fp_reg(rs2),
                                          read_fp_reg(rs3) ^ FSIGN_MASK64,
                                          (RoundingModeEnum)rm, &s->fflags) | F64_HIGH);
                break;
#endif
#if FLEN >= 128
            case 3:
                write_fp_reg(rd, fma_sf128(read_fp_reg(rs1),
                                           read_fp_reg(rs2),
                                           read_fp_reg(rs3) ^ FSIGN_MASK128,
                                           (RoundingModeEnum)rm, &s->fflags));
                break;
#endif
            default:
                goto illegal_insn;
            }
            NEXT_INSN;
        case 0x4b: /* fnmsub */
            if (s->fs == 0)
                goto illegal_insn;
            funct3 = (insn >> 25) & 3;
            rs3 = insn >> 27;
            rm = get_insn_rm(s, (insn >> 12) & 7);
            if (rm < 0)
                goto illegal_insn;
            switch (funct3) {
            case 0:
                write_fp_reg(rd, fma_sf32(chkfp32(read_fp_reg(rs1)) ^ FSIGN_MASK32,
                                          chkfp32(read_fp_reg(rs2)),
                                          chkfp32(read_fp_reg(rs3)),
                                          (RoundingModeEnum)rm, &s->fflags) | F32_HIGH);
                break;
#if FLEN >= 64
            case 1:
                write_fp_reg(rd, fma_sf64(read_fp_reg(rs1) ^ FSIGN_MASK64,
                                          read_fp_reg(rs2),
                                          read_fp_reg(rs3),
                                          (RoundingModeEnum)rm, &s->fflags) | F64_HIGH);
                break;
#endif
#if FLEN >= 128
            case 3:
                write_fp_reg(rd, fma_sf128(read_fp_reg(rs1) ^ FSIGN_MASK128,
                                           read_fp_reg(rs2),
                                           read_fp_reg(rs3),
                                           (RoundingModeEnum)rm, &s->fflags));
                break;
#endif
            default:
                goto illegal_insn;
            }
            NEXT_INSN;
        case 0x4f: /* fnmadd */
            if (s->fs == 0)
                goto illegal_insn;
            funct3 = (insn >> 25) & 3;
            rs3 = insn >> 27;
            rm = get_insn_rm(s, (insn >> 12) & 7);
            if (rm < 0)
                goto illegal_insn;
            switch (funct3) {
            case 0:
                write_fp_reg(rd, fma_sf32(chkfp32(read_fp_reg(rs1)) ^ FSIGN_MASK32,
                                          chkfp32(read_fp_reg(rs2)),
                                          chkfp32(read_fp_reg(rs3)) ^ FSIGN_MASK32,
                                          (RoundingModeEnum)rm, &s->fflags) | F32_HIGH);
                break;
#if FLEN >= 64
            case 1:
                write_fp_reg(rd, fma_sf64(read_fp_reg(rs1) ^ FSIGN_MASK64,
                                          read_fp_reg(rs2),
                                          read_fp_reg(rs3) ^ FSIGN_MASK64,
                                          (RoundingModeEnum)rm, &s->fflags) | F64_HIGH);
                break;
#endif
#if FLEN >= 128
            case 3:
                write_fp_reg(rd, fma_sf128(read_fp_reg(rs1) ^ FSIGN_MASK128,
                                           read_fp_reg(rs2),
                                           read_fp_reg(rs3) ^ FSIGN_MASK128,
                                           (RoundingModeEnum)rm, &s->fflags));
                break;
#endif
            default:
                goto illegal_insn;
            }
            NEXT_INSN;
        case 0x53:
            if (s->fs == 0)
                goto illegal_insn;
            imm = insn >> 25;
            rm = (insn >> 12) & 7;
            switch (imm) {

#define F_SIZE 32
#include "dromajo_fp_template.h"
#if FLEN >= 64
#define F_SIZE 64
#include "dromajo_fp_template.h"
#endif
#if FLEN >= 128
#define F_SIZE 128
#include "dromajo_fp_template.h"
#endif

            default:
                goto illegal_insn;
            }
            NEXT_INSN;
#endif
        default:
            goto illegal_insn;
        }
        /* update PC for next instruction */
    jump_insn:
        ;
    } /* end of main loop */
 illegal_insn:
    s->pending_exception = CAUSE_ILLEGAL_INSTRUCTION;
    s->pending_tval = 0;
 mmu_exception:
 exception:
    s->pc = GET_PC();
    if (s->pending_exception >= 0) {
        if ((s->pending_exception < CAUSE_USER_ECALL ||
             s->pending_exception > CAUSE_USER_ECALL + 3) &&
            s->pending_exception != CAUSE_BREAKPOINT) {
            /* All other causes cancelled the instruction and shouldn't be
             * counted in minstret */
            --insn_counter_addend;
            --insn_executed;
        }

        raise_exception2(s, s->pending_exception, s->pending_tval);
    }
    /* we exit because XLEN may have changed */

done_interp:
    n_cycles--;

the_end:
    s->insn_counter = GET_INSN_COUNTER();
    if (!s->stop_the_counter) {
      int delta = s->insn_counter - insn_counter_start;
      assert(delta >= 0);
      s->mcycle += delta;
      s->minstret += delta;
    }

    return insn_executed;
}

#undef uintx_t
#undef intx_t
#undef XLEN
#undef OP_A

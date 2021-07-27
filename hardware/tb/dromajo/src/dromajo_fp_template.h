/*
 * Dromajo
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
 * THIS FILE IS BASED ON RISCVEMU SOURCE CODE WHICH IS DISTRIBUTED UNDER
 * THE FOLLOWING LICENSE:
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
#if F_SIZE == 32
#define OPID 0
#define F_HIGH F32_HIGH
#elif F_SIZE == 64
#define OPID 1
#define F_HIGH F64_HIGH
#elif F_SIZE == 128
#define OPID 3
#define F_HIGH 0
#else
#error unsupported F_SIZE
#endif

/*
  This template is included for each of F_SIZE=32 (single precision),
  F_SIZE=64 (double precision), and F_SIZE=128 (quad precision).

  unbox() checks that the value is corrected NaN-boxed _according to
  F_SIZE_.  That means, that when XLEN=F_SIZE, it's a no-op, when XLEN
  < F_SIZE it's undefined and not used.  It's only non-trivial when
  XLEN > F_SIZE (and the case we case the most about is XLEN=64 and
  F_SIZE=32.

  However, some of the instruction below are operating on two formats
  at once and care must applied to only use box() upon generic
  arguments (that is, values that depend on F_SIZE)
*/


#define unbox glue(f_unbox, F_SIZE)
#define FSIGN_MASK glue(FSIGN_MASK, F_SIZE)

            case (0x00 << 2) | OPID:
                rm = get_insn_rm(s, rm);
                if (rm < 0)
                    goto illegal_insn;
                write_fp_reg(rd, glue(add_sf, F_SIZE)(unbox(read_fp_reg(rs1)),
                                                      unbox(read_fp_reg(rs2)),
                                                      (RoundingModeEnum)rm, &s->fflags) | F_HIGH);
                s->fs = 3;
                break;
            case (0x01 << 2) | OPID:
                rm = get_insn_rm(s, rm);
                if (rm < 0)
                    goto illegal_insn;
                write_fp_reg(rd, glue(sub_sf, F_SIZE)(unbox(read_fp_reg(rs1)),
                                                      unbox(read_fp_reg(rs2)),
                                                      (RoundingModeEnum)rm, &s->fflags) | F_HIGH);
                s->fs = 3;
                break;
            case (0x02 << 2) | OPID:
                rm = get_insn_rm(s, rm);
                if (rm < 0)
                    goto illegal_insn;
                write_fp_reg(rd, glue(mul_sf, F_SIZE)(unbox(read_fp_reg(rs1)),
                                                      unbox(read_fp_reg(rs2)),
                                                      (RoundingModeEnum)rm, &s->fflags) | F_HIGH);
                s->fs = 3;
                break;
            case (0x03 << 2) | OPID:
                rm = get_insn_rm(s, rm);
                if (rm < 0)
                    goto illegal_insn;
                write_fp_reg(rd, glue(div_sf, F_SIZE)(unbox(read_fp_reg(rs1)),
                                                      unbox(read_fp_reg(rs2)),
                                                      (RoundingModeEnum)rm, &s->fflags) | F_HIGH);
                s->fs = 3;
                break;
            case (0x0b << 2) | OPID:
                rm = get_insn_rm(s, rm);
                if (rm < 0 || rs2 != 0)
                    goto illegal_insn;
                write_fp_reg(rd, glue(sqrt_sf, F_SIZE)(unbox(read_fp_reg(rs1)),
                                                       (RoundingModeEnum)rm, &s->fflags) | F_HIGH);
                s->fs = 3;
                break;
            case (0x04 << 2) | OPID:
                switch (rm) {
                case 0: /* fsgnj */
                    write_fp_reg(rd,
                                 (unbox(read_fp_reg(rs1)) & ~FSIGN_MASK) |
                                 (unbox(read_fp_reg(rs2)) &  FSIGN_MASK) | F_HIGH);
                    break;
                case 1: /* fsgnjn */
                    write_fp_reg(rd,
                                 (unbox(read_fp_reg(rs1)) & ~FSIGN_MASK) |
                                 ((unbox(read_fp_reg(rs2)) & FSIGN_MASK) ^ FSIGN_MASK) | F_HIGH);
                    break;
                case 2: /* fsgnjx */
                    write_fp_reg(rd,
                                 (unbox(read_fp_reg(rs1)) ^
                                  (unbox(read_fp_reg(rs2)) & FSIGN_MASK)) | F_HIGH);
                    break;
                default:
                    goto illegal_insn;
                }
                s->fs = 3;
                break;
            case (0x05 << 2) | OPID:
                switch (rm) {
                case 0: /* fmin */
                    write_fp_reg(rd, glue(min_sf, F_SIZE)(unbox(read_fp_reg(rs1)),
                                                          unbox(read_fp_reg(rs2)),
                                                          &s->fflags) | F_HIGH);
                    break;
                case 1: /* fmax */
                    write_fp_reg(rd, glue(max_sf, F_SIZE)(unbox(read_fp_reg(rs1)),
                                                          unbox(read_fp_reg(rs2)),
                                                          &s->fflags) | F_HIGH);
                    break;
                default:
                    goto illegal_insn;
                }
                s->fs = 3;
                break;
            case (0x18 << 2) | OPID:
                rm = get_insn_rm(s, rm);
                if (rm < 0)
                    goto illegal_insn;
                switch (rs2) {
                case 0: /* fcvt.w.[sdq] */
                    val = (int32_t)glue(glue(cvt_sf, F_SIZE), _i32)(unbox(read_fp_reg(rs1)), (RoundingModeEnum)rm,
                                                                    &s->fflags);
                    break;
                case 1: /* fcvt.wu.[sdq] */
                    val = (int32_t)glue(glue(cvt_sf, F_SIZE), _u32)(unbox(read_fp_reg(rs1)), (RoundingModeEnum)rm,
                                                                    &s->fflags);
                    break;
#if XLEN >= 64
                case 2: /* fcvt.l.[sdq] */
                    val = (int64_t)glue(glue(cvt_sf, F_SIZE), _i64)(unbox(read_fp_reg(rs1)), (RoundingModeEnum)rm,
                                                                    &s->fflags);
                    break;
                case 3: /* fcvt.lu.[sdq] */
                    val = (int64_t)glue(glue(cvt_sf, F_SIZE), _u64)(unbox(read_fp_reg(rs1)), (RoundingModeEnum)rm,
                                                                    &s->fflags);
                    break;
                default:
                    goto illegal_insn;
                }
                if (rd != 0)
                    write_reg(rd, val);
                break;
            case (0x14 << 2) | OPID:
                switch (rm) {
                case 0: /* fle */
                    val = glue(le_sf, F_SIZE)(unbox(read_fp_reg(rs1)),
                                              unbox(read_fp_reg(rs2)),
                                              &s->fflags);
                    break;
                case 1: /* flt */
                    val = glue(lt_sf, F_SIZE)(unbox(read_fp_reg(rs1)),
                                              unbox(read_fp_reg(rs2)),
                                              &s->fflags);
                    break;
                case 2: /* feq */
                    val = glue(eq_quiet_sf, F_SIZE)(unbox(read_fp_reg(rs1)),
                                                    unbox(read_fp_reg(rs2)),
                                                    &s->fflags);
                    break;
                default:
                    goto illegal_insn;
                }
                if (rd != 0)
                    write_reg(rd, val);
                break;
            case (0x1a << 2) | OPID:
                rm = get_insn_rm(s, rm);
                if (rm < 0)
                    goto illegal_insn;
                switch (rs2) {
                case 0: /* fcvt.[sdq].w */
                    write_fp_reg(rd, glue(cvt_i32_sf, F_SIZE)(read_reg(rs1), (RoundingModeEnum)rm,
                                                              &s->fflags) | F_HIGH);
                    break;
                case 1: /* fcvt.[sdq].wu */
                    write_fp_reg(rd, glue(cvt_u32_sf, F_SIZE)(read_reg(rs1), (RoundingModeEnum)rm,
                                                              &s->fflags) | F_HIGH);
                    break;
                case 2: /* fcvt.[sdq].l */
                    write_fp_reg(rd, glue(cvt_i64_sf, F_SIZE)(read_reg(rs1), (RoundingModeEnum)rm,
                                                              &s->fflags) | F_HIGH);
                    break;
                case 3: /* fcvt.[sdq].lu */
                    write_fp_reg(rd, glue(cvt_u64_sf, F_SIZE)(read_reg(rs1), (RoundingModeEnum)rm,
                                                              &s->fflags) | F_HIGH);
                    break;
#endif
                default:
                    goto illegal_insn;
                }
                s->fs = 3;
                break;

            case (0x08 << 2) | OPID:
                rm = get_insn_rm(s, rm);
                if (rm < 0)
                    goto illegal_insn;
                switch (rs2) {
#if F_SIZE == 32 && FLEN >= 64
                case 1: /* cvt.s.d */
                    write_fp_reg(rd, cvt_sf64_sf32(read_fp_reg(rs1), (RoundingModeEnum)rm, &s->fflags) | F32_HIGH);
                    break;
#if FLEN >= 128
                case 3: /* cvt.s.q */
                    write_fp_reg(rd, cvt_sf128_sf32(read_fp_reg(rs1), (RoundingModeEnum)rm, &s->fflags) | F32_HIGH);
                    break;
#endif
#endif /* F_SIZE == 32 */
#if F_SIZE == 64
                case 0: /* cvt.d.s */
                    {
                        /* Check NaN-boxing of the *explictly* 32-bit float */
                        fp_uint v = read_fp_reg(rs1);
                        if ((v & F32_HIGH) != F32_HIGH)
                            v = f_qnan32;
                        v = cvt_sf32_sf64(v, &s->fflags) | F64_HIGH;
                        write_fp_reg(rd, v);
                    }
                    break;
#if FLEN >= 128
                case 1: /* cvt.d.q */
                    write_fp_reg(rd, cvt_sf128_sf64(read_fp_reg(rs1), (RoundingModeEnum)rm, &s->fflags) | F64_HIGH);
                    break;
#endif
#endif /* F_SIZE == 64 */
#if F_SIZE == 128
                case 0: /* cvt.q.s */
                    write_fp_reg(rd, cvt_sf32_sf128(unbox(read_fp_reg(rs1)), &s->fflags));
                    break;
                case 1: /* cvt.q.d */
                    write_fp_reg(rd, cvt_sf64_sf128(unbox(read_fp_reg(rs1)), &s->fflags));
                    break;
#endif /* F_SIZE == 128 */

                default:
                    goto illegal_insn;
                }
                s->fs = 3;
                break;

            case (0x1c << 2) | OPID:
                if (rs2 != 0)
                    goto illegal_insn;
                switch (rm) {
#if F_SIZE <= XLEN
                case 0: /* fmv.x.w */
#if F_SIZE == 32
                    val = (int32_t)read_fp_reg(rs1);
#elif F_SIZE == 64
                    val = (int64_t)read_fp_reg(rs1);
#else
                    val = (int128_t)read_fp_reg(rs1);
#endif
                    break;
#endif /* F_SIZE <= XLEN */
                case 1: /* fclass */
                    val = glue(fclass_sf, F_SIZE)(unbox(read_fp_reg(rs1)));
                    break;
                default:
                    goto illegal_insn;
                }
                if (rd != 0)
                    write_reg(rd, val);
                break;

#if F_SIZE <= XLEN
            case (0x1e << 2) | OPID: /* fmv.w.x */
                if (rs2 != 0 || rm != 0)
                    goto illegal_insn;
#if F_SIZE == 32
                write_fp_reg(rd, (int32_t)read_reg(rs1) | F_HIGH);
#elif F_SIZE == 64
                write_fp_reg(rd, (int64_t)read_reg(rs1) | F_HIGH);
#else
                write_fp_reg(rd, (int128_t)read_reg(rs1) | F_HIGH);
#endif
                s->fs = 3;
                break;
#endif /* F_SIZE <= XLEN */

#undef F_SIZE
#undef F_HIGH
#undef OPID
#undef FSIGN_MASK

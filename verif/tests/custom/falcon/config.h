/*
 * Manual configuration file for the Falcon implementation. Here can
 * be set some compilation-time options.
 *
 * ==========================(LICENSE BEGIN)============================
 *
 * Copyright (c) 2017-2019  Falcon Project
 *
 * Permission is hereby granted, free of charge, to any person obtaining
 * a copy of this software and associated documentation files (the
 * "Software"), to deal in the Software without restriction, including
 * without limitation the rights to use, copy, modify, merge, publish,
 * distribute, sublicense, and/or sell copies of the Software, and to
 * permit persons to whom the Software is furnished to do so, subject to
 * the following conditions:
 *
 * The above copyright notice and this permission notice shall be
 * included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
 * EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.
 * IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY
 * CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT,
 * TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE
 * SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 *
 * ===========================(LICENSE END)=============================
 *
 * @author   Thomas Pornin <thomas.pornin@nccgroup.com>
 */

#ifndef FALCON_CONFIG_H__
#define FALCON_CONFIG_H__

#define FALCON_FPNATIVE 0
#define FALCON_FPEMU 1

/*
 * Each option is a macro which should be defined to either 1 or 0.
 * If any of the options below is left undefined, then a default value
 * will be used by the code, possibly using compile-time autodetection
 * from compiler-defined macros.
 *
 * Explicitly setting a parameter can be done by uncommenting/modifying
 * its definition below, in this file, or equivalently by setting it as
 * a compiler flag.
 */

/*
 * Use the native 'double' C type for floating-point computations. Exact
 * reproducibility of all tests requires that type to faithfully follow
 * IEEE-754 "round-to-nearest" rules.
 *
 * Native double support will use the CPU hardware and/or
 * compiler-provided functions; the latter is typically NOT
 * constant-time, while the former MAY be constant-time, or not. On
 * recent x86 CPU in 64-bit mode, SSE2 opcodes are used and they provide
 * constant-time operations for all the operations used in Falcon,
 * except for some special cases of divisions and square roots, but it
 * can be shown that theses cases imply only negligible leak of
 * information that cannot be leveraged into a full attack.
 *
 * If neither FALCON_FPNATIVE nor FALCON_FPEMU is defined, then use of
 * the native 'double' C type is the default behaviour unless
 * FALCON_ASM_CORTEXM4 is defined to 1, in which case the emulated code
 * will be used.
 *
#define FALCON_FPNATIVE   1
 */

/*
 * Use emulated floating-point implementation.
 *
 * Emulation uses only integer operations with uint32_t and uint64_t
 * types. This is constant-time, provided that the underlying platform
 * offers constant-time opcodes for the following operations:
 *
 *  - Multiplication of two 32-bit unsigned integers into a 64-bit result.
 *  - Left-shift or right-shift of a 32-bit unsigned integer by a
 *    potentially secret shift count in the 0..31 range.
 *
 * Notably, the ARM Cortex M3 does not fulfill the first condition,
 * while the Pentium IV does not fulfill the second.
 *
 * If neither FALCON_FPNATIVE nor FALCON_FPEMU is defined, then use of
 * the native 'double' C type is the default behaviour unless
 * FALCON_ASM_CORTEXM4 is defined to 1, in which case the emulated code
 * will be used.
 *
#define FALCON_FPEMU   1
 */

/*
 * Enable use of assembly for ARM Cortex-M4 CPU. By default, such
 * support will be used based on some autodection on the compiler
 * version and target architecture. Define this variable to 1 to force
 * use of the assembly code, or 0 to disable it regardless of the
 * autodetection.
 *
 * When FALCON_ASM_CORTEXM4 is enabled (whether defined explicitly or
 * autodetected), emulated floating-point code will be used, unless
 * FALCON_FPNATIVE or FALCON_FPEMU is explicitly set to override the
 * choice. Emulated code with ARM assembly is constant-time and provides
 * better performance than emulated code with plain C.
 *
 * The assembly code for the M4 can also work on a Cortex-M3. If the
 * compiler is instructed to target the M3 (e.g. '-mcpu=cortex-m3' with
 * GCC) then FALCON_ASM_CORTEXM4 won't be autodetected, but it can be
 * enabled explicitly. Take care, though, that the M3 multiplication
 * opcode (multiplication of two 32-bit unsigned integers with a 64-bit
 * result) is NOT constant-time.
 *
#define FALCON_ASM_CORTEXM4   1
 */

/*
 * Enable use of AVX2 intrinsics. If enabled, then the code will compile
 * only when targeting x86 with a compiler that supports AVX2 intrinsics
 * (tested with GCC 7.4.0, Clang 6.0.0, and MSVC 2015, both in 32-bit
 * and 64-bit modes), and run only on systems that offer the AVX2
 * opcodes. Some operations leverage AVX2 for better performance.
 *
#define FALCON_AVX2   1
 */

/*
 * Enable use of FMA intrinsics. This setting has any effect only if
 * FALCON_AVX2 is also enabled. The FMA intrinsics are normally available
 * on any x86 CPU that also has AVX2. Note that setting this option will
 * slightly modify the values of expanded private keys, but will normally
 * not change the values of non-expanded private keys, public keys or
 * signatures, for a given keygen/sign seed (non-expanded private keys
 * and signatures might theoretically change, but only with low probability,
 * less than 2^(-40); produced signatures are still safe and interoperable).
 *
#define FALCON_FMA   1
 */

/*
 * Assert that the platform uses little-endian encoding. If enabled,
 * then encoding and decoding of aligned multibyte values will be
 * slightly faster (especially for hashing and random number
 * generation). If not defined explicitly, then autodetection is
 * applied.
 *
#define FALCON_LE   1
 */

/*
 * Assert that the platform tolerates accesses to unaligned multibyte
 * values. If enabled, then some operations are slightly faster. Note
 * that ARM Cortex M4 do _not_ fully tolerate unaligned accesses; for
 * such systems, this option should not be enabled. If not defined
 * explicitly, then autodetection is applied.
 *
#define FALCON_UNALIGNED   1
 */

/*
 * Use a PRNG based on ChaCha20 and seeded with SHAKE256, instead of
 * SHAKE256 directly, for key pair generation purposes. This speeds up
 * key pair generation, especially on platforms where SHAKE256 is
 * comparatively slow: on the ARM Cortex M4, average key generation time
 * is reduced by 19% with this setting; on a recent x86 Skylake, the
 * reduction is smaller (less than 8%).
 *
 * However, this setting changes the private/public key pair obtained
 * from a given seed, thus preventing reproducibility of the
 * known-answer tests vectors. For compatibility with existing KAT
 * vectors (e.g. in PQClean, pqm4 and NIST implementations), this
 * setting is not enabled by default.
 *
#define FALCON_KG_CHACHA20   1
 */

/*
 * Use an explicit OS-provided source of randomness for seeding (for the
 * Zf(get_seed)() function implementation). Three possible sources are
 * defined:
 *
 *  - getentropy() system call
 *  - /dev/urandom special file
 *  - CryptGenRandom() function call
 *
 * More than one source may be enabled, in which case they will be tried
 * in the order above, until a success is reached.
 *
 * By default, sources are enabled at compile-time based on these
 * conditions:
 *
 *  - getentropy(): target is one of: Linux with Glibc-2.25+, FreeBSD 12+,
 *    or OpenBSD.
 *  - /dev/urandom: target is a Unix-like system (including Linux,
 *    FreeBSD, NetBSD, OpenBSD, DragonFly, macOS, Android, Solaris, AIX).
 *  - CryptGenRandom(): target is Windows (Win32 or Win64).
 *
 * On most small embedded systems, none will be enabled and Zf(get_seed)()
 * will always return 0. Applications will need to provide their own seeds.
 *
#define FALCON_RAND_GETENTROPY   1
#define FALCON_RAND_URANDOM      1
#define FALCON_RAND_WIN32        1
 */

#endif

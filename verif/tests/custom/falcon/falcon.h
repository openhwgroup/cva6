/*
 * External Falcon API.
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

#ifndef FALCON_H__
#define FALCON_H__

#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

/* ==================================================================== */
/*
 * Falcon API Notes
 * ----------------
 *
 *
 * FALCON DEGREE
 *
 * Falcon is parameterized by a degree, which is a power of two. Formally,
 * two values are possible: 512 and 1024 (for Falcon-512 and Falcon-1024,
 * respectively). This implementation also supports lower degrees, from
 * 2 to 256; these reduced variants do not provide adequate security and
 * should be used for research purposes only.
 *
 * In all functions and macros defined below, the degree is provided
 * logarithmically as the 'logn' parameter: logn ranges from 1 to 10,
 * and represents the degree 2^logn.
 *
 *
 * ERROR REPORTING
 *
 * All functions that may fail for some reason return an 'int' value. A
 * returned value of zero is a success; all error conditions are
 * reported as an error code. Error codes are negative. Macros are
 * defined for some error codes; in the interest of forward
 * compatiblity, applications that use this implementation should be
 * prepared to receive other error codes not listed in the macros below.
 *
 *
 * TEMPORARY BUFFERS
 *
 * Many functions expect temporary areas, provided as the parameter
 * 'tmp'. The caller is responsible for allocating these areas with the
 * proper size; the FALCON_TMPSIZE_* macros evaluate to constant
 * expressions that yield the proper size (in bytes) and can be used to
 * allocate the temporaries on the stack or elsewhere. There are no
 * alignment requirements on temporaries (the functions handle alignment
 * internally).
 *
 * The caller is responsible for clearing temporary buffer contents,
 * if such memory scrubbing is deemed relevant in the context where this
 * implementation is used.
 *
 * The same temporary buffer can be reused for several operations,
 * possibly distinct from each other. For all degrees from 8 to 1024
 * (logn = 3 to 10), the following sizes are in ascending order:
 *
 *    FALCON_TMPSIZE_MAKEPUB
 *    FALCON_TMPSIZE_VERIFY
 *    FALCON_TMPSIZE_KEYGEN
 *    FALCON_TMPSIZE_SIGNTREE
 *    FALCON_TMPSIZE_EXPANDPRIV
 *    FALCON_TMPSIZE_SIGNDYN
 *
 * i.e. a temporary buffer large enough for computing signatures with
 * an expanded key ("SIGNTREE") will also be large enough for a
 * key pair generation ("KEYGEN"). For logn = 1 or 2, the same order
 * holds, except that the KEYGEN buffer is larger.
 *
 * Here are the actual values for the temporary buffer sizes (in bytes):
 *
 * degree  mkpub  verify  keygen  signtree  expkey  signdyn
 *     2      13      17     285       107     111      163
 *     4      25      33     291       207     215      319
 *     8      49      65     303       407     423      631
 *    16      97     129     503       807     839     1255
 *    32     193     257     999      1607    1671     2503
 *    64     385     513    1991      3207    3335     4999
 *   128     769    1025    3975      6407    6663     9991
 *   256    1537    2049    7943     12807   13319    19975
 *   512    3073    4097   15879     25607   26631    39943
 *  1024    6145    8193   31751     51207   53255    79879
 *
 * Take care that the "expkey" column here qualifies the temporary buffer
 * for the key expansion process, but NOT the expanded key itself (which
 * has size FALCON_EXPANDEDKEY_SIZE(logn) and is larger than that).
 *
 *
 * FORMATS
 *
 * Public and private keys are exchanged as serialized sequences of
 * bytes. Their respective sizes are fixed (for a given degree) and the
 * FALCON_PRIVKEY_SIZE and FALCON_PUBKEY_SIZE macros return that value
 * as constant expressions.
 *
 * There are three formats for signatures:
 *
 *   - COMPRESSED: this is the default format, which yields the shortest
 *     signatures on average. However, the size is variable (see below)
 *     though within a limited range.
 *
 *   - PADDED: this is the compressed format, but with extra padding bytes
 *     to obtain a fixed size known at compile-time. The size depends only
 *     on the degree; the FALCON_SIG_PADDED_SIZE macro computes it. The
 *     signature process enforces that size by restarting the process
 *     until an appropriate size is obtained (such restarts are uncommon
 *     enough that the computational overhead is negligible).
 *
 *   - CT: this is a fixed-size format, which furthermore allows
 *     constant-time processing with regard to the signature value and
 *     message data. This is meant for uncommon situations in which
 *     the signed data is secret but of low entropy, and the public key
 *     is not actually public. The CT format is larger than the
 *     COMPRESSED and PADDED formats.
 *
 * The signature format is selected by the 'sig_type' parameter to
 * the signature generation and verification functions.
 *
 * Actual signature size has been measured over 10000 signatures for each
 * degree (100 random keys, 100 signatures per key):
 *
 * degree     ct   padded  compressed (with std. dev)  comp_max
 *     2      44      44       44.00 (+/- 0.00)            44
 *     4      47      47       46.03 (+/- 0.17)            47
 *     8      52      52       50.97 (+/- 0.26)            52
 *    16      65      63       60.45 (+/- 0.52)            64
 *    32      89      82       79.53 (+/- 0.68)            86
 *    64     137     122      117.69 (+/- 0.94)           130
 *   128     233     200      193.96 (+/- 1.30)           219
 *   256     425     356      346.53 (+/- 1.84)           397
 *   512     809     666      651.59 (+/- 2.55)           752
 *  1024    1577    1280     1261.06 (+/- 3.57)          1462
 *
 * with:
 *   degree = Falcon degree = 2^logn
 *   ct = FALCON_SIG_CT_SIZE(logn)  (size of a CT signature)
 *   padded = FALCON_SIG_PADDED_SIZE(logn)  (size of a PADDED signature)
 *   compressed = measured average length of a COMPRESSED signature
 *   v_max = FALCON_SIG_COMPRESSED_MAXSIZE(logn)  (maximum theoretical
 *           size of a COMPRESSED signature)
 * All lengths are in bytes.
 *
 * A private key, in its encoded format, can be used as parameter to
 * falcon_sign_dyn(). An "expanded private key" is computed with
 * falcon_expand_privkey(), to be used with falcon_sign_tree(). The
 * expanded private key is much larger than the encoded private key, and
 * its format is not portable. Its size (in bytes) is provided by
 * FALCON_EXPANDEDKEY_SIZE. There are no specific alignment requirements
 * on expanded keys, except that the alignment of a given expanded key
 * must not change (i.e. if an expanded key is moved from address addr1
 * to address addr2, then it must hold that addr1 = addr2 mod 8).
 * Expanded private keys are meant to be used when several signatures are
 * to be computed with the same private key: amortized cost per signature
 * is about halved when using expanded private keys (for short messages,
 * and depending on underlying architecture and implementation choices).
 *
 *
 * USE OF SHAKE256
 *
 * SHAKE256 is used in two places:
 *
 *  - As a PRNG: all functions that require randomness (key pair
 *    generation, signature generation) receive as parameter a SHAKE256
 *    object, in output mode, from which pseudorandom data is obtained.
 *
 *    A SHAKE256 instance, to be used as a RNG, can be initialized
 *    from an explicit 48-byte seed, or from an OS-provided RNG. Using
 *    an explicit seed is meant for reproducibility of test vectors,
 *    or to be used in cases where no OS-provided RNG is available and
 *    supported.
 *
 *  - As the hashing mechanism for the message which should be signed.
 *    The streamed signature API exposes that SHAKE256 object, since
 *    the caller then performs the hashing externally.
 */

/* ==================================================================== */
/*
 * Error codes.
 *
 * Most functions in this API that may fail for some reason return an
 * 'int' value which will be 0 on success, or a negative error code.
 * The macros below define the error codes. In the interest of forward
 * compatibility, callers should be prepared to receive additional error
 * codes not included in the list below.
 */

/*
 * FALCON_ERR_RANDOM is returned when the library tries to use an
 * OS-provided RNG, but either none is supported, or that RNG fails.
 */
#define FALCON_ERR_RANDOM     -1

/*
 * FALCON_ERR_SIZE is returned when a buffer has been provided to
 * the library but is too small to receive the intended value.
 */
#define FALCON_ERR_SIZE       -2

/*
 * FALCON_ERR_FORMAT is returned when decoding of an external object
 * (public key, private key, signature) fails.
 */
#define FALCON_ERR_FORMAT     -3

/*
 * FALCON_ERR_BADSIG is returned when verifying a signature, the signature
 * is validly encoded, but its value does not match the provided message
 * and public key.
 */
#define FALCON_ERR_BADSIG     -4

/*
 * FALCON_ERR_BADARG is returned when a provided parameter is not in
 * a valid range.
 */
#define FALCON_ERR_BADARG     -5

/*
 * FALCON_ERR_INTERNAL is returned when some internal computation failed.
 */
#define FALCON_ERR_INTERNAL   -6

/* ==================================================================== */
/*
 * Signature formats.
 */

/*
 * Variable-size signature. This format produces the most compact
 * signatures on average, but the signature size may vary depending
 * on private key, signed data, and random seed.
 */
#define FALCON_SIG_COMPRESSED   1

/*
 * Fixed-size signature. This format produces is equivalent to the
 * "compressed" format, but includes padding to a known fixed size
 * (specified by FALCON_SIG_PADDED_SIZE). With this format, the
 * signature generation loops until an appropriate signature size is
 * achieved (such looping is uncommon) and adds the padding bytes;
 * the verification functions check the presence and contents of the
 * padding bytes.
 */
#define FALCON_SIG_PADDED       2

/*
 * Fixed-size format amenable to constant-time implementation. All formats
 * allow constant-time code with regard to the private key; the 'CT'
 * format of signature also prevents information about the signature value
 * and the signed data hash to leak through timing-based side channels
 * (this feature is rarely needed).
 */
#define FALCON_SIG_CT           3

/* ==================================================================== */
/*
 * Sizes.
 *
 * The sizes are expressed in bytes. Each size depends on the Falcon
 * degree, which is provided logarithmically: use logn=9 for Falcon-512,
 * logn=10 for Falcon-1024. Valid values for logn range from 1 to 10
 * (values 1 to 8 correspond to reduced variants of Falcon that do not
 * provided adequate security and are meant for research purposes only).
 *
 * The sizes are provided as macros that evaluate to constant
 * expressions, as long as the 'logn' parameter is itself a constant
 * expression. Moreover, all sizes are monotonic (for each size category,
 * increasing logn cannot result in a shorter length).
 *
 * Note: each macro may evaluate its argument 'logn' several times.
 */

/*
 * Private key size (in bytes). The size is exact.
 */
#define FALCON_PRIVKEY_SIZE(logn) \
	(((logn) <= 3 \
		? (3u << (logn)) \
		: ((10u - ((logn) >> 1)) << ((logn) - 2)) + (1 << (logn))) \
	+ 1)

/*
 * Public key size (in bytes). The size is exact.
 */
#define FALCON_PUBKEY_SIZE(logn) \
	(((logn) <= 1 \
		? 4u \
		: (7u << ((logn) - 2))) \
	+ 1)

/*
 * Maximum signature size (in bytes) when using the COMPRESSED format.
 * In practice, the signature will be shorter.
 */
#define FALCON_SIG_COMPRESSED_MAXSIZE(logn) \
	(((((11u << (logn)) + (101u >> (10 - (logn)))) \
	+ 7) >> 3) + 41)

/*
 * Signature size (in bytes) when using the PADDED format. The size
 * is exact.
 */
#define FALCON_SIG_PADDED_SIZE(logn) \
	(44u + 3 * (256u >> (10 - (logn))) + 2 * (128u >> (10 - (logn))) \
	+ 3 * (64u >> (10 - (logn))) + 2 * (16u >> (10 - (logn))) \
	- 2 * (2u >> (10 - (logn))) - 8 * (1u >> (10 - (logn))))

/*
 * Signature size (in bytes) when using the CT format. The size is exact.
 */
#define FALCON_SIG_CT_SIZE(logn) \
	((3u << ((logn) - 1)) - ((logn) == 3) + 41)

/*
 * Temporary buffer size for key pair generation.
 */
#define FALCON_TMPSIZE_KEYGEN(logn) \
	(((logn) <= 3 ? 272u : (28u << (logn))) + (3u << (logn)) + 7)

/*
 * Temporary buffer size for computing the pubic key from the private key.
 */
#define FALCON_TMPSIZE_MAKEPUB(logn) \
	((6u << (logn)) + 1)

/*
 * Temporary buffer size for generating a signature ("dynamic" variant).
 */
#define FALCON_TMPSIZE_SIGNDYN(logn) \
	((78u << (logn)) + 7)

/*
 * Temporary buffer size for generating a signature ("tree" variant, with
 * an expanded key).
 */
#define FALCON_TMPSIZE_SIGNTREE(logn) \
	((50u << (logn)) + 7)

/*
 * Temporary buffer size for expanding a private key.
 */
#define FALCON_TMPSIZE_EXPANDPRIV(logn) \
	((52u << (logn)) + 7)

/*
 * Size of an expanded private key.
 */
#define FALCON_EXPANDEDKEY_SIZE(logn) \
	(((8u * (logn) + 40) << (logn)) + 8)

/*
 * Temporary buffer size for verifying a signature.
 */
#define FALCON_TMPSIZE_VERIFY(logn) \
	((8u << (logn)) + 1)

/* ==================================================================== */
/*
 * SHAKE256.
 */

/*
 * Context for a SHAKE256 computation. Contents are opaque.
 * Contents are pure data with no pointer; they need not be released
 * explicitly and don't reference any other allocated resource. The
 * caller is responsible for allocating the context structure itself,
 * typically on the stack.
 */
typedef struct {
	uint64_t opaque_contents[26];
} shake256_context;

/*
 * Initialize a SHAKE256 context to its initial state. The state is
 * then ready to receive data (with shake256_inject()).
 */
void shake256_init(shake256_context *sc);

/*
 * Inject some data bytes into the SHAKE256 context ("absorb" operation).
 * This function can be called several times, to inject several chunks
 * of data of arbitrary length.
 */
void shake256_inject(shake256_context *sc, const void *data, size_t len);

/*
 * Flip the SHAKE256 state to output mode. After this call, shake256_inject()
 * can no longer be called on the context, but shake256_extract() can be
 * called.
 *
 * Flipping is one-way; a given context can be converted back to input
 * mode only by initializing it again, which forgets all previously
 * injected data.
 */
void shake256_flip(shake256_context *sc);

/*
 * Extract bytes from the SHAKE256 context ("squeeze" operation). The
 * context must have been flipped to output mode (with shake256_flip()).
 * Arbitrary amounts of data can be extracted, in one or several calls
 * to this function.
 */
void shake256_extract(shake256_context *sc, void *out, size_t len);

/*
 * Initialize a SHAKE256 context as a PRNG from the provided seed.
 * This initializes the context, injects the seed, then flips the context
 * to output mode to make it ready to produce bytes.
 */
void shake256_init_prng_from_seed(shake256_context *sc,
	const void *seed, size_t seed_len);

/*
 * Initialize a SHAKE256 context as a PRNG, using an initial seed from
 * the OS-provided RNG. If there is no known/supported OS-provided RNG,
 * or if that RNG fails, then the context is not properly initialized
 * and FALCON_ERR_RANDOM is returned.
 *
 * Returned value: 0 on success, or a negative error code.
 */
int shake256_init_prng_from_system(shake256_context *sc);

/* ==================================================================== */
/*
 * Key pair generation.
 */

/*
 * Generate a new keypair.
 *
 * The logarithm of the Falcon degree (logn) must be in the 1 to 10
 * range; values 1 to 8 correspond to reduced versions of Falcon that do
 * not provide adequate security and are meant for research purposes
 * only.
 *
 * The source of randomness is the provided SHAKE256 context *rng, which
 * must have been already initialized, seeded, and set to output mode (see
 * shake256_init_prng_from_seed() and shake256_init_prng_from_system()).
 *
 * The new private key is written in the buffer pointed to by privkey.
 * The size of that buffer must be specified in privkey_len; if that
 * size is too low, then this function fails with FALCON_ERR_SIZE. The
 * actual private key length can be obtained from the FALCON_PRIVKEY_SIZE()
 * macro.
 *
 * If pubkey is not NULL, then the new public key is written in the buffer
 * pointed to by pubkey. The size of that buffer must be specified in
 * pubkey_len; if that size is too low, then this function fails with
 * FALCON_ERR_SIZE. The actual public key length can be obtained from the
 * FALCON_PUBKEY_SIZE() macro.
 *
 * If pubkey is NULL then pubkey_len is ignored; the private key will
 * still be generated and written to privkey[], but the public key
 * won't be written anywhere. The public key can be later on recomputed
 * from the private key with falcon_make_public().
 *
 * The tmp[] buffer is used to hold temporary values. Its size tmp_len
 * MUST be at least FALCON_TMPSIZE_KEYGEN(logn) bytes.
 *
 * Returned value: 0 on success, or a negative error code.
 */
int falcon_keygen_make(
	shake256_context *rng,
	unsigned logn,
	void *privkey, size_t privkey_len,
	void *pubkey, size_t pubkey_len,
	void *tmp, size_t tmp_len);

/*
 * Recompute the public key from the private key.
 *
 * The private key is provided encoded. This function decodes the
 * private key and verifies that its length (in bytes) is exactly
 * the provided value privkey_len (trailing extra bytes are not
 * tolerated).
 *
 * The public key is written in the buffer pointed to by pubkey. The
 * size (in bytes) of the pubkey buffer must be provided in pubkey_len;
 * if it is too short for the public key, then FALCON_ERR_SIZE is
 * returned. The actual public key size can be obtained from the
 * FALCON_PUBKEY_SIZE() macro.
 *
 * The tmp[] buffer is used to hold temporary values. Its size tmp_len
 * MUST be at least FALCON_TMPSIZE_MAKEPUB(logn) bytes.
 *
 * Returned value: 0 on success, or a negative error code.
 */
int falcon_make_public(
	void *pubkey, size_t pubkey_len,
	const void *privkey, size_t privkey_len,
	void *tmp, size_t tmp_len);

/*
 * Get the Falcon degree from an encoded private key, public key or
 * signature. Returned value is the logarithm of the degree (1 to 10),
 * or a negative error code.
 */
int falcon_get_logn(void *obj, size_t len);

/* ==================================================================== */
/*
 * Signature generation.
 */

/*
 * Sign the data provided in buffer data[] (of length data_len bytes),
 * using the private key held in privkey[] (of length privkey_len bytes).
 *
 * The source of randomness is the provided SHAKE256 context *rng, which
 * must have been already initialized, seeded, and set to output mode (see
 * shake256_init_prng_from_seed() and shake256_init_prng_from_system()).
 *
 * The signature is written in sig[]. The caller must set *sig_len to
 * the maximum size of sig[]; if the signature computation is
 * successful, then *sig_len will be set to the actual length of the
 * signature. The signature length depends on the signature type,
 * which is specified with the sig_type parameter to one of the three
 * defined values FALCON_SIG_COMPRESSED, FALCON_SIG_PADDED or
 * FALCON_SIG_CT; for the last two of these, the signature length is
 * fixed (for a given Falcon degree).
 *
 * Regardless of the signature type, the process is constant-time with
 * regard to the private key. When sig_type is FALCON_SIG_CT, it is also
 * constant-time with regard to the signature value and the message data,
 * i.e. no information on the signature and the message may be inferred
 * from timing-related side channels.
 *
 * The tmp[] buffer is used to hold temporary values. Its size tmp_len
 * MUST be at least FALCON_TMPSIZE_SIGNDYN(logn) bytes.
 *
 * Returned value: 0 on success, or a negative error code.
 */
int falcon_sign_dyn(shake256_context *rng,
	void *sig, size_t *sig_len, int sig_type,
	const void *privkey, size_t privkey_len,
	const void *data, size_t data_len,
	void *tmp, size_t tmp_len);

/*
 * Expand a private key. The provided Falcon private key (privkey, of
 * size privkey_len bytes) is decoded and expanded into expanded_key[].
 *
 * The expanded_key[] buffer has size expanded_key_len, which MUST be at
 * least FALCON_EXPANDEDKEY_SIZE(logn) bytes (where 'logn' qualifies the
 * Falcon degree encoded in the private key and can be obtained with
 * falcon_get_logn()). Expanded key contents have an internal,
 * implementation-specific format. Expanded keys may be moved in RAM
 * only if their 8-byte alignment remains unchanged.
 *
 * The tmp[] buffer is used to hold temporary values. Its size tmp_len
 * MUST be at least FALCON_TMPSIZE_EXPANDPRIV(logn) bytes.
 *
 * Returned value: 0 on success, or a negative error code.
 */
int falcon_expand_privkey(void *expanded_key, size_t expanded_key_len,
	const void *privkey, size_t privkey_len,
	void *tmp, size_t tmp_len);

/*
 * Sign the data provided in buffer data[] (of length data_len bytes),
 * using the expanded private key held in expanded_key[], as generated
 * by falcon_expand_privkey().
 *
 * The source of randomness is the provided SHAKE256 context *rng, which
 * must have been already initialized, seeded, and set to output mode (see
 * shake256_init_prng_from_seed() and shake256_init_prng_from_system()).
 *
 * The signature is written in sig[]. The caller must set *sig_len to
 * the maximum size of sig[]; if the signature computation is
 * successful, then *sig_len will be set to the actual length of the
 * signature. The signature length depends on the signature type,
 * which is specified with the sig_type parameter to one of the three
 * defined values FALCON_SIG_COMPRESSED, FALCON_SIG_PADDED or
 * FALCON_SIG_CT; for the last two of these, the signature length is
 * fixed (for a given Falcon degree).
 *
 * Regardless of the signature type, the process is constant-time with
 * regard to the private key. When sig_type is FALCON_SIG_CT, it is also
 * constant-time with regard to the signature value and the message data,
 * i.e. no information on the signature and the message may be inferred
 * from timing-related side channels.
 *
 * The tmp[] buffer is used to hold temporary values. Its size tmp_len
 * MUST be at least FALCON_TMPSIZE_SIGNTREE(logn) bytes.
 *
 * Returned value: 0 on success, or a negative error code.
 */
int falcon_sign_tree(shake256_context *rng,
	void *sig, size_t *sig_len, int sig_type,
	const void *expanded_key,
	const void *data, size_t data_len,
	void *tmp, size_t tmp_len);

/* ==================================================================== */
/*
 * Signature generation, streamed API.
 *
 * In the streamed API, the caller performs the data hashing externally.
 * An initialization function (falcon_sign_start()) is first called; it
 * generates and returns a random 40-byte nonce value; it also initializes
 * a SHAKE256 context and injects the nonce value in that context. The
 * caller must then inject the data to sign in the SHAKE256 context, and
 * finally call falcon_sign_dyn_finish() or falcon_sign_tree_finish() to
 * finalize the signature generation.
 */

/*
 * Start a signature generation context.
 *
 * A 40-byte nonce is generated and written in nonce[]. The *hash_data
 * context is also initialized, and the nonce is injected in that context.
 *
 * The source of randomness is the provided SHAKE256 context *rng, which
 * must have been already initialized, seeded, and set to output mode (see
 * shake256_init_prng_from_seed() and shake256_init_prng_from_system()).
 *
 * Returned value: 0 on success, or a negative error code.
 */
int falcon_sign_start(shake256_context *rng,
	void *nonce,
	shake256_context *hash_data);

/*
 * Finish a signature generation operation, using the private key held
 * in privkey[] (of length privkey_len bytes). The hashed nonce + message
 * is provided as the SHAKE256 context *hash_data, which must still be
 * in input mode (i.e. not yet flipped to output mode). That context is
 * modified in the process.
 *
 * The nonce value (which was used at the start of the hashing process,
 * usually as part of a falcon_sign_start() call) must be provided again,
 * because it is encoded into the signature. The nonce length is 40 bytes.
 *
 * The source of randomness is the provided SHAKE256 context *rng, which
 * must have been already initialized, seeded, and set to output mode (see
 * shake256_init_prng_from_seed() and shake256_init_prng_from_system()).
 *
 * The signature is written in sig[]. The caller must set *sig_len to
 * the maximum size of sig[]; if the signature computation is
 * successful, then *sig_len will be set to the actual length of the
 * signature. The signature length depends on the signature type,
 * which is specified with the sig_type parameter to one of the three
 * defined values FALCON_SIG_COMPRESSED, FALCON_SIG_PADDED or
 * FALCON_SIG_CT; for the last two of these, the signature length is
 * fixed (for a given Falcon degree).
 *
 * Regardless of the signature type, the process is constant-time with
 * regard to the private key. When sig_type is FALCON_SIG_CT, it is also
 * constant-time with regard to the signature value and the message data,
 * i.e. no information on the signature and the message may be inferred
 * from timing-related side channels.
 *
 * The tmp[] buffer is used to hold temporary values. Its size tmp_len
 * MUST be at least FALCON_TMPSIZE_SIGNDYN(logn) bytes.
 *
 * Returned value: 0 on success, or a negative error code.
 */
int falcon_sign_dyn_finish(shake256_context *rng,
	void *sig, size_t *sig_len, int sig_type,
	const void *privkey, size_t privkey_len,
	shake256_context *hash_data, const void *nonce,
	void *tmp, size_t tmp_len);

/*
 * Finish a signature generation operation, using the expanded private
 * key held in expanded_key[] (as obtained from
 * falcon_expand_privkey()). The hashed nonce + message is provided as
 * the SHAKE256 context *hash_data, which must still be in input mode
 * (i.e. not yet flipped to output mode). That context is modified in
 * the process.
 *
 * The nonce value (which was used at the start of the hashing process,
 * usually as part of a falcon_sign_start() call) must be provided again,
 * because it is encoded into the signature. The nonce length is 40 bytes.
 *
 * The source of randomness is the provided SHAKE256 context *rng, which
 * must have been already initialized, seeded, and set to output mode (see
 * shake256_init_prng_from_seed() and shake256_init_prng_from_system()).
 *
 * The signature is written in sig[]. The caller must set *sig_len to
 * the maximum size of sig[]; if the signature computation is
 * successful, then *sig_len will be set to the actual length of the
 * signature. The signature length depends on the signature type,
 * which is specified with the sig_type parameter to one of the three
 * defined values FALCON_SIG_COMPRESSED, FALCON_SIG_PADDED or
 * FALCON_SIG_CT; for the last two of these, the signature length is
 * fixed (for a given Falcon degree).
 *
 * Regardless of the signature type, the process is constant-time with
 * regard to the private key. When sig_type is FALCON_SIG_CT, it is also
 * constant-time with regard to the signature value and the message data,
 * i.e. no information on the signature and the message may be inferred
 * from timing-related side channels.
 *
 * The tmp[] buffer is used to hold temporary values. Its size tmp_len
 * MUST be at least FALCON_TMPSIZE_SIGNTREE(logn) bytes.
 *
 * Returned value: 0 on success, or a negative error code.
 */
int falcon_sign_tree_finish(shake256_context *rng,
	void *sig, size_t *sig_len, int sig_type,
	const void *expanded_key,
	shake256_context *hash_data, const void *nonce,
	void *tmp, size_t tmp_len);

/* ==================================================================== */
/*
 * Signature verification.
 */

/*
 * Verify the signature sig[] (of length sig_len bytes) with regards to
 * the provided public key pubkey[] (of length pubkey_len bytes) and the
 * message data[] (of length data_len bytes).
 *
 * The sig_type parameter must be zero, or one of FALCON_SIG_COMPRESSED,
 * FALCON_SIG_PADDED or FALCON_SIG_CT. The function verifies that
 * the provided signature has the correct format. If sig_type is zero,
 * then the signature format is inferred from the signature header byte;
 * note that in that case, the signature is malleable (since a signature
 * value can be transcoded to other formats).
 *
 * The tmp[] buffer is used to hold temporary values. Its size tmp_len
 * MUST be at least FALCON_TMPSIZE_VERIFY(logn) bytes.
 *
 * Returned value: 0 on success, or a negative error code.
 */
int falcon_verify(const void *sig, size_t sig_len, int sig_type,
	const void *pubkey, size_t pubkey_len,
	const void *data, size_t data_len,
	void *tmp, size_t tmp_len);

/*
 * Start a streamed signature verification. The provided SHAKE256 context
 * *hash_data is initialized, and the nonce value (extracted from the
 * signature) is injected into it. The caller shall then inject the
 * message data into the SHAKE256 context, and finally call
 * falcon_verify_finish().
 *
 * Returned value: 0 on success, or a negative error code.
 */
int falcon_verify_start(shake256_context *hash_data,
	const void *sig, size_t sig_len);

/*
 * Finish a streamed signature verification. The signature sig[] (of
 * length sig_len bytes) is verified against the provided public key
 * pubkey[] (of length pubkey_len bytes) and the hashed message. The
 * hashed message is provided as a SHAKE256 context *hash_data;
 * that context must have received the nonce and the message itself
 * (usually, the context is initialized and the nonce injected as
 * part of a falcon_verify_start() call), and still be in input
 * mode (not yet flipped to output mode). *hash_data is modified by
 * the verification process.
 *
 * The sig_type parameter must be zero, or one of FALCON_SIG_COMPRESSED,
 * FALCON_SIG_PADDED or FALCON_SIG_CT. The function verifies that
 * the provided signature has the correct format. If sig_type is zero,
 * then the signature format is inferred from the signature header byte;
 * note that in that case, the signature is malleable (since a signature
 * value can be transcoded to other formats).
 *
 * The tmp[] buffer is used to hold temporary values. Its size tmp_len
 * MUST be at least FALCON_TMPSIZE_VERIFY(logn) bytes.
 *
 * Returned value: 0 on success, or a negative error code.
 */
int falcon_verify_finish(const void *sig, size_t sig_len, int sig_type,
	const void *pubkey, size_t pubkey_len,
	shake256_context *hash_data,
	void *tmp, size_t tmp_len);

/* ==================================================================== */

#ifdef __cplusplus
}
#endif

#endif

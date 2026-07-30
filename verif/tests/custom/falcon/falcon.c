/*
 * Implementation of the external Falcon API.
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

#include "falcon.h"
#include "inner.h"

/* see falcon.h */
void
shake256_init(shake256_context *sc)
{
	inner_shake256_init((inner_shake256_context *)sc);
}

/* see falcon.h */
void
shake256_inject(shake256_context *sc, const void *data, size_t len)
{
	inner_shake256_inject((inner_shake256_context *)sc, data, len);
}

/* see falcon.h */
void
shake256_flip(shake256_context *sc)
{
	inner_shake256_flip((inner_shake256_context *)sc);
}

/* see falcon.h */
void
shake256_extract(shake256_context *sc, void *out, size_t len)
{
	inner_shake256_extract((inner_shake256_context *)sc, out, len);
}

/* see falcon.h */
void
shake256_init_prng_from_seed(shake256_context *sc,
	const void *seed, size_t seed_len)
{
	shake256_init(sc);
	shake256_inject(sc, seed, seed_len);
	shake256_flip(sc);
}

/* see falcon.h */
int
shake256_init_prng_from_system(shake256_context *sc)
{
	uint8_t seed[48];

	if (!Zf(get_seed)(seed, sizeof seed)) {
		return FALCON_ERR_RANDOM;
	}
	shake256_init(sc);
	shake256_inject(sc, seed, sizeof seed);
	shake256_flip(sc);
	return 0;
}

static inline uint8_t *
align_u64(void *tmp)
{
	uint8_t *atmp;
	unsigned off;

	atmp = tmp;
	off = (uintptr_t)atmp & 7u;
	if (off != 0) {
		atmp += 8u - off;
	}
	return atmp;
}

static inline uint8_t *
align_u16(void *tmp)
{
	uint8_t *atmp;

	atmp = tmp;
	if (((uintptr_t)atmp & 1u) != 0) {
		atmp ++;
	}
	return atmp;
}

static inline fpr *
align_fpr(void *tmp)
{
	uint8_t *atmp;
	unsigned off;

	atmp = tmp;
	off = (uintptr_t)atmp & 7u;
	if (off != 0) {
		atmp += 8u - off;
	}
	return (fpr *)atmp;
}

/* see falcon.h */
int
falcon_keygen_make(
	shake256_context *rng,
	unsigned logn,
	void *privkey, size_t privkey_len,
	void *pubkey, size_t pubkey_len,
	void *tmp, size_t tmp_len)
{
	int8_t *f, *g, *F;
	uint16_t *h;
	uint8_t *atmp;
	size_t n, u, v, sk_len, pk_len;
	uint8_t *sk, *pk;
	unsigned oldcw;

	/*
	 * Check parameters.
	 */
	if (logn < 1 || logn > 10) {
		return FALCON_ERR_BADARG;
	}
	if (privkey_len < FALCON_PRIVKEY_SIZE(logn)
		|| (pubkey != NULL && pubkey_len < FALCON_PUBKEY_SIZE(logn))
		|| tmp_len < FALCON_TMPSIZE_KEYGEN(logn))
	{
		return FALCON_ERR_SIZE;
	}

	/*
	 * Prepare buffers and generate private key.
	 */
	n = (size_t)1 << logn;
	f = tmp;
	g = f + n;
	F = g + n;
	atmp = align_u64(F + n);
	oldcw = set_fpu_cw(2);
	Zf(keygen)((inner_shake256_context *)rng,
		f, g, F, NULL, NULL, logn, atmp);
	set_fpu_cw(oldcw);

	/*
	 * Encode private key.
	 */
	sk = privkey;
	sk_len = FALCON_PRIVKEY_SIZE(logn);
	sk[0] = 0x50 + logn;
	u = 1;
	v = Zf(trim_i8_encode)(sk + u, sk_len - u,
		f, logn, Zf(max_fg_bits)[logn]);
	if (v == 0) {
		return FALCON_ERR_INTERNAL;
	}
	u += v;
	v = Zf(trim_i8_encode)(sk + u, sk_len - u,
		g, logn, Zf(max_fg_bits)[logn]);
	if (v == 0) {
		return FALCON_ERR_INTERNAL;
	}
	u += v;
	v = Zf(trim_i8_encode)(sk + u, sk_len - u,
		F, logn, Zf(max_FG_bits)[logn]);
	if (v == 0) {
		return FALCON_ERR_INTERNAL;
	}
	u += v;
	if (u != sk_len) {
		return FALCON_ERR_INTERNAL;
	}

	/*
	 * Recompute public key and encode it.
	 */
	if (pubkey != NULL) {
		h = (uint16_t *)align_u16(g + n);
		atmp = (uint8_t *)(h + n);
		if (!Zf(compute_public)(h, f, g, logn, atmp)) {
			return FALCON_ERR_INTERNAL;
		}
		pk = pubkey;
		pk_len = FALCON_PUBKEY_SIZE(logn);
		pk[0] = 0x00 + logn;
		v = Zf(modq_encode)(pk + 1, pk_len - 1, h, logn);
		if (v != pk_len - 1) {
			return FALCON_ERR_INTERNAL;
		}
	}

	return 0;
}

/* see falcon.h */
int
falcon_make_public(
	void *pubkey, size_t pubkey_len,
	const void *privkey, size_t privkey_len,
	void *tmp, size_t tmp_len)
{
	uint8_t *pk, *atmp;
	const uint8_t *sk;
	unsigned logn;
	size_t u, v, n, pk_len;
	int8_t *f, *g;
	uint16_t *h;

	/*
	 * Get degree from private key header byte, and check
	 * parameters.
	 */
	if (privkey_len == 0) {
		return FALCON_ERR_FORMAT;
	}
	sk = privkey;
	if ((sk[0] & 0xF0) != 0x50) {
		return FALCON_ERR_FORMAT;
	}
	logn = sk[0] & 0x0F;
	if (logn < 1 || logn > 10) {
		return FALCON_ERR_FORMAT;
	}
	if (privkey_len != FALCON_PRIVKEY_SIZE(logn)) {
		return FALCON_ERR_FORMAT;
	}
	if (pubkey_len < FALCON_PUBKEY_SIZE(logn)
		|| tmp_len < FALCON_TMPSIZE_MAKEPUB(logn))
	{
		return FALCON_ERR_SIZE;
	}

	/*
	 * Decode private key (f and g).
	 */
	n = (size_t)1 << logn;
	f = (int8_t *)tmp;
	g = f + n;
	u = 1;
	v = Zf(trim_i8_decode)(f, logn, Zf(max_fg_bits)[logn],
		sk + u, privkey_len - u);
	if (v == 0) {
		return FALCON_ERR_FORMAT;
	}
	u += v;
	v = Zf(trim_i8_decode)(g, logn, Zf(max_fg_bits)[logn],
		sk + u, privkey_len - u);
	if (v == 0) {
		return FALCON_ERR_FORMAT;
	}

	/*
	 * Compute public key.
	 */
	h = (uint16_t *)align_u16(g + n);
	atmp = (uint8_t *)(h + n);
	if (!Zf(compute_public)(h, f, g, logn, atmp)) {
		return FALCON_ERR_FORMAT;
	}

	/*
	 * Encode public key.
	 */
	pk = pubkey;
	pk_len = FALCON_PUBKEY_SIZE(logn);
	pk[0] = 0x00 + logn;
	v = Zf(modq_encode)(pk + 1, pk_len - 1, h, logn);
	if (v != pk_len - 1) {
		return FALCON_ERR_INTERNAL;
	}
	return 0;
}

/* see falcon.h */
int
falcon_get_logn(void *obj, size_t len)
{
	int logn;

	if (len == 0) {
		return FALCON_ERR_FORMAT;
	}
	logn = *(uint8_t *)obj & 0x0F;
	if (logn < 1 || logn > 10) {
		return FALCON_ERR_FORMAT;
	}
	return logn;
}

/* see falcon.h */
int
falcon_sign_start(shake256_context *rng,
	void *nonce,
	shake256_context *hash_data)
{
	shake256_extract(rng, nonce, 40);
	shake256_init(hash_data);
	shake256_inject(hash_data, nonce, 40);
	return 0;
}

/* see falcon.h */
int
falcon_sign_dyn_finish(shake256_context *rng,
	void *sig, size_t *sig_len, int sig_type,
	const void *privkey, size_t privkey_len,
	shake256_context *hash_data, const void *nonce,
	void *tmp, size_t tmp_len)
{
	unsigned logn;
	const uint8_t *sk;
	uint8_t *es;
	int8_t *f, *g, *F, *G;
	uint16_t *hm;
	int16_t *sv;
	uint8_t *atmp;
	size_t u, v, n, es_len;
	unsigned oldcw;
	inner_shake256_context sav_hash_data;

	/*
	 * Get degree from private key header byte, and check
	 * parameters.
	 */
	if (privkey_len == 0) {
		return FALCON_ERR_FORMAT;
	}
	sk = privkey;
	if ((sk[0] & 0xF0) != 0x50) {
		return FALCON_ERR_FORMAT;
	}
	logn = sk[0] & 0x0F;
	if (logn < 1 || logn > 10) {
		return FALCON_ERR_FORMAT;
	}
	if (privkey_len != FALCON_PRIVKEY_SIZE(logn)) {
		return FALCON_ERR_FORMAT;
	}
	if (tmp_len < FALCON_TMPSIZE_SIGNDYN(logn)) {
		return FALCON_ERR_SIZE;
	}
	es_len = *sig_len;
	if (es_len < 41) {
		return FALCON_ERR_SIZE;
	}
	switch (sig_type) {
	case FALCON_SIG_COMPRESSED:
		break;
	case FALCON_SIG_PADDED:
		if (*sig_len < FALCON_SIG_PADDED_SIZE(logn)) {
			return FALCON_ERR_SIZE;
		}
		break;
	case FALCON_SIG_CT:
		if (*sig_len < FALCON_SIG_CT_SIZE(logn)) {
			return FALCON_ERR_SIZE;
		}
		break;
	default:
		return FALCON_ERR_BADARG;
	}

	/*
	 * Decode private key elements, and complete private key.
	 */
	n = (size_t)1 << logn;
	f = (int8_t *)tmp;
	g = f + n;
	F = g + n;
	G = F + n;
	hm = (uint16_t *)(G + n);
	sv = (int16_t *)hm;
	atmp = align_u64(hm + n);
	u = 1;
	v = Zf(trim_i8_decode)(f, logn, Zf(max_fg_bits)[logn],
		sk + u, privkey_len - u);
	if (v == 0) {
		return FALCON_ERR_FORMAT;
	}
	u += v;
	v = Zf(trim_i8_decode)(g, logn, Zf(max_fg_bits)[logn],
		sk + u, privkey_len - u);
	if (v == 0) {
		return FALCON_ERR_FORMAT;
	}
	u += v;
	v = Zf(trim_i8_decode)(F, logn, Zf(max_FG_bits)[logn],
		sk + u, privkey_len - u);
	if (v == 0) {
		return FALCON_ERR_FORMAT;
	}
	u += v;
	if (u != privkey_len) {
		return FALCON_ERR_FORMAT;
	}
	if (!Zf(complete_private)(G, f, g, F, logn, atmp)) {
		return FALCON_ERR_FORMAT;
	}

	/*
	 * Hash message to a point.
	 */
	shake256_flip(hash_data);
	sav_hash_data = *(inner_shake256_context *)hash_data;

	/*
	 * Compute and encode signature.
	 */
	for (;;) {
		/*
		 * Hash message to a point. We must redo it when looping
		 * (in case of a padded signature format and a failed
		 * attempt due to an oversized compressed signature), because
		 * we overwrite the hash output with the signature (in order
		 * to save some RAM).
		 */
		*(inner_shake256_context *)hash_data = sav_hash_data;
		if (sig_type == FALCON_SIG_CT) {
			Zf(hash_to_point_ct)(
				(inner_shake256_context *)hash_data,
				hm, logn, atmp);
		} else {
			Zf(hash_to_point_vartime)(
				(inner_shake256_context *)hash_data,
				hm, logn);
		}
		oldcw = set_fpu_cw(2);
		Zf(sign_dyn)(sv, (inner_shake256_context *)rng,
			f, g, F, G, hm, logn, atmp);
		set_fpu_cw(oldcw);
		es = sig;
		es_len = *sig_len;
		memcpy(es + 1, nonce, 40);
		u = 41;
		switch (sig_type) {
			size_t tu;

		case FALCON_SIG_COMPRESSED:
			es[0] = 0x30 + logn;
			v = Zf(comp_encode)(es + u, es_len - u, sv, logn);
			if (v == 0) {
				return FALCON_ERR_SIZE;
			}
			break;
		case FALCON_SIG_PADDED:
			es[0] = 0x30 + logn;
			tu = FALCON_SIG_PADDED_SIZE(logn);
			v = Zf(comp_encode)(es + u, tu - u, sv, logn);
			if (v == 0) {
				/*
				 * Signature does not fit, loop.
				 */
				continue;
			}
			if (u + v < tu) {
				memset(es + u + v, 0, tu - (u + v));
				v = tu - u;
			}
			break;
		case FALCON_SIG_CT:
			es[0] = 0x50 + logn;
			v = Zf(trim_i16_encode)(es + u, es_len - u,
				sv, logn, Zf(max_sig_bits)[logn]);
			if (v == 0) {
				return FALCON_ERR_SIZE;
			}
			break;
		}
		*sig_len = u + v;
		return 0;
	}
}

/* see falcon.h */
int
falcon_expand_privkey(void *expanded_key, size_t expanded_key_len,
	const void *privkey, size_t privkey_len,
	void *tmp, size_t tmp_len)
{
	unsigned logn;
	const uint8_t *sk;
	int8_t *f, *g, *F, *G;
	uint8_t *atmp;
	size_t u, v, n;
	fpr *expkey;
	unsigned oldcw;

	/*
	 * Get degree from private key header byte, and check
	 * parameters.
	 */
	if (privkey_len == 0) {
		return FALCON_ERR_FORMAT;
	}
	sk = privkey;
	if ((sk[0] & 0xF0) != 0x50) {
		return FALCON_ERR_FORMAT;
	}
	logn = sk[0] & 0x0F;
	if (logn < 1 || logn > 10) {
		return FALCON_ERR_FORMAT;
	}
	if (privkey_len != FALCON_PRIVKEY_SIZE(logn)) {
		return FALCON_ERR_FORMAT;
	}
	if (expanded_key_len < FALCON_EXPANDEDKEY_SIZE(logn)
		|| tmp_len < FALCON_TMPSIZE_EXPANDPRIV(logn))
	{
		return FALCON_ERR_SIZE;
	}

	/*
	 * Decode private key elements, and complete private key.
	 */
	n = (size_t)1 << logn;
	f = (int8_t *)tmp;
	g = f + n;
	F = g + n;
	G = F + n;
	atmp = align_u64(G + n);
	u = 1;
	v = Zf(trim_i8_decode)(f, logn, Zf(max_fg_bits)[logn],
		sk + u, privkey_len - u);
	if (v == 0) {
		return FALCON_ERR_FORMAT;
	}
	u += v;
	v = Zf(trim_i8_decode)(g, logn, Zf(max_fg_bits)[logn],
		sk + u, privkey_len - u);
	if (v == 0) {
		return FALCON_ERR_FORMAT;
	}
	u += v;
	v = Zf(trim_i8_decode)(F, logn, Zf(max_FG_bits)[logn],
		sk + u, privkey_len - u);
	if (v == 0) {
		return FALCON_ERR_FORMAT;
	}
	u += v;
	if (u != privkey_len) {
		return FALCON_ERR_FORMAT;
	}
	if (!Zf(complete_private)(G, f, g, F, logn, atmp)) {
		return FALCON_ERR_FORMAT;
	}

	/*
	 * Expand private key.
	 */
	*(uint8_t *)expanded_key = logn;
	expkey = align_fpr((uint8_t *)expanded_key + 1);
	oldcw = set_fpu_cw(2);
	Zf(expand_privkey)(expkey, f, g, F, G, logn, atmp);
	set_fpu_cw(oldcw);
	return 0;
}

/* see falcon.h */
int
falcon_sign_tree_finish(shake256_context *rng,
	void *sig, size_t *sig_len, int sig_type,
	const void *expanded_key,
	shake256_context *hash_data, const void *nonce,
	void *tmp, size_t tmp_len)
{
	unsigned logn;
	uint8_t *es;
	const fpr *expkey;
	uint16_t *hm;
	int16_t *sv;
	uint8_t *atmp;
	size_t u, v, n, es_len;
	unsigned oldcw;
	inner_shake256_context sav_hash_data;

	/*
	 * Get degree from private key header byte, and check
	 * parameters.
	 */
	logn = *(const uint8_t *)expanded_key;
	if (logn < 1 || logn > 10) {
		return FALCON_ERR_FORMAT;
	}
	if (tmp_len < FALCON_TMPSIZE_SIGNTREE(logn)) {
		return FALCON_ERR_SIZE;
	}
	es_len = *sig_len;
	if (es_len < 41) {
		return FALCON_ERR_SIZE;
	}
	expkey = (const fpr *)align_fpr((uint8_t *)expanded_key + 1);
	switch (sig_type) {
	case FALCON_SIG_COMPRESSED:
		break;
	case FALCON_SIG_PADDED:
		if (*sig_len < FALCON_SIG_PADDED_SIZE(logn)) {
			return FALCON_ERR_SIZE;
		}
		break;
	case FALCON_SIG_CT:
		if (*sig_len < FALCON_SIG_CT_SIZE(logn)) {
			return FALCON_ERR_SIZE;
		}
		break;
	default:
		return FALCON_ERR_BADARG;
	}

	n = (size_t)1 << logn;
	hm = (uint16_t *)align_u16(tmp);
	sv = (int16_t *)hm;
	atmp = align_u64(sv + n);

	/*
	 * Hash message to a point.
	 */
	shake256_flip(hash_data);
	sav_hash_data = *(inner_shake256_context *)hash_data;

	/*
	 * Compute and encode signature.
	 */
	for (;;) {
		/*
		 * Hash message to a point. We must redo it when looping
		 * (in case of a padded signature format and a failed
		 * attempt due to an oversized compressed signature), because
		 * we overwrite the hash output with the signature (in order
		 * to save some RAM).
		 */
		*(inner_shake256_context *)hash_data = sav_hash_data;
		if (sig_type == FALCON_SIG_CT) {
			Zf(hash_to_point_ct)(
				(inner_shake256_context *)hash_data,
				hm, logn, atmp);
		} else {
			Zf(hash_to_point_vartime)(
				(inner_shake256_context *)hash_data,
				hm, logn);
		}
		oldcw = set_fpu_cw(2);
		Zf(sign_tree)(sv, (inner_shake256_context *)rng,
			expkey, hm, logn, atmp);
		set_fpu_cw(oldcw);
		es = sig;
		es_len = *sig_len;
		memcpy(es + 1, nonce, 40);
		u = 41;
		switch (sig_type) {
			size_t tu;

		case FALCON_SIG_COMPRESSED:
			es[0] = 0x30 + logn;
			v = Zf(comp_encode)(es + u, es_len - u, sv, logn);
			if (v == 0) {
				return FALCON_ERR_SIZE;
			}
			break;
		case FALCON_SIG_PADDED:
			es[0] = 0x30 + logn;
			tu = FALCON_SIG_PADDED_SIZE(logn);
			v = Zf(comp_encode)(es + u, tu - u, sv, logn);
			if (v == 0) {
				/*
				 * Signature does not fit, loop.
				 */
				continue;
			}
			if (u + v < tu) {
				memset(es + u + v, 0, tu - (u + v));
				v = tu - u;
			}
			break;
		case FALCON_SIG_CT:
			es[0] = 0x50 + logn;
			v = Zf(trim_i16_encode)(es + u, es_len - u,
				sv, logn, Zf(max_sig_bits)[logn]);
			if (v == 0) {
				return FALCON_ERR_SIZE;
			}
			break;
		}
		*sig_len = u + v;
		return 0;
	}
}

/* see falcon.h */
int
falcon_sign_dyn(shake256_context *rng,
	void *sig, size_t *sig_len, int sig_type,
	const void *privkey, size_t privkey_len,
	const void *data, size_t data_len,
	void *tmp, size_t tmp_len)
{
	shake256_context hd;
	uint8_t nonce[40];
	int r;

	r = falcon_sign_start(rng, nonce, &hd);
	if (r != 0) {
		return r;
	}
	shake256_inject(&hd, data, data_len);
	return falcon_sign_dyn_finish(rng, sig, sig_len, sig_type,
		privkey, privkey_len, &hd, nonce, tmp, tmp_len);
}

/* see falcon.h */
int
falcon_sign_tree(shake256_context *rng,
	void *sig, size_t *sig_len, int sig_type,
	const void *expanded_key,
	const void *data, size_t data_len,
	void *tmp, size_t tmp_len)
{
	shake256_context hd;
	uint8_t nonce[40];
	int r;

	r = falcon_sign_start(rng, nonce, &hd);
	if (r != 0) {
		return r;
	}
	shake256_inject(&hd, data, data_len);
	return falcon_sign_tree_finish(rng, sig, sig_len, sig_type,
		expanded_key, &hd, nonce, tmp, tmp_len);
}

/* see falcon.h */
int
falcon_verify_start(shake256_context *hash_data,
	const void *sig, size_t sig_len)
{
	if (sig_len < 41) {
		return FALCON_ERR_FORMAT;
	}
	shake256_init(hash_data);
	shake256_inject(hash_data, (const uint8_t *)sig + 1, 40);
	return 0;
}

/* see falcon.h */
int
falcon_verify_finish(const void *sig, size_t sig_len, int sig_type,
	const void *pubkey, size_t pubkey_len,
	shake256_context *hash_data,
	void *tmp, size_t tmp_len)
{
	unsigned logn;
	uint8_t *atmp;
	const uint8_t *pk, *es;
	size_t u, v, n;
	uint16_t *h, *hm;
	int16_t *sv;
	int ct;

	/*
	 * Get Falcon degree from public key; verify consistency with
	 * signature value, and check parameters.
	 */
	if (sig_len < 41 || pubkey_len == 0) {
		return FALCON_ERR_FORMAT;
	}
	es = sig;
	pk = pubkey;
	if ((pk[0] & 0xF0) != 0x00) {
		return FALCON_ERR_FORMAT;
	}
	logn = pk[0] & 0x0F;
	if (logn < 1 || logn > 10) {
		return FALCON_ERR_FORMAT;
	}
	if ((es[0] & 0x0F) != logn) {
		return FALCON_ERR_BADSIG;
	}
	ct = 0;
	switch (sig_type) {
	case 0:
		switch (es[0] & 0xF0) {
		case 0x30:
			break;
		case 0x50:
			if (sig_len != FALCON_SIG_CT_SIZE(logn)) {
				return FALCON_ERR_FORMAT;
			}
			ct = 1;
			break;
		default:
			return FALCON_ERR_BADSIG;
		}
		break;
	case FALCON_SIG_COMPRESSED:
		if ((es[0] & 0xF0) != 0x30) {
			return FALCON_ERR_FORMAT;
		}
		break;
	case FALCON_SIG_PADDED:
		if ((es[0] & 0xF0) != 0x30) {
			return FALCON_ERR_FORMAT;
		}
		if (sig_len != FALCON_SIG_PADDED_SIZE(logn)) {
			return FALCON_ERR_FORMAT;
		}
		break;
	case FALCON_SIG_CT:
		if ((es[0] & 0xF0) != 0x50) {
			return FALCON_ERR_FORMAT;
		}
		if (sig_len != FALCON_SIG_CT_SIZE(logn)) {
			return FALCON_ERR_FORMAT;
		}
		ct = 1;
		break;
	default:
		return FALCON_ERR_BADARG;
	}
	if (pubkey_len != FALCON_PUBKEY_SIZE(logn)) {
		return FALCON_ERR_FORMAT;
	}
	if (tmp_len < FALCON_TMPSIZE_VERIFY(logn)) {
		return FALCON_ERR_SIZE;
	}

	n = (size_t)1 << logn;
	h = (uint16_t *)align_u16(tmp);
	hm = h + n;
	sv = (int16_t *)(hm + n);
	atmp = (uint8_t *)(sv + n);

	/*
	 * Decode public key.
	 */
	if (Zf(modq_decode)(h, logn, pk + 1, pubkey_len - 1)
		!= pubkey_len - 1)
	{
		return FALCON_ERR_FORMAT;
	}

	/*
	 * Decode signature value.
	 */
	u = 41;
	if (ct) {
		v = Zf(trim_i16_decode)(sv, logn,
			Zf(max_sig_bits)[logn], es + u, sig_len - u);
	} else {
		v = Zf(comp_decode)(sv, logn, es + u, sig_len - u);
	}
	if (v == 0) {
		return FALCON_ERR_FORMAT;
	}
	if ((u + v) != sig_len) {
		/*
		 * Extra bytes of value 0 are tolerated only for the
		 * "padded" format.
		 */
		if ((sig_type == 0 && sig_len == FALCON_SIG_PADDED_SIZE(logn))
			|| sig_type == FALCON_SIG_PADDED)
		{
			while (u + v < sig_len) {
				if (es[u + v] != 0) {
					return FALCON_ERR_FORMAT;
				}
				v ++;
			}
		} else {
			return FALCON_ERR_FORMAT;
		}
	}

	/*
	 * Hash message to point.
	 */
	shake256_flip(hash_data);
	if (ct) {
		Zf(hash_to_point_ct)(
			(inner_shake256_context *)hash_data, hm, logn, atmp);
	} else {
		Zf(hash_to_point_vartime)(
			(inner_shake256_context *)hash_data, hm, logn);
	}

	/*
	 * Verify signature.
	 */
	Zf(to_ntt_monty)(h, logn);
	if (!Zf(verify_raw)(hm, sv, h, logn, atmp)) {
		return FALCON_ERR_BADSIG;
	}
	return 0;
}

/* see falcon.h */
int
falcon_verify(const void *sig, size_t sig_len, int sig_type,
	const void *pubkey, size_t pubkey_len,
	const void *data, size_t data_len,
	void *tmp, size_t tmp_len)
{
	shake256_context hd;
	int r;

	r = falcon_verify_start(&hd, sig, sig_len);
	if (r < 0) {
		return r;
	}
	shake256_inject(&hd, data, data_len);
	return falcon_verify_finish(sig, sig_len, sig_type,
		pubkey, pubkey_len, &hd, tmp, tmp_len);
}

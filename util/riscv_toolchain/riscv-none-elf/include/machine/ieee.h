#ifndef _MACHINE_IEEE_H_
#define _MACHINE_IEEE_H_
#include <sys/types.h>
#include <sys/cdefs.h>
#include <machine/ieeefp.h>
#include <float.h>

#if LDBL_MANT_DIG == 24
#define EXT_IMPLICIT_NBIT
#define EXT_TO_ARRAY32(p, a) do {      \
    (a)[0] = (p)->ext_frac;  \
} while (0)
#ifdef __IEEE_LITTLE_ENDIAN
struct ieee_ext {
    uint32_t   ext_frac:23;
    uint32_t   ext_exp:8;
    uint32_t   ext_sign:1;
};
#endif
#ifdef __IEEE_BIG_ENDIAN
struct ieee_ext {
#ifndef ___IEEE_BYTES_LITTLE_ENDIAN
    uint32_t   ext_sign:1;
    uint32_t   ext_exp:8;
    uint32_t   ext_frac:23;
#else /* ARMEL without __VFP_FP__ */
    uint32_t   ext_frac:23;
    uint32_t   ext_exp:8;
    uint32_t   ext_sign:1;
#endif
};
#endif
#elif LDBL_MANT_DIG == 53
#define EXT_IMPLICIT_NBIT
#define EXT_TO_ARRAY32(p, a) do {       \
    (a)[0] = (p)->ext_fracl;  \
    (a)[1] = (p)->ext_frach;  \
} while (0)
#ifdef __IEEE_LITTLE_ENDIAN
struct ieee_ext {
    uint32_t   ext_fracl;
    uint32_t   ext_frach:20;
    uint32_t   ext_exp:11;
    uint32_t   ext_sign:1;
};
#endif
#ifdef __IEEE_BIG_ENDIAN
struct ieee_ext {
#ifndef ___IEEE_BYTES_LITTLE_ENDIAN
    uint32_t   ext_sign:1;
    uint32_t   ext_exp:11;
    uint32_t   ext_frach:20;
#else /* ARMEL without __VFP_FP__ */
    uint32_t   ext_frach:20;
    uint32_t   ext_exp:11;
    uint32_t   ext_sign:1;
#endif
    uint32_t   ext_fracl;
};
#endif
#elif LDBL_MANT_DIG == 64
#define EXT_TO_ARRAY32(p, a) do {       \
    (a)[0] = (p)->ext_fracl;  \
    (a)[1] = (p)->ext_frach;  \
} while (0)
#ifdef __IEEE_LITTLE_ENDIAN /* for Intel CPU */
struct ieee_ext {
    uint32_t   ext_fracl;
    uint32_t   ext_frach;
    uint32_t   ext_exp:15;
    uint32_t   ext_sign:1;
    uint32_t   ext_padl:16;
    uint32_t   ext_padh;
};
#endif
#ifdef __IEEE_BIG_ENDIAN
struct ieee_ext {
#ifndef ___IEEE_BYTES_LITTLE_ENDIAN /* for m68k */
    uint32_t   ext_sign:1;
    uint32_t   ext_exp:15;
    uint32_t   ext_pad:16;
#else /* ARM FPA10 math coprocessor */
    uint32_t   ext_exp:15;
    uint32_t   ext_pad:16;
    uint32_t   ext_sign:1;
#endif
    uint32_t   ext_frach;
    uint32_t   ext_fracl;
};
#endif
#elif LDBL_MANT_DIG == 113
#define EXT_IMPLICIT_NBIT
#define EXT_TO_ARRAY32(p, a) do {        \
    (a)[0] = (p)->ext_fracl;   \
    (a)[1] = (p)->ext_fraclm;  \
    (a)[2] = (p)->ext_frachm;  \
    (a)[3] = (p)->ext_frach;   \
} while (0)
#ifdef __IEEE_LITTLE_ENDIAN
struct ieee_ext {
    uint32_t   ext_fracl;
    uint32_t   ext_fraclm;
    uint32_t   ext_frachm;
    uint32_t   ext_frach:16;
    uint32_t   ext_exp:15;
    uint32_t   ext_sign:1;
};
#endif
#ifdef __IEEE_BIG_ENDIAN
struct ieee_ext {
#ifndef ___IEEE_BYTES_LITTLE_ENDIAN
    uint32_t   ext_sign:1;
    uint32_t   ext_exp:15;
    uint32_t   ext_frach:16;
#else /* ARMEL without __VFP_FP__ */
    uint32_t   ext_frach:16;
    uint32_t   ext_exp:15;
    uint32_t   ext_sign:1;
#endif
    uint32_t   ext_frachm;
    uint32_t   ext_fraclm;
    uint32_t   ext_fracl;
};
#endif
#endif

#endif /* _MACHINE_IEEE_H_ */

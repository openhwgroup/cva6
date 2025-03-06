/* newlib.h.  Generated from newlib.hin by configure.  */
/* newlib.hin.  Generated from configure.ac by autoheader.  */

/* NB: The contents are filtered before being installed. */

#ifndef __NEWLIB_H__
#define __NEWLIB_H__ 1

/* Newlib version */
#include <_newlib_version.h>

/* Define to 1 if the system has the type `long double'. */

/* Define to the address where bug reports for this package should be sent. */

/* Define to the full name of this package. */

/* Define to the full name and version of this package. */

/* Define to the one symbol short name of this package. */

/* Define to the home page for this package. */

/* Define to the version of this package. */

/* If atexit() may dynamically allocate space for cleanup functions. */
/* #undef _ATEXIT_DYNAMIC_ALLOC */

/* EL/IX level */
/* #undef _ELIX_LEVEL */

/* Define if fseek functions support seek optimization. */
#define _FSEEK_OPTIMIZATION 1

/* Define if ivo supported in streamio. */
#define _FVWRITE_IN_STREAMIO 1

/* Define if compiler supports -fno-tree-loop-distribute-patterns. */
#define _HAVE_CC_INHIBIT_LOOP_TO_LIBCALL 1

/* Define if the linker supports .preinit_array/.init_array/.fini_array
   sections. */
#define _HAVE_INITFINI_ARRAY 1

/* Define if the platform supports long double type. */
#define _HAVE_LONG_DOUBLE 1

/* ICONV enabled. */
/* #undef _ICONV_ENABLED */

/* Enable ICONV external CCS files loading capabilities. */
/* #undef _ICONV_ENABLE_EXTERNAL_CCS */

/* Support big5 input encoding. */
/* #undef _ICONV_FROM_ENCODING_BIG5 */

/* Support cp775 input encoding. */
/* #undef _ICONV_FROM_ENCODING_CP775 */

/* Support cp850 input encoding. */
/* #undef _ICONV_FROM_ENCODING_CP850 */

/* Support cp852 input encoding. */
/* #undef _ICONV_FROM_ENCODING_CP852 */

/* Support cp855 input encoding. */
/* #undef _ICONV_FROM_ENCODING_CP855 */

/* Support cp866 input encoding. */
/* #undef _ICONV_FROM_ENCODING_CP866 */

/* Support euc_jp input encoding. */
/* #undef _ICONV_FROM_ENCODING_EUC_JP */

/* Support euc_kr input encoding. */
/* #undef _ICONV_FROM_ENCODING_EUC_KR */

/* Support euc_tw input encoding. */
/* #undef _ICONV_FROM_ENCODING_EUC_TW */

/* Support iso_8859_1 input encoding. */
/* #undef _ICONV_FROM_ENCODING_ISO_8859_1 */

/* Support iso_8859_10 input encoding. */
/* #undef _ICONV_FROM_ENCODING_ISO_8859_10 */

/* Support iso_8859_11 input encoding. */
/* #undef _ICONV_FROM_ENCODING_ISO_8859_11 */

/* Support iso_8859_13 input encoding. */
/* #undef _ICONV_FROM_ENCODING_ISO_8859_13 */

/* Support iso_8859_14 input encoding. */
/* #undef _ICONV_FROM_ENCODING_ISO_8859_14 */

/* Support iso_8859_15 input encoding. */
/* #undef _ICONV_FROM_ENCODING_ISO_8859_15 */

/* Support iso_8859_2 input encoding. */
/* #undef _ICONV_FROM_ENCODING_ISO_8859_2 */

/* Support iso_8859_3 input encoding. */
/* #undef _ICONV_FROM_ENCODING_ISO_8859_3 */

/* Support iso_8859_4 input encoding. */
/* #undef _ICONV_FROM_ENCODING_ISO_8859_4 */

/* Support iso_8859_5 input encoding. */
/* #undef _ICONV_FROM_ENCODING_ISO_8859_5 */

/* Support iso_8859_6 input encoding. */
/* #undef _ICONV_FROM_ENCODING_ISO_8859_6 */

/* Support iso_8859_7 input encoding. */
/* #undef _ICONV_FROM_ENCODING_ISO_8859_7 */

/* Support iso_8859_8 input encoding. */
/* #undef _ICONV_FROM_ENCODING_ISO_8859_8 */

/* Support iso_8859_9 input encoding. */
/* #undef _ICONV_FROM_ENCODING_ISO_8859_9 */

/* Support iso_ir_111 input encoding. */
/* #undef _ICONV_FROM_ENCODING_ISO_IR_111 */

/* Support koi8_r input encoding. */
/* #undef _ICONV_FROM_ENCODING_KOI8_R */

/* Support koi8_ru input encoding. */
/* #undef _ICONV_FROM_ENCODING_KOI8_RU */

/* Support koi8_u input encoding. */
/* #undef _ICONV_FROM_ENCODING_KOI8_U */

/* Support koi8_uni input encoding. */
/* #undef _ICONV_FROM_ENCODING_KOI8_UNI */

/* Support ucs_2 input encoding. */
/* #undef _ICONV_FROM_ENCODING_UCS_2 */

/* Support ucs_2be input encoding. */
/* #undef _ICONV_FROM_ENCODING_UCS_2BE */

/* Support ucs_2le input encoding. */
/* #undef _ICONV_FROM_ENCODING_UCS_2LE */

/* Support ucs_2_internal input encoding. */
/* #undef _ICONV_FROM_ENCODING_UCS_2_INTERNAL */

/* Support ucs_4 input encoding. */
/* #undef _ICONV_FROM_ENCODING_UCS_4 */

/* Support ucs_4be input encoding. */
/* #undef _ICONV_FROM_ENCODING_UCS_4BE */

/* Support ucs_4le input encoding. */
/* #undef _ICONV_FROM_ENCODING_UCS_4LE */

/* Support ucs_4_internal input encoding. */
/* #undef _ICONV_FROM_ENCODING_UCS_4_INTERNAL */

/* Support us_ascii input encoding. */
/* #undef _ICONV_FROM_ENCODING_US_ASCII */

/* Support utf_16 input encoding. */
/* #undef _ICONV_FROM_ENCODING_UTF_16 */

/* Support utf_16be input encoding. */
/* #undef _ICONV_FROM_ENCODING_UTF_16BE */

/* Support utf_16le input encoding. */
/* #undef _ICONV_FROM_ENCODING_UTF_16LE */

/* Support utf_8 input encoding. */
/* #undef _ICONV_FROM_ENCODING_UTF_8 */

/* Support win_1250 input encoding. */
/* #undef _ICONV_FROM_ENCODING_WIN_1250 */

/* Support win_1251 input encoding. */
/* #undef _ICONV_FROM_ENCODING_WIN_1251 */

/* Support win_1252 input encoding. */
/* #undef _ICONV_FROM_ENCODING_WIN_1252 */

/* Support win_1253 input encoding. */
/* #undef _ICONV_FROM_ENCODING_WIN_1253 */

/* Support win_1254 input encoding. */
/* #undef _ICONV_FROM_ENCODING_WIN_1254 */

/* Support win_1255 input encoding. */
/* #undef _ICONV_FROM_ENCODING_WIN_1255 */

/* Support win_1256 input encoding. */
/* #undef _ICONV_FROM_ENCODING_WIN_1256 */

/* Support win_1257 input encoding. */
/* #undef _ICONV_FROM_ENCODING_WIN_1257 */

/* Support win_1258 input encoding. */
/* #undef _ICONV_FROM_ENCODING_WIN_1258 */

/* Support big5 output encoding. */
/* #undef _ICONV_TO_ENCODING_BIG5 */

/* Support cp775 output encoding. */
/* #undef _ICONV_TO_ENCODING_CP775 */

/* Support cp850 output encoding. */
/* #undef _ICONV_TO_ENCODING_CP850 */

/* Support cp852 output encoding. */
/* #undef _ICONV_TO_ENCODING_CP852 */

/* Support cp855 output encoding. */
/* #undef _ICONV_TO_ENCODING_CP855 */

/* Support cp866 output encoding. */
/* #undef _ICONV_TO_ENCODING_CP866 */

/* Support euc_jp output encoding. */
/* #undef _ICONV_TO_ENCODING_EUC_JP */

/* Support euc_kr output encoding. */
/* #undef _ICONV_TO_ENCODING_EUC_KR */

/* Support euc_tw output encoding. */
/* #undef _ICONV_TO_ENCODING_EUC_TW */

/* Support iso_8859_1 output encoding. */
/* #undef _ICONV_TO_ENCODING_ISO_8859_1 */

/* Support iso_8859_10 output encoding. */
/* #undef _ICONV_TO_ENCODING_ISO_8859_10 */

/* Support iso_8859_11 output encoding. */
/* #undef _ICONV_TO_ENCODING_ISO_8859_11 */

/* Support iso_8859_13 output encoding. */
/* #undef _ICONV_TO_ENCODING_ISO_8859_13 */

/* Support iso_8859_14 output encoding. */
/* #undef _ICONV_TO_ENCODING_ISO_8859_14 */

/* Support iso_8859_15 output encoding. */
/* #undef _ICONV_TO_ENCODING_ISO_8859_15 */

/* Support iso_8859_2 output encoding. */
/* #undef _ICONV_TO_ENCODING_ISO_8859_2 */

/* Support iso_8859_3 output encoding. */
/* #undef _ICONV_TO_ENCODING_ISO_8859_3 */

/* Support iso_8859_4 output encoding. */
/* #undef _ICONV_TO_ENCODING_ISO_8859_4 */

/* Support iso_8859_5 output encoding. */
/* #undef _ICONV_TO_ENCODING_ISO_8859_5 */

/* Support iso_8859_6 output encoding. */
/* #undef _ICONV_TO_ENCODING_ISO_8859_6 */

/* Support iso_8859_7 output encoding. */
/* #undef _ICONV_TO_ENCODING_ISO_8859_7 */

/* Support iso_8859_8 output encoding. */
/* #undef _ICONV_TO_ENCODING_ISO_8859_8 */

/* Support iso_8859_9 output encoding. */
/* #undef _ICONV_TO_ENCODING_ISO_8859_9 */

/* Support iso_ir_111 output encoding. */
/* #undef _ICONV_TO_ENCODING_ISO_IR_111 */

/* Support koi8_r output encoding. */
/* #undef _ICONV_TO_ENCODING_KOI8_R */

/* Support koi8_ru output encoding. */
/* #undef _ICONV_TO_ENCODING_KOI8_RU */

/* Support koi8_u output encoding. */
/* #undef _ICONV_TO_ENCODING_KOI8_U */

/* Support koi8_uni output encoding. */
/* #undef _ICONV_TO_ENCODING_KOI8_UNI */

/* Support ucs_2 output encoding. */
/* #undef _ICONV_TO_ENCODING_UCS_2 */

/* Support ucs_2be output encoding. */
/* #undef _ICONV_TO_ENCODING_UCS_2BE */

/* Support ucs_2le output encoding. */
/* #undef _ICONV_TO_ENCODING_UCS_2LE */

/* Support ucs_2_internal output encoding. */
/* #undef _ICONV_TO_ENCODING_UCS_2_INTERNAL */

/* Support ucs_4 output encoding. */
/* #undef _ICONV_TO_ENCODING_UCS_4 */

/* Support ucs_4be output encoding. */
/* #undef _ICONV_TO_ENCODING_UCS_4BE */

/* Support ucs_4le output encoding. */
/* #undef _ICONV_TO_ENCODING_UCS_4LE */

/* Support ucs_4_internal output encoding. */
/* #undef _ICONV_TO_ENCODING_UCS_4_INTERNAL */

/* Support us_ascii output encoding. */
/* #undef _ICONV_TO_ENCODING_US_ASCII */

/* Support utf_16 output encoding. */
/* #undef _ICONV_TO_ENCODING_UTF_16 */

/* Support utf_16be output encoding. */
/* #undef _ICONV_TO_ENCODING_UTF_16BE */

/* Support utf_16le output encoding. */
/* #undef _ICONV_TO_ENCODING_UTF_16LE */

/* Support utf_8 output encoding. */
/* #undef _ICONV_TO_ENCODING_UTF_8 */

/* Support win_1250 output encoding. */
/* #undef _ICONV_TO_ENCODING_WIN_1250 */

/* Support win_1251 output encoding. */
/* #undef _ICONV_TO_ENCODING_WIN_1251 */

/* Support win_1252 output encoding. */
/* #undef _ICONV_TO_ENCODING_WIN_1252 */

/* Support win_1253 output encoding. */
/* #undef _ICONV_TO_ENCODING_WIN_1253 */

/* Support win_1254 output encoding. */
/* #undef _ICONV_TO_ENCODING_WIN_1254 */

/* Support win_1255 output encoding. */
/* #undef _ICONV_TO_ENCODING_WIN_1255 */

/* Support win_1256 output encoding. */
/* #undef _ICONV_TO_ENCODING_WIN_1256 */

/* Support win_1257 output encoding. */
/* #undef _ICONV_TO_ENCODING_WIN_1257 */

/* Support win_1258 output encoding. */
/* #undef _ICONV_TO_ENCODING_WIN_1258 */

/* Define if the platform long double type is equal to double. */
/* #undef _LDBL_EQ_DBL */

/* Define if lite version of exit supported. */
/* #undef _LITE_EXIT */

/* Multibyte supported. */
/* #undef _MB_CAPABLE */

/* Multibyte max length. */
#define _MB_LEN_MAX 1

/* Define if small footprint nano-formatted-IO implementation used. */
/* #undef _NANO_FORMATTED_IO */

/* nano version of malloc is used. */
/* #undef _NANO_MALLOC */

/* Verify _REENT_CHECK macros allocate memory successfully. */
#define _REENT_CHECK_VERIFY 1

/* Define if using retargetable functions for default lock routines. */
/* #undef _RETARGETABLE_LOCKING */

/* Define if unbuffered stream file optimization is supported. */
#define _UNBUF_STREAM_OPT 1

/* Enable C99 formats support (e.g. %a, %zu, ...) in IO functions like
   printf/scanf. */
#define _WANT_IO_C99_FORMATS 1

/* Define to enable long double type support in IO functions like
   printf/scanf. */
#define _WANT_IO_LONG_DOUBLE 1

/* Define to enable long long type support in IO functions like printf/scanf.
   */
#define _WANT_IO_LONG_LONG 1

/* Positional argument support in printf functions enabled. */
/* #undef _WANT_IO_POS_ARGS */

/* Define to enable backward binary compatibility for struct _reent. */
/* #undef _WANT_REENT_BACKWARD_BINARY_COMPAT */

/* Optional reentrant struct support. Used mostly on platforms with very
   restricted storage. */
/* #undef _WANT_REENT_SMALL */

/* Define to enable thread-local storage objects as a replacment for struct
   _reent members. */
/* #undef _WANT_REENT_THREAD_LOCAL */

/* Register application finalization function using atexit. */
#define _WANT_REGISTER_FINI 1

/* Define if using gdtoa rather than legacy ldtoa. */
#define _WANT_USE_GDTOA 1

/* Define to use type long for time_t. */
/* #undef _WANT_USE_LONG_TIME_T */

/* Define if wide char orientation is supported. */
#define _WIDE_ORIENT 1

#endif /* !__NEWLIB_H__ */

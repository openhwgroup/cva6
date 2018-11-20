/* config.h.  Generated from config.h.in by configure.  */
/* config.h.in.  Generated from configure.ac by autoheader.  */

/* Define if building universal (internal helper macro) */
/* #undef AC_APPLE_UNIVERSAL_BUILD */

/* Default value for --isa switch */
#define DEFAULT_ISA "RV64IMAFDC"

/* Path to the device-tree-compiler */
#define DTC "/home/zarubaf/bin/dtc"

/* Define if subproject MCPPBS_SPROJ_NORM is enabled */
#define DUMMY_ROCC_ENABLED /**/

/* Define to 1 if you have the <inttypes.h> header file. */
#define HAVE_INTTYPES_H 1

/* Define to 1 if you have the `fesvr' library (-lfesvr). */
#define HAVE_LIBFESVR 1

/* Define to 1 if you have the `pthread' library (-lpthread). */
#define HAVE_LIBPTHREAD 1

/* Define to 1 if you have the <memory.h> header file. */
#define HAVE_MEMORY_H 1

/* Define to 1 if you have the <stdint.h> header file. */
#define HAVE_STDINT_H 1

/* Define to 1 if you have the <stdlib.h> header file. */
#define HAVE_STDLIB_H 1

/* Define to 1 if you have the <strings.h> header file. */
#define HAVE_STRINGS_H 1

/* Define to 1 if you have the <string.h> header file. */
#define HAVE_STRING_H 1

/* Define to 1 if you have the <sys/stat.h> header file. */
#define HAVE_SYS_STAT_H 1

/* Define to 1 if you have the <sys/types.h> header file. */
#define HAVE_SYS_TYPES_H 1

/* Define to 1 if you have the <unistd.h> header file. */
#define HAVE_UNISTD_H 1

/* Define to the address where bug reports for this package should be sent. */
#define PACKAGE_BUGREPORT "Andrew Waterman"

/* Define to the full name of this package. */
#define PACKAGE_NAME "RISC-V ISA Simulator"

/* Define to the full name and version of this package. */
#define PACKAGE_STRING "RISC-V ISA Simulator ?"

/* Define to the one symbol short name of this package. */
#define PACKAGE_TARNAME "spike"

/* Define to the home page for this package. */
#define PACKAGE_URL ""

/* Define to the version of this package. */
#define PACKAGE_VERSION "?"

/* Define if subproject MCPPBS_SPROJ_NORM is enabled */
#define RISCV_ENABLED /**/

/* Enable commit log generation */
#define RISCV_ENABLE_COMMITLOG /**/

/* Enable hardware management of PTE accessed and dirty bits */
/* #undef RISCV_ENABLE_DIRTY */

/* Enable PC histogram generation */
/* #undef RISCV_ENABLE_HISTOGRAM */

/* Enable hardware support for misaligned loads and stores */
/* #undef RISCV_ENABLE_MISALIGNED */

/* Define if subproject MCPPBS_SPROJ_NORM is enabled */
#define SOFTFLOAT_ENABLED /**/

/* Define if subproject MCPPBS_SPROJ_NORM is enabled */
#define SPIKE_MAIN_ENABLED /**/

/* Define to 1 if you have the ANSI C header files. */
#define STDC_HEADERS 1

/* Define WORDS_BIGENDIAN to 1 if your processor stores words with the most
   significant byte first (like Motorola and SPARC, unlike Intel). */
#if defined AC_APPLE_UNIVERSAL_BUILD
# if defined __BIG_ENDIAN__
#  define WORDS_BIGENDIAN 1
# endif
#else
# ifndef WORDS_BIGENDIAN
/* #  undef WORDS_BIGENDIAN */
# endif
#endif

/*
    (C) Copyright 2014 CEA LIST. All Rights Reserved.
    Contributor(s): Olivier BICHLER (olivier.bichler@cea.fr)

    This software is governed by the CeCILL-C license under French law and
    abiding by the rules of distribution of free software.  You can  use,
    modify and/ or redistribute the software under the terms of the CeCILL-C
    license as circulated by CEA, CNRS and INRIA at the following URL
    "http://www.cecill.info".

    As a counterpart to the access to the source code and  rights to copy,
    modify and redistribute granted by the license, users are provided only
    with a limited warranty  and the software's author,  the holder of the
    economic rights,  and the successive licensors  have only  limited
    liability.

    The fact that you are presently reading this means that you have had
    knowledge of the CeCILL-C license and that you accept its terms.
*/

#ifndef N2D2_EXPORTC_UTILS_H
#define N2D2_EXPORTC_UTILS_H

#include <assert.h>
#include <limits.h>
#include <stdbool.h>
#include <stdint.h> // (u)intx_t typedef

#ifndef M_PI
#define M_PI 3.14159265358979323846264338327950288
#endif

#if defined(__cplusplus)
#define N2D2_UNUSED(x)       // = nothing
#elif defined(__GNUC__)
#define N2D2_UNUSED(x)       x##_UNUSED __attribute__((unused))
#else
#define N2D2_UNUSED(x)       x##_UNUSED
#endif

#ifndef WIN32
// Text attributes
#define ESC_ALL_OFF "\033[0m"
#define ESC_BOLD "\033[1m"
#define ESC_UNDERSCORE "\033[4m"
#define ESC_BLINK "\033[5m"

// Foreground colors
#define ESC_FG_BLACK "\033[30m"
#define ESC_FG_RED "\033[31m"
#define ESC_FG_GREEN "\033[32m"
#define ESC_FG_YELLOW "\033[33m"
#define ESC_FG_BLUE "\033[34m"
#define ESC_FG_MAGENTA "\033[35m"
#define ESC_FG_CYAN "\033[36m"
#define ESC_FG_WHITE "\033[37m"
#define ESC_FG_GRAY "\033[90m"
#define ESC_FG_LIGHT_RED "\033[91m"
#define ESC_FG_LIGHT_GREEN "\033[92m"
#define ESC_FG_LIGHT_YELLOW "\033[93m"
#define ESC_FG_LIGHT_BLUE "\033[94m"
#define ESC_FG_LIGHT_MAGENTA "\033[95m"
#define ESC_FG_LIGHT_CYAN "\033[96m"

// Background colors
#define ESC_BG_BLACK "\033[40m"
#define ESC_BG_RED "\033[41m"
#define ESC_BG_GREEN "\033[42m"
#define ESC_BG_YELLOW "\033[43m"
#define ESC_BG_BLUE "\033[44m"
#define ESC_BG_MAGENTA "\033[45m"
#define ESC_BG_CYAN "\033[46m"
#define ESC_BG_WHITE "\033[47m"
#define ESC_BG_GRAY "\033[100m"
#define ESC_BG_LIGHT_RED "\033[101m"
#define ESC_BG_LIGHT_GREEN "\033[102m"
#define ESC_BG_LIGHT_YELLOW "\033[103m"
#define ESC_BG_LIGHT_BLUE "\033[104m"
#define ESC_BG_LIGHT_MAGENTA "\033[105m"
#define ESC_BG_LIGHT_CYAN "\033[106m"
#else
// Text attributes
#define ESC_ALL_OFF ""
#define ESC_BOLD ""
#define ESC_UNDERSCORE ""
#define ESC_BLINK ""

// Foreground colors
#define ESC_FG_BLACK ""
#define ESC_FG_RED ""
#define ESC_FG_GREEN ""
#define ESC_FG_YELLOW ""
#define ESC_FG_BLUE ""
#define ESC_FG_MAGENTA ""
#define ESC_FG_CYAN ""
#define ESC_FG_WHITE ""

// Background colors
#define ESC_BG_BLACK ""
#define ESC_BG_RED ""
#define ESC_BG_GREEN ""
#define ESC_BG_YELLOW ""
#define ESC_BG_BLUE ""
#define ESC_BG_MAGENTA ""
#define ESC_BG_CYAN ""
#define ESC_BG_WHITE ""
#endif

#define STR_NX(x) #x
#define STR(x) STR_NX(x)

#define CAT(a, ...) PRIMITIVE_CAT(a, __VA_ARGS__)
#define PRIMITIVE_CAT(a, ...) a ## __VA_ARGS__

#define COMPL(b) PRIMITIVE_CAT(COMPL_, b)
#define COMPL_0 1
#define COMPL_1 0

#define BITAND(x) PRIMITIVE_CAT(BITAND_, x)
#define BITAND_0(y) 0
#define BITAND_1(y) y

#define INC(x) PRIMITIVE_CAT(INC_, x)
#define INC_0 1
#define INC_1 2
#define INC_2 3
#define INC_3 4
#define INC_4 5
#define INC_5 6
#define INC_6 7
#define INC_7 8
#define INC_8 9
#define INC_9 10
#define INC_10 11
#define INC_11 12
#define INC_12 13
#define INC_13 14
#define INC_14 15
#define INC_15 16
#define INC_16 16

#define DEC(x) PRIMITIVE_CAT(DEC_, x)
#define DEC_0 0
#define DEC_1 0
#define DEC_2 1
#define DEC_3 2
#define DEC_4 3
#define DEC_5 4
#define DEC_6 5
#define DEC_7 6
#define DEC_8 7
#define DEC_9 8
#define DEC_10 9
#define DEC_11 10
#define DEC_12 11
#define DEC_13 12
#define DEC_14 13
#define DEC_15 14
#define DEC_16 15

#define ADD(x, y) PRIMITIVE_CAT(ADD_, x)(y)
#define ADD_0(x) x
#define ADD_1(x) INC(x)
#define ADD_2(x) ADD_1(INC(x))
#define ADD_3(x) ADD_2(INC(x))
#define ADD_4(x) ADD_3(INC(x))
#define ADD_5(x) ADD_4(INC(x))
#define ADD_6(x) ADD_5(INC(x))
#define ADD_7(x) ADD_6(INC(x))
#define ADD_8(x) ADD_7(INC(x))
#define ADD_9(x) ADD_8(INC(x))
#define ADD_10(x) ADD_9(INC(x))
#define ADD_11(x) ADD_10(INC(x))
#define ADD_12(x) ADD_11(INC(x))
#define ADD_13(x) ADD_12(INC(x))
#define ADD_14(x) ADD_13(INC(x))
#define ADD_15(x) ADD_14(INC(x))
#define ADD_16(x) ADD_15(INC(x))

#define CHECK_N(x, n, ...) n
#define CHECK(...) CHECK_N(__VA_ARGS__, 0,)
#define PROBE(x) x, 1,

#define IS_PAREN(x) CHECK(IS_PAREN_PROBE x)
#define IS_PAREN_PROBE(...) PROBE(~)

#define NOT(x) CHECK(PRIMITIVE_CAT(NOT_, x))
#define NOT_0 PROBE(~)

#define COMPL(b) PRIMITIVE_CAT(COMPL_, b)
#define COMPL_0 1
#define COMPL_1 0

#define BOOL(x) COMPL(NOT(x))

#define IIF(c) PRIMITIVE_CAT(IIF_, c)
#define IIF_0(t, ...) __VA_ARGS__
#define IIF_1(t, ...) t

#define IF(c) IIF(BOOL(c))

#define EAT(...)
#define EXPAND(...) __VA_ARGS__
#define WHEN(c) IF(c)(EXPAND, EAT)

#define EMPTY()
#define DEFER(id) id EMPTY()
#define OBSTRUCT(id) id DEFER(EMPTY)()

#define EVAL(...)  EVAL1(EVAL1(EVAL1(__VA_ARGS__)))
#define EVAL1(...) EVAL2(EVAL2(EVAL2(__VA_ARGS__)))
#define EVAL2(...) EVAL3(EVAL3(EVAL3(__VA_ARGS__)))
#define EVAL3(...) EVAL4(EVAL4(EVAL4(__VA_ARGS__)))
#define EVAL4(...) EVAL5(EVAL5(EVAL5(__VA_ARGS__)))
#define EVAL5(...) __VA_ARGS__

#define REPEAT(count, macro, ...) \
    WHEN(count) \
    ( \
        OBSTRUCT(REPEAT_INDIRECT) () \
        ( \
            DEC(count), macro, __VA_ARGS__ \
        ) \
        OBSTRUCT(macro) \
        ( \
            DEC(count), __VA_ARGS__ \
        ) \
    )
#define REPEAT_INDIRECT() REPEAT

#define WHILE(pred, op, ...) \
    IF(pred(__VA_ARGS__)) \
    ( \
        OBSTRUCT(WHILE_INDIRECT) () \
        ( \
            pred, op, op(__VA_ARGS__) \
        ), \
        __VA_ARGS__ \
    )
#define WHILE_INDIRECT() WHILE

#define PRIMITIVE_COMPARE(x, y) IS_PAREN \
( \
    COMPARE_ ## x ( COMPARE_ ## y) (())  \
)

#define IS_COMPARABLE(x) IS_PAREN( CAT(COMPARE_, x) (()) )

#define NOT_EQUAL(x, y) \
IIF(BITAND(IS_COMPARABLE(x))(IS_COMPARABLE(y)) ) \
( \
   PRIMITIVE_COMPARE, \
   1 EAT \
)(x, y)

#define EQUAL(x, y) COMPL(NOT_EQUAL(x, y))

#define COMMA() ,

#define COMMA_IF(n) IF(n)(COMMA, EAT)()

#define MIN(a, b) (((a) < (b)) ? (a) : (b))
#define MAX(a, b) (((a) > (b)) ? (a) : (b))

#define MAX_2(x0, x1) MAX(x0, x1)
#define MAX_3(x0, x1, x2) MAX(x0, MAX_2(x1, x2))
#define MAX_4(x0, x1, x2, x3) MAX(MAX_2(x0, x1), MAX_2(x2, x3))
#define MAX_5(x0, x1, x2, x3, x4) MAX(x0, MAX_4(x1, x2, x3, x4))
#define MAX_6(x0, x1, x2, x3, x4, x5) MAX(MAX_2(x0, x1), MAX_4(x2, x3, x4, x5))
#define MAX_7(x0, x1, x2, x3, x4, x5, x7) MAX(MAX_3(x0, x1, x2), MAX_4(x3, x4, x5, x7))
#define MAX_8(x0, x1, x2, x3, x4, x5, x6, x7) MAX(MAX_4(x0, x1, x2, x3), MAX_4(x4, x5, x6, x7))
#define MAX_9(x0, x1, x2, x3, x4, x5, x6, x7, x8) MAX(x0, MAX_8(x1, x2, x3, x4, x5, x6, x7, x8))
#define MAX_10(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9) MAX(MAX_2(x0, x1), MAX_8(x2, x3, x4, x5, x6, x7, x8, x9))
#define MAX_11(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10) MAX(MAX_3(x0, x1, x2), MAX_8(x3, x4, x5, x6, x7, x8, x9, x10))
#define MAX_12(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11) MAX(MAX_4(x0, x1, x2, x3), MAX_8(x4, x5, x6, x7, x8, x9, x10, x11))
#define MAX_13(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12) MAX(MAX_5(x0, x1, x2, x3, x4), MAX_8(x5, x6, x7, x8, x9, x10, x11, x12))
#define MAX_14(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13) MAX(MAX_6(x0, x1, x2, x3, x4, x5), MAX_8(x6, x7, x8, x9, x10, x11, x12, x13))
#define MAX_15(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14) MAX(MAX_7(x0, x1, x2, x3, x4, x5, x6), MAX_8(x7, x8, x9, x10, x11, x12, x13, x14))
#define MAX_16(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15) MAX(MAX_8(x0, x1, x2, x3, x4, x5, x6, x7), MAX_8(x8, x9, x10, x11, x12, x13, x14, x15))
#define MAX_17(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16) MAX(x0, MAX_16(x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16))
#define MAX_18(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17) MAX(MAX_2(x0, x1), MAX_16(x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17))
#define MAX_19(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18) MAX(MAX_3(x0, x1, x2), MAX_16(x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18))
#define MAX_20(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19) MAX(MAX_4(x0, x1, x2, x3), MAX_16(x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19))
#define MAX_21(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20) MAX(MAX_5(x0, x1, x2, x3, x4), MAX_16(x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20))
#define MAX_22(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21) MAX(MAX_6(x0, x1, x2, x3, x4, x5), MAX_16(x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21))
#define MAX_23(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22) MAX(MAX_7(x0, x1, x2, x3, x4, x5, x6), MAX_16(x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22))
#define MAX_24(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23) MAX(MAX_8(x0, x1, x2, x3, x4, x5, x6, x7), MAX_16(x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23))
#define MAX_25(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24) MAX(x0, MAX_24(x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24))
#define MAX_26(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25) MAX(MAX_2(x0, x1), MAX_24(x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25))
#define MAX_27(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26) MAX(MAX_3(x0, x1, x2), MAX_24(x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26))
#define MAX_28(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27) MAX(MAX_4(x0, x1, x2, x3), MAX_24(x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27))
#define MAX_29(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28) MAX(MAX_5(x0, x1, x2, x3, x4), MAX_24(x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28))
#define MAX_30(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29) MAX(MAX_6(x0, x1, x2, x3, x4, x5), MAX_24(x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29))
#define MAX_31(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30) MAX(MAX_7(x0, x1, x2, x3, x4, x5, x6), MAX_24(x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30))
#define MAX_32(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, x31) MAX(MAX_16(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15), MAX_16(x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, x31))

// round up to the nearest multiple of a number
// multiple must be a power of 2
static inline unsigned int roundUp(unsigned int numToRound,
                                   unsigned int multiple)
{
    assert(multiple && ((multiple & (multiple - 1)) == 0));
    return (numToRound + multiple - 1) & -multiple;
}

// min() and max()
static inline char char_max(char a, char b)
{
    return (a > b) ? a : b;
}
static inline char char_min(char a, char b)
{
    return (a < b) ? a : b;
}
static inline unsigned char uchar_max(unsigned char a, unsigned char b)
{
    return (unsigned char)((a > b) ? a : b);
}
static inline unsigned char uchar_min(unsigned char a, unsigned char b)
{
    return (unsigned char)((a < b) ? a : b);
}
static inline short short_max(short a, short b)
{
    return (a > b) ? a : b;
}
static inline short short_min(short a, short b)
{
    return (a < b) ? a : b;
}
static inline unsigned short ushort_max(unsigned short a, unsigned short b)
{
    return (unsigned short)((a > b) ? a : b);
}
static inline unsigned short ushort_min(unsigned short a, unsigned short b)
{
    return (unsigned short)((a < b) ? a : b);
}
static inline int int_max(int a, int b)
{
    return (a > b) ? a : b;
}
static inline int int_min(int a, int b)
{
    return (a < b) ? a : b;
}
static inline unsigned int uint_max(unsigned int a, unsigned int b)
{
    return (a > b) ? a : b;
}
static inline unsigned int uint_min(unsigned int a, unsigned int b)
{
    return (a < b) ? a : b;
}

static inline int8_t int8_max(int8_t a, int8_t b)
{
    return (a > b) ? a : b;
}
static inline int8_t int8_min(int8_t a, int8_t b)
{
    return (a < b) ? a : b;
}
static inline uint8_t uint8_max(uint8_t a, uint8_t b)
{
    return (a > b) ? a : b;
}
static inline uint8_t uint8_min(uint8_t a, uint8_t b)
{
    return (a < b) ? a : b;
}
static inline int16_t int16_max(int16_t a, int16_t b)
{
    return (a > b) ? a : b;
}
static inline int16_t int16_min(int16_t a, int16_t b)
{
    return (a < b) ? a : b;
}
static inline uint16_t uint16_max(uint16_t a, uint16_t b)
{
    return (a > b) ? a : b;
}
static inline uint16_t uint16_min(uint16_t a, uint16_t b)
{
    return (a < b) ? a : b;
}
static inline int32_t int32_max(int32_t a, int32_t b)
{
    return (a > b) ? a : b;
}
static inline int32_t int32_min(int32_t a, int32_t b)
{
    return (a < b) ? a : b;
}
static inline uint32_t uint32_max(uint32_t a, uint32_t b)
{
    return (a > b) ? a : b;
}
static inline uint32_t uint32_min(uint32_t a, uint32_t b)
{
    return (a < b) ? a : b;
}

// swap()
static inline void char_swap(char* a, char* b)
{
    char tmp = *a;
    *a = *b;
    *b = tmp;
}
static inline void uchar_swap(unsigned char* a, unsigned char* b)
{
    unsigned char tmp = *a;
    *a = *b;
    *b = tmp;
}
static inline void short_swap(short* a, short* b)
{
    short tmp = *a;
    *a = *b;
    *b = tmp;
}
static inline void ushort_swap(unsigned short* a, unsigned short* b)
{
    unsigned short tmp = *a;
    *a = *b;
    *b = tmp;
}
static inline void int_swap(int* a, int* b)
{
    int tmp = *a;
    *a = *b;
    *b = tmp;
}
static inline void uint_swap(unsigned int* a, unsigned int* b)
{
    unsigned int tmp = *a;
    *a = *b;
    *b = tmp;
}

static inline void int8_swap(int8_t* a, int8_t* b)
{
    int8_t tmp = *a;
    *a = *b;
    *b = tmp;
}
static inline void uint8_swap(uint8_t* a, uint8_t* b)
{
    uint8_t tmp = *a;
    *a = *b;
    *b = tmp;
}
static inline void int16_swap(int16_t* a, int16_t* b)
{
    int16_t tmp = *a;
    *a = *b;
    *b = tmp;
}
static inline void uint16_swap(uint16_t* a, uint16_t* b)
{
    uint16_t tmp = *a;
    *a = *b;
    *b = tmp;
}
static inline void int32_swap(int32_t* a, int32_t* b)
{
    int32_t tmp = *a;
    *a = *b;
    *b = tmp;
}
static inline void uint32_swap(uint32_t* a, uint32_t* b)
{
    uint32_t tmp = *a;
    *a = *b;
    *b = tmp;
}

static inline unsigned int isqrt(unsigned int x)
{
    unsigned int op, res, one;
    op = x;
    res = 0;

/* "one" starts at the highest power of four <= than the argument. */
#if UINT_MAX == 0xFFFFU
    one = 1 << 14; /* second-to-top bit set */
#elif UINT_MAX == 0xFFFFFFFFUL
    one = 1 << 30; /* second-to-top bit set */
#else
#error "isqrt(): unsupported unsigned int type size"
#endif

    while (one > op)
        one >>= 2;

    while (one != 0) {
        if (op >= res + one) {
            op -= res + one;
            res += one << 1; // <-- faster than 2 * one
        }

        res >>= 1;
        one >>= 2;
    }

    return res;
}

#endif // N2D2_EXPORTC_UTILS_H
